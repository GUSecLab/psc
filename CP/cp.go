/*
Created on Apr 18, 2017

@author: Akshaya Mani, Georgetown University
*/

package main

import (
    "bytes"
    "crypto/sha256"
    "crypto/tls"
    "crypto/x509"
    "encoding/binary"
    "errors"
    "fmt"
    "psc/lib/danieldk/par"
    "go.dedis.ch/kyber/v3"
    "go.dedis.ch/kyber/v3/group/edwards25519"
    "go.dedis.ch/kyber/v3/proof"
    "go.dedis.ch/kyber/v3/shuffle"
    "go.dedis.ch/kyber/v3/sign/schnorr"
    "github.com/sirupsen/logrus"
    "github.com/golang/protobuf/proto"
    "io"
    "io/ioutil"
    "math"
    "math/big"
    "net"
    "os"
    "psc/config"
    "psc/lib/dpres"
    "psc/lib/combytes"
    "psc/lib/comtime"
    "psc/lib/schnorrkey"
    "psc/lib/sessionno"
    "psc/lib/cpres"
    "strconv"
    "syscall"
    "time"
)

// ReRandomizeDecryptProof represents a NIZK proof.
type ReRandomizeDecryptProof struct {
    C kyber.Scalar //Challenge
    R1 kyber.Scalar //Response 1
    R2 kyber.Scalar //Response 2
    R3 kyber.Scalar //Response 2
}

var suite = edwards25519.NewBlakeSHA256Ed25519() //Cipher suite
var pseudorand = suite.RandomStream() //For Randomness
var pointSize = suite.Point().MarshalSize() //Point size
var scalarSize = suite.Scalar().MarshalSize() //Scalar size
var sigSize = scalarSize + pointSize //Schnorr signature length
var hashSize = sha256.Size
var bSize = 1 //Broadcast flag length (fixed)
var dSize = 1 //No. of distinct messages length (fixed)
var rSize = 1 //Round no. length (fixed)
var snoSize = 4 //Step no. length (fixed)
var signArray = 2 //Signature array consisting of CPs that have signed (allows maximum of 16 bits (or CPs))
//var minDM = 2 //Minimum no. of distinct messages for proof of equivocation

var theoryBytes = big.NewInt(0) //Theoretical communication cost
var implSendBytes = big.NewInt(0) //Implementation send communication cost
var implRecvBytes = big.NewInt(0) //Implementation receive communication cost
var theoryStepBytes = big.NewInt(0) //Theoretical step communication cost
var implStepBytes = big.NewInt(0) //Implementation step communication cost
var implEchoSendBytes = big.NewInt(0) //Implementation echo send communication cost
var implEchoRecvBytes = big.NewInt(0) //Implementation echo receive communication cost

var start_time time.Time //Start time from 1st step
var step_start time.Time //Step start time
var step_end time.Duration //Step end time
var echo_start time.Time //Step start time
var echo_end time.Duration //Step end time
var ds_start time.Time //Step start time
var ds_end time.Duration //Step end time

var dpIP = config.DP_IP //DP IP
var dpPort = config.DP_Port //DP port no.
var cpIPs []string //CP IPs
var cpPortPrefix = config.CP_PortPrefix //CP port prefix

type PlainFormatter struct {
    TimestampFormat string
    LevelDesc []string
}

func (f *PlainFormatter) Format(entry *logrus.Entry) ([]byte, error) {
    timestamp := fmt.Sprintf(entry.Time.Format(f.TimestampFormat))
    return []byte(fmt.Sprintf("%s %s %s\n", f.LevelDesc[entry.Level], timestamp, entry.Message)), nil
}

func main() {

    plainFormatter := new(PlainFormatter)
    plainFormatter.TimestampFormat = "2006-01-02 15:04:05"
    plainFormatter.LevelDesc = []string{"PANIC", "FATAL", "ERROR", "WARN", "INFO", "DEBG", "TRACE"}
    logrus.SetFormatter(plainFormatter)

    b := config.B //No. of entries in the IP table
    no_CPs := config.NoCPs //No. of CPs
    no_DPs := config.NoDPs //No. of DPs
    epsilon := config.Epsilon //Epsilon
    delta := config.Delta //Delta
    n := int(math.Floor((math.Log(2 / delta) * 64)/math.Pow(epsilon, 2))) + 1 //No. of noise vectors
    outputPath := config.OutputPath

    cpIPs = make([]string, no_CPs) //Initialize

    //Iterate over all CPs
    for j := 0; j < no_CPs; j++ {

        cpIPs[j] = config.CP_IPs[j] //Initialize with CP IP addresses
    }

    cp_no := parseCommandline(os.Args) //Parse CP no., port no.

    var agg int64 //Aggregate
    agg = 0 //Initialize aggregate to 0

    s_dmsg := make(map[string][]byte) //CP signatures appended with hash of distinct messages (in Dolev-Strong)
    var b_msg []byte //Message received from broadcaster (in Dolev-Strong)
    y := make([]kyber.Point, no_CPs) //Public key list
    c_i := make([]kyber.Scalar, b) //Blinded IP counters list per DP
    nv_dp := make(map[int]bool) //List of DPs whose zkps verification failed
    s_b := make([][]byte, no_DPs) //DP signed ElGamal encrypted blinding values (in bytes) list
    s_c := make([][]byte, no_DPs) //DP signed blinded IP counters (in bytes) list
    dp_no := 0 //No. of DPs responded so far
    var step_no uint32 //Step no.
    f_flag := false //Finish flag
    fb_flag := false //Fallback option flag (Signal to echo hash of all DP inputs)
    q_flag := false //Quit flag
    var b_flag bool //Broadcast flag
    var cp_bcast int //CP no. broadcasting
    var s_no uint32 //Session No.
    no_dmsgs := 0 //No. of distinct messages received (in Dolev-Strong)

    x := suite.Scalar().Pick(pseudorand) //CP private key
    y[cp_no - 1] = suite.Point().Mul(x, nil) //CP public key
    Y := suite.Point().Mul(x, nil) //Joint public key
    s_Y := make([][]byte, no_CPs) //CP signed compouned public key list

    //ElGamal encrypted noise
    nr := make([][2]kyber.Point, n)
    nc := make([][2]kyber.Point, n)

    //Shuffled ElGamal encrypted noise
    nr_o := make([][2]kyber.Point, n)
    nc_o := make([][2]kyber.Point, n)

    //ElGamal encrypted IP counters (CP input)
    R := make([]kyber.Point, b+n)
    C := make([]kyber.Point, b+n)

    //ElGamal encrypted IP counters (CP output)
    R_O := make([]kyber.Point, b+n)
    C_O := make([]kyber.Point, b+n)

    //DP ElGamal encrypted blinding values
    tr := make([][]kyber.Point, no_DPs)
    tc := make([][]kyber.Point, no_DPs)

    priv := new(Schnorrkey.Priv) //CP private key in bytes
    pub := new(Schnorrkey.Pub) //CP public key in bytes

    //Convert to bytes
    var tb bytes.Buffer //Temporary buffer
    x.MarshalTo(&tb)
    priv.X = tb.Bytes()

    tb.Reset() //Buffer reset
    y[cp_no - 1].MarshalTo(&tb)
    pub.Y = tb.Bytes()

    //Set broadcasting CP
    cp_bcast = 1

    //Set session no.
    in, err := ioutil.ReadFile("../session/session.no")
    checkError(err)
    sno := &Sessionno.SNo{}
    err = proto.Unmarshal(in, sno)
    checkError(err)
    s_no = *sno.S

    //Set step no.
    step_no = s_no + 1

    //Set broadcast flag
    if cp_no == 1 {

        b_flag = true

    } else {

        b_flag = false
    }

    //Iterate over all IP counters
    for j := 0; j < no_DPs; j++ {

        tr[j] = make([]kyber.Point, b)
        tc[j] = make([]kyber.Point, b)
    }

    //Iterate over all IP counters
    for j := 0; j < b; j++ {

        c_i[j] = suite.Scalar().Zero() //Initialize with zero
        R[j] = suite.Point().Null() //Initialize with identity element
        C[j] = suite.Point().Null() //Initialize with identity element
    }

    //Iterate over all noise counters
    for j := 0; j < n; j++ {

        //Initialize 0 & 1 ciphers
        nr[j][0] = suite.Point().Null() //Initialize with identity element
        nr[j][1] = suite.Point().Null() //Initialize with identity element
        nc[j][0] = suite.Point().Null() //Initialize with identity element
        nc[j][1] = suite.Point().Base() //Initialize with base point
    }

    logrus.Info("Started server")

    //Listen to the TCP port
    sock := createServer(cp_no)

    start := time.Now()

    for{

        //If Quit flag not true
        if q_flag == false && f_flag == false {

            //If broadcasting CP is current CP and broadcast flag is set
            if cp_bcast == cp_no && b_flag == true {

                if step_no == s_no + 1 { //If step no. is 1

                    start_time = time.Now()
                    logrus.Info("Starting step no. ", step_no-s_no)
                    step_start = time.Now()

                    theoryStepBytes = big.NewInt(0) //Theoretical step communication cost
                    implStepBytes = big.NewInt(0) //Implementation step communication cost

                    //Set CP response to public key
                    cp_resp := new(CPres.Response)
                    cp_resp.R = make([][]byte, 1)
                    cp_resp.Proof = make([][]byte, 1)
                    cp_resp.R[0] = pub.Y

                    //Create proof
                    rep := proof.Rep("X", "x", "B")
                    secret := map[string]kyber.Scalar{"x": x}
                    public := map[string]kyber.Point{"B": suite.Point().Base(), "X": y[cp_no - 1]}
                    prover := rep.Prover(suite, secret, public, nil)
                    prf, _ := proof.HashProve(suite, strconv.Itoa(int(step_no)), prover)
                    cp_resp.Proof[0] = make([]byte, len(prf))
                    copy(cp_resp.Proof[0][:], prf)

                    //Convert to bytes
                    cp_resp1, _ := proto.Marshal(cp_resp)

                    step_end = time.Since(step_start)
                    logrus.Info("Step no. ", step_no-s_no, " computing time ", step_end.String())

                    theoryStepBytes.Add(theoryStepBytes, big.NewInt(int64( (no_CPs-1) * (bSize+snoSize + sigSize + (pointSize + len(prf))) ))) //For broadcast
                    implStepBytes.Add(implStepBytes, big.NewInt(int64( (no_CPs-1) * (bSize+snoSize + sigSize + len(cp_resp1)) ))) //For broadcast implementation

                    //Broadcast public key
                    logrus.Info("Step no. ", step_no-s_no, " communication cost ", implStepBytes.String(), " bytes")
                    step_start = time.Now()
                    broadcastData(step_no, cp_no, cp_resp1, no_CPs)
                    step_end = time.Since(step_start)
                    logrus.Info("Step no. ", step_no-s_no, " broadcast end-end time ", step_end.String())

                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_CPs-1) * (bSize+snoSize + sigSize + (pointSize + len(prf))) ))) //For broadcast
                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_CPs-1) * (no_CPs-2) * (bSize+snoSize+rSize+dSize + sigSize + (sigSize + hashSize)) ))) //For echo
                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_CPs-2) * (no_CPs-1) * (no_CPs-2) * (bSize+snoSize+rSize+dSize) ))) //For heartbeat

                } else if step_no == s_no + 2 { //If step no. is 2

                    step_start = time.Now()
                    logrus.Info("Starting step no. ", step_no-s_no)

                    theoryStepBytes = big.NewInt(0) //Theoretical step communication cost
                    implStepBytes = big.NewInt(0) //Implementation step communication cost

                    //Set CP response to broadcast public key
                    cp_resp := new(CPres.Response)
                    cp_resp.R = make([][]byte, 1)
                    cp_resp.Proof = make([][]byte, 1)

                    //Convert joint public key to bytes
                    tb.Reset() //Buffer reset
                    Y.MarshalTo(&tb)
                    cp_resp.R[0] = tb.Bytes()

                    //Convert to bytes
                    cp_resp1, _ := proto.Marshal(cp_resp)

                    step_end = time.Since(step_start)
                    logrus.Info("Step no. ", step_no-s_no, " computing time ", step_end.String())

                    theoryStepBytes.Add(theoryStepBytes, big.NewInt(int64( (no_CPs-1) * (bSize+snoSize + sigSize + (pointSize)) ))) //For broadcast
                    implStepBytes.Add(implStepBytes, big.NewInt(int64( (no_CPs-1) * (bSize+snoSize + sigSize + len(cp_resp1)) ))) //For broadcast implementation

                    //Broadcast compound public key
                    logrus.Info("Step no. ", step_no-s_no, " communication cost ", implStepBytes.String(), " bytes")
                    step_start = time.Now()
                    broadcastData(step_no, cp_no, cp_resp1, no_CPs)
                    step_end = time.Since(step_start)
                    logrus.Info("Step no. ", step_no-s_no, " broadcast end-end time ", step_end.String())

                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_CPs-1) * (bSize+snoSize + sigSize + (pointSize)) ))) //For broadcast
                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_CPs-1) * (no_CPs-2) * (bSize+snoSize+rSize+dSize + sigSize + (sigSize + hashSize)) ))) //For echo
                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_CPs-2) * (no_CPs-1) * (no_CPs-2) * (bSize+snoSize+rSize+dSize) ))) //For heartbeat

                } else if step_no == s_no + 3 { //If step no. is 3

                    step_start = time.Now()
                    logrus.Info("Starting step no. ", step_no-s_no)

                    theoryStepBytes = big.NewInt(0) //Theoretical step communication cost
                    implStepBytes = big.NewInt(0) //Implementation step communication cost

                    var msg []byte //Message containing signature and marshalled joint public key from step 2

                    msg = append(msg, b_msg...) //Append joint public key

                    //Iterate over all counters
                    for i := 0; i < no_CPs; i++ {

                        if i != cp_bcast - 1 {

                            msg = append(msg, s_Y[i]...) //Append CP signed joint public key
                        }
                    }

                    step_end = time.Since(step_start)
                    logrus.Info("Step no. ", step_no-s_no, " computing time ", step_end.String())

                    theoryStepBytes.Add(theoryStepBytes, big.NewInt(int64( (no_DPs) * (bSize+snoSize + sigSize + (((no_CPs-1)*sigSize) + pointSize)) ))) //For broadcast
                    implStepBytes.Add(implStepBytes, big.NewInt(int64( (no_DPs) * (bSize+snoSize + sigSize + len(msg)) ))) //For broadcast implementation

                    //Send joint public key to DPs
                    logrus.Info("Step no. ", step_no-s_no, " communication cost ", implStepBytes.String(), " bytes")
                    step_start = time.Now()
                    signSendDataToDP(step_no, cp_no, msg, no_DPs)
                    step_end = time.Since(step_start)
                    logrus.Info("Step no. ", step_no-s_no, " send data to DP end-end time ", step_end.String())

                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_DPs) * (bSize+snoSize + sigSize + (((no_CPs-1)*sigSize) + pointSize)) ))) //For CP-DP communication

                } else if step_no == s_no + 6 { //If step no. is 6

                    step_start = time.Now()
                    logrus.Info("Starting step no. ", step_no-s_no)

                    theoryStepBytes = big.NewInt(0) //Theoretical step communication cost
                    implStepBytes = big.NewInt(0) //Implementation step communication cost

                    cp_resp := new(CPres.Response) //CP response
                    cp_resp.R = make([][]byte, b)
                    cp_resp.C = make([][]byte, b)

                    //Iterate over all Counters
                    for i := 0; i < b; i++ {

                        tb.Reset() //Buffer reset
                        _,_ = R[i].MarshalTo(&tb)
                        cp_resp.R[i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.R[i][:], tb.Bytes()) //Convert to bytes

                        tb.Reset() //Buffer reset
                        _,_ = C[i].MarshalTo(&tb)
                        cp_resp.C[i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.C[i][:], tb.Bytes()) //Convert to bytes
                    }

                    //Convert to bytes
                    cp_resp1, _ := proto.Marshal(cp_resp)

                    step_end = time.Since(step_start)
                    logrus.Info("Step no. ", step_no-s_no, " computing time ", step_end.String())

                    theoryStepBytes.Add(theoryStepBytes, big.NewInt(int64( (no_CPs-1) * (bSize+snoSize + sigSize + (2*b*pointSize)) ))) //For broadcast
                    implStepBytes.Add(implStepBytes, big.NewInt(int64( (no_CPs-1) * (bSize+snoSize + sigSize + len(cp_resp1)) ))) //For broadcast implementation

                    //Broadcast ElGamal ciphertexts
                    logrus.Info("Step no. ", step_no-s_no, " communication cost ", implStepBytes.String(), " bytes")
                    step_start = time.Now()
                    broadcastData(step_no, cp_no, cp_resp1, no_CPs)
                    step_end = time.Since(step_start)
                    logrus.Info("Step no. ", step_no-s_no, " broadcast end-end time ", step_end.String())

                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_CPs-1) * (bSize+snoSize + sigSize + (2*b*pointSize)) ))) //For broadcast
                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_CPs-1) * (no_CPs-2) * (bSize+snoSize+rSize+dSize + sigSize + (sigSize + hashSize)) ))) //For echo
                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_CPs-2) * (no_CPs-1) * (no_CPs-2) * (bSize+snoSize+rSize+dSize) ))) //For heartbeat

                } else if step_no == s_no + 7 { //If step no. is 7 - Fallback option phase 1

                    s_dmsg[string(s_c[dp_no][:hashSize])] = s_c[dp_no] //Add to map

                    data := make([][]byte, 1) //Data to be sent

                    data[0] = s_c[dp_no]

                    //Broadcast DP signed inputs
                    logrus.Info("Step no. ", step_no-s_no, " fallback option phase 1 Dolev-Strong")
                    sendDataN_1(step_no, uint8(0), uint8(1), 0, 1, data, no_CPs)

                } else if step_no == s_no + 8 { //If step no. is 8 - Fallback option phase 2

                    s_dmsg[string(s_b[dp_no][:hashSize])] = s_b[dp_no] //Add to map

                    data := make([][]byte, 1) //Data to be sent

                    data[0] = s_b[dp_no]

                    //Broadcast DP signed inputs
                    logrus.Info("Step no. ", step_no-s_no, " fallback option phase 1 Dolev-Strong")
                    sendDataN_1(step_no, uint8(0), uint8(1), 0, 1, data, no_CPs)

                } else if step_no == s_no + 9 { //If step no. is 9

                    step_start = time.Now()
                    logrus.Info("Starting step no. ", step_no-s_no)

                    theoryStepBytes = big.NewInt(0) //Theoretical step communication cost
                    implStepBytes = big.NewInt(0) //Implementation step communication cost

                    prf_len := 0 //Proof length to compute theoretical communication cost

                    cp_resp := new(CPres.Response) //CP response
                    cp_resp.R = make([][]byte, 2 * n)
                    cp_resp.C = make([][]byte, 2 * n)
                    cp_resp.Proof = make([][]byte, n)

                    xbar, ybar, prover := par.MapElgamalCiphersChunked(shuffleNoise, nr, nc, Y, n) //Parallel shuffle n noise coins
                    //Iterate over all noise counters
                    for i := 0; i < n; i++ {

                        //Change its input as shuffled output for next verification
                        nr[i][0] = suite.Point().Set(xbar[i][0])
                        nr[i][1] = suite.Point().Set(xbar[i][1])
                        nc[i][0] = suite.Point().Set(ybar[i][0])
                        nc[i][1] = suite.Point().Set(ybar[i][1])

                        //Set CP response to broadcast noise
                        tb.Reset() //Buffer reset
                        xbar[i][0].MarshalTo(&tb)
                        cp_resp.R[2*i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.R[2*i][:], tb.Bytes()) //Convert to bytes

                        tb.Reset() //Buffer reset
                        xbar[i][1].MarshalTo(&tb)
                        cp_resp.R[(2*i)+1] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.R[(2*i)+1][:], tb.Bytes()) //Convert to bytes

                        tb.Reset() //Buffer reset
                        ybar[i][0].MarshalTo(&tb)
                        cp_resp.C[2*i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.C[2*i][:], tb.Bytes()) //Convert to bytes

                        tb.Reset() //Buffer reset
                        ybar[i][1].MarshalTo(&tb)
                        cp_resp.C[(2*i)+1] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.C[(2*i)+1][:], tb.Bytes()) //Convert to bytes

                        prf, _ := proof.HashProve(suite, strconv.Itoa(int(step_no))+strconv.Itoa(i), prover[i])
                        cp_resp.Proof[i] = make([]byte, len(prf))
                        copy(cp_resp.Proof[i][:], prf)

                        prf_len += len(prf)
                    }

                    //Convert to bytes
                    cp_resp1, _ := proto.Marshal(cp_resp)

                    step_end = time.Since(step_start)
                    logrus.Info("Step no. ", step_no-s_no, " computing time ", step_end.String())

                    theoryStepBytes.Add(theoryStepBytes, big.NewInt(int64( (no_CPs-1) * (bSize+snoSize + sigSize + ((4*n*pointSize) + prf_len)) ))) //For broadcast
                    implStepBytes.Add(implStepBytes, big.NewInt(int64( (no_CPs-1) * (bSize+snoSize + sigSize + len(cp_resp1)) ))) //For broadcast implementation

                    //Broadcast shuffled noise
                    logrus.Info("Step no. ", step_no-s_no, " communication cost ", implStepBytes.String(), " bytes")
                    step_start = time.Now()
                    broadcastData(step_no, cp_no, cp_resp1, no_CPs)
                    step_end = time.Since(step_start)
                    logrus.Info("Step no. ", step_no-s_no, " broadcast end-end time ", step_end.String())

                    //If last CP has broadcasted
                    if cp_bcast == no_CPs {

                        //Iterate over all noise counters
                        for i := b; i < b+n; i++ {

                            //Select 1st Coin as noise
                            R[i] = suite.Point().Set(nr[i-b][0])
                            C[i] = suite.Point().Set(nc[i-b][0])
                        }

                    }

                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_CPs-1) * (bSize+snoSize + sigSize + ((4*n*pointSize) + prf_len)) ))) //For broadcast
                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_CPs-1) * (no_CPs-2) * (bSize+snoSize+rSize+dSize + sigSize + (sigSize + hashSize)) ))) //For echo
                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_CPs-2) * (no_CPs-1) * (no_CPs-2) * (bSize+snoSize+rSize+dSize) ))) //For heartbeat

                } else if step_no == s_no + 10 { //If step no. is 10

                    step_start = time.Now()
                    logrus.Info("Starting step no. ", step_no-s_no)

                    theoryStepBytes = big.NewInt(0) //Theoretical step communication cost
                    implStepBytes = big.NewInt(0) //Implementation step communication cost

                    Xbar, Ybar, prover := shuffle.Shuffle(suite, nil, Y, R, C, pseudorand) //Shuffle counters

                    //Assign to output vector and convert to bytes
                    cp_resp := new(CPres.Response) //CP response
                    cp_resp.R = make([][]byte, b+n)
                    cp_resp.C = make([][]byte, b+n)
                    cp_resp.Proof = make([][]byte, 1)

                    prf, _ := proof.HashProve(suite, strconv.Itoa(int(step_no)), prover)
                    cp_resp.Proof[0] = make([]byte, len(prf))
                    copy(cp_resp.Proof[0][:], prf)

                    //Iterate over all Counters
                    for i := 0; i < b+n; i++ {

                        //Change its input as shuffled Output for next verification
                        R[i] = suite.Point().Set(Xbar[i])
                        C[i] = suite.Point().Set(Ybar[i])

                        tb.Reset() //Buffer reset
                        Xbar[i].MarshalTo(&tb)
                        cp_resp.R[i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.R[i][:], tb.Bytes()) //Convert to bytes

                        tb.Reset() //Buffer reset
                        Ybar[i].MarshalTo(&tb)
                        cp_resp.C[i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.C[i][:], tb.Bytes()) //Convert to bytes
                    }

                    //Convert to bytes
                    cp_resp1, _ := proto.Marshal(cp_resp)

                    step_end = time.Since(step_start)
                    logrus.Info("Step no. ", step_no-s_no, " computing time ", step_end.String())

                    theoryStepBytes.Add(theoryStepBytes, big.NewInt(int64( (no_CPs-1) * (bSize+snoSize + sigSize + ((2*(b+n)*pointSize) + len(prf))) ))) //For broadcast
                    implStepBytes.Add(implStepBytes, big.NewInt(int64( (no_CPs-1) * (bSize+snoSize + sigSize + len(cp_resp1)) ))) //For broadcast implementation

                    //Broadcast shuffled counters
                    logrus.Info("Step no. ", step_no-s_no, " communication cost ", implStepBytes.String(), " bytes")
                    step_start = time.Now()
                    broadcastData(step_no, cp_no, cp_resp1, no_CPs)
                    step_end = time.Since(step_start)
                    logrus.Info("Step no. ", step_no-s_no, " broadcast end-end time ", step_end.String())

                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_CPs-1) * (bSize+snoSize + sigSize + ((2*(b+n)*pointSize) + len(prf))) ))) //For broadcast
                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_CPs-1) * (no_CPs-2) * (bSize+snoSize+rSize+dSize + sigSize + (sigSize + hashSize)) ))) //For echo
                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_CPs-2) * (no_CPs-1) * (no_CPs-2) * (bSize+snoSize+rSize+dSize) ))) //For heartbeat

                } else if step_no == s_no + 11 { //If step no. is 11

                    step_start = time.Now()
                    logrus.Info("Starting step no. ", step_no-s_no)

                    theoryStepBytes = big.NewInt(0) //Theoretical step communication cost
                    implStepBytes = big.NewInt(0) //Implementation step communication cost

                    yi := suite.Point().Null() //Partial joint public key

                    //Compute partial joint public key
                    for i := cp_bcast-1; i < no_CPs; i++ {

                        yi.Add(yi, y[i])
                    }

                    s := make([]kyber.Scalar, b+n) //Randomness for re-encryption
                    q := make([]kyber.Scalar, b+n) //Randomness for re-randomization

                    //Re-encrypted, re-randomized, and decrypted output
                    Xbar := make([]kyber.Point, b+n)
                    Ybar := make([]kyber.Point, b+n)

                    //Iterate over all Counters
                    for i := 0; i < b+n; i++ {

                        s[i] = suite.Scalar().Pick(pseudorand) //Pick a random scalar

                        //Choose non-zero re-randomization scalar that does not make the output an encryption with identity element
                        for true {

                            q[i] = suite.Scalar().Zero()

                            for q[i].Equal(suite.Scalar().Zero()) == true {
                                q[i] = suite.Scalar().Pick(pseudorand) //Set exponent to non-zero random scalar
                            }

                            //Re-encrypt
                            Xbar[i] = suite.Point().Add(R[i], suite.Point().Mul(s[i], nil))

                            //Re-randomize
                            Xbar[i] = suite.Point().Mul(q[i], Xbar[i])

                            if !Xbar[i].Equal(suite.Point().Null()) { //If identity element - honest CP is blamed with negligible probability

                                break
                            }
                        }

                        //Re-encrypt
                        Ybar[i] = suite.Point().Add(C[i], suite.Point().Mul(s[i], yi))

                        //Re-randomize
                        Ybar[i] = suite.Point().Mul(q[i], Ybar[i])

                        //Decrypt
                        Ybar[i] = suite.Point().Sub(Ybar[i], suite.Point().Mul(x, Xbar[i]))
                    }

                    prf, _ := rerandomizeDecryptProofBatch(suite, R, C, Xbar, Ybar, nil, yi, s, q, x) //Re-randomization

                    //Assign to output vector and convert to bytes
                    cp_resp := new(CPres.Response) //CP response
                    cp_resp.R = make([][]byte, b+n)
                    cp_resp.C = make([][]byte, b+n)
                    cp_resp.Proof = make([][]byte, b+n)

                    //Iterate over all counters
                    for i := 0; i < b+n; i++ {

                        //Change its input as re-randomized decrypted output for next verification
                        R[i] = suite.Point().Set(Xbar[i])
                        C[i] = suite.Point().Set(Ybar[i])

                        tb.Reset() //Buffer reset
                        Xbar[i].MarshalTo(&tb)
                        cp_resp.R[i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.R[i][:], tb.Bytes()) //Convert to bytes

                        tb.Reset() //Buffer reset
                        Ybar[i].MarshalTo(&tb)
                        cp_resp.C[i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.C[i][:], tb.Bytes()) //Convert to bytes

                        tb.Reset() //Buffer reset
                        suite.Write(&tb, prf[i])
                        cp_resp.Proof[i] = make([]byte, len(tb.Bytes()))
                        copy(cp_resp.Proof[i][:], tb.Bytes()) //Convert to bytes
                    }

                    //Proof length
                    tb.Reset()
                    suite.Write(&tb, cp_resp.Proof[:])
                    prf_len := len(tb.Bytes()) //Length of proof to calculate communication cost

                    //Convert to bytes
                    cp_resp1, _ := proto.Marshal(cp_resp)

                    step_end = time.Since(step_start)
                    logrus.Info("Step no. ", step_no-s_no, " computing time ", step_end.String())

                    theoryStepBytes.Add(theoryStepBytes, big.NewInt(int64( (no_CPs-1) * (bSize+snoSize + sigSize + ((2*(b+n)*pointSize) + prf_len)) ))) //For broadcast
                    implStepBytes.Add(implStepBytes, big.NewInt(int64( (no_CPs-1) * (bSize+snoSize + sigSize + len(cp_resp1)) ))) //For broadcast implementation

                    //Broadcast re-randomized and decrypted counters
                    logrus.Info("Step no. ", step_no-s_no, " communication cost ", implStepBytes.String(), " bytes")
                    step_start = time.Now()
                    broadcastData(step_no, cp_no, cp_resp1, no_CPs)
                    step_end = time.Since(step_start)
                    logrus.Info("Step no. ", step_no-s_no, " broadcast end-end time ", step_end.String())

                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_CPs-1) * (bSize+snoSize + sigSize + ((2*(b+n)*pointSize) + prf_len)) ))) //For broadcast
                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_CPs-1) * (no_CPs-2) * (bSize+snoSize+rSize+dSize + sigSize + (sigSize + hashSize)) ))) //For echo
                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_CPs-2) * (no_CPs-1) * (no_CPs-2) * (bSize+snoSize+rSize+dSize) ))) //For heartbeat

                    if cp_bcast == no_CPs {

                        f_flag = true //Set finish flag
                        break
                    }
                }

                if step_no == s_no + 3 {//If step no. 3

                    step_no += 1 //Set to next step

                    cp_bcast = 1 //Set CP1 as broadcasting CP

                    b_flag = false //Do nothing till DPs send ElGamal encrypted blinding values

                    logrus.Info("Waiting for DPs to send ElGamal encrypted blinding values")

                } else if step_no == s_no + 7 || step_no == s_no + 8 {//Fallback phases

                    b_flag = false //Do nothing till DS is over

                } else {

                    if cp_bcast == no_CPs { //If broadcasting CP is last CP

                        if step_no == s_no + 6 && fb_flag == false { //If step no. 6 and fallback option not set

                            step_no += 3 //Skip fallback option - skip broadcasting hash of all DP responses

                        } else {

                            step_no += 1 //Start next step broadcast
                        }

                        if step_no != s_no + 3 { //If step no. not 3 (in step 3, all CPs can send joint public key to DPs at the same time)

                            cp_bcast = 1 //Set CP1 as broadcasting CP
                        }

                    } else if cp_bcast != no_CPs { //If broadcasting CP is not last CP

                        cp_bcast = cp_no + 1 //Set next CP as broadcasting CP
                    }

                    //Set broadcast flag of next CP to true
                    if cp_no != cp_bcast {

                        b_flag = false

                    } else {

                        b_flag = true
                    }
                }

            } else {

                //If Data is available
                if conn := acceptConnections(cp_no, sock); conn != nil {

                    //Parse common name
                    com_name := parseCommonName(conn)

                    if com_name[0:len(com_name)-1] == "DP" { //If sender is a DP

                        buf := receiveData(conn) //Receive data
                        conn.Close() //Close connection
                        resp := new(DPres.Response)

                        if dp_no == 0 {

                            theoryStepBytes = big.NewInt(0) //Theoretical step communication cost
                            implStepBytes = big.NewInt(0) //Implementation step communication cost

                            step_start = time.Now()
                            logrus.Info("Starting step no. ", step_no-s_no)
                        }

                        //Proof length to calculate communication cost
                        prf_len := 0

                        //Verify sign
                        f := verifySign(0, buf)

                        if f == true { //If signature verified

                            l_buf := len(buf) //Length of buffer

                            //Received step no. in message
                            r_stepno := binary.BigEndian.Uint32(buf[bSize:bSize+snoSize])

                            //If step no. and broadcast flag verified
                            if r_stepno == step_no && uint8(buf[0]) == 1 {

                                //Compute hash
                                h := sha256.New()
                                h.Write(buf[:l_buf-sigSize]) //hash of DP response

                                //DP signature
                                tmp := make([]byte, len(buf[l_buf-sigSize:]))
                                copy(tmp[:], buf[l_buf-sigSize:])

                                proto.Unmarshal(buf[bSize+snoSize:l_buf-sigSize], resp) //DP response

                                //Buffer length to calculate communication cost
                                tb.Reset()
                                suite.Write(&tb, buf[:])

                                implStepBytes.Add(implStepBytes, big.NewInt(int64( len(tb.Bytes()) ))) //For receive implementation

                                if step_no == s_no + 4 { //If step no. 4

                                    //Store DP sign appended with hash of DP response
                                    s_b[dp_no] = append(tmp, h.Sum(nil)...)

                                    //Convert bytes to data
                                    for i := 0; i < b; i++ {

                                        //Store ElGamal encrypted blinding values
                                        tmpb := bytes.NewReader(resp.R[i]) //Temporary
                                        tr[dp_no][i] = suite.Point() //Temporary
                                        tr[dp_no][i].UnmarshalFrom(tmpb)

                                        tmpb = bytes.NewReader(resp.C[i]) //Temporary
                                        tc[dp_no][i] = suite.Point() //Temporary
                                        tc[dp_no][i].UnmarshalFrom(tmpb)

                                        //Verify proof
                                        rep := proof.Rep("X", "x", "B")
                                        public := map[string]kyber.Point{"B": suite.Point().Base(), "X": tr[dp_no][i]}
                                        verifier := rep.Verifier(suite, public)
                                        err := proof.HashVerify(suite, strconv.Itoa(int(step_no))+strconv.Itoa(dp_no)+strconv.Itoa(i), verifier, resp.Proof[i])
                                        prf_len = prf_len + len(resp.Proof[i][:])

                                        //If proof not verified
                                        if err != nil {

                                            nv_dp[dp_no+1] = true
                                        }
                                    }

                                    //If zkp verified
                                    if _, ok := nv_dp[dp_no+1]; !ok {

                                        //Add ElGamal encrypted blinding values
                                        for i := 0; i < b; i++ {

                                             R[i].Add(R[i], tr[dp_no][i])
                                             C[i].Add(C[i], tc[dp_no][i])
                                        }

                                    } else {

                                        logrus.Error("Incorrect proof for knowledge of randomness by DP ", dp_no+1)
                                    }

                                } else if step_no == s_no + 5 { //If step No. 5

                                    //Store signature prepended with hash of message
                                    s_c[dp_no] = append(h.Sum(nil), tmp...)

                                    //Convert bytes to data
                                    for j := 0; j < b; j++ {

                                        if _, ok := nv_dp[dp_no+1]; !ok {

                                            tmpb := suite.Scalar().SetBytes(resp.R[j])
                                            c_i[j].Add(c_i[j], tmpb) //Add blinded IP counter

                                            tc[dp_no][j].Add(tc[dp_no][j], suite.Point().Mul(c_i[j], nil)) //For easy removing of equivocating DPs later
                                        }
                                    }
                                }

                                //Increment the number of DPs responded
                                dp_no = dp_no + 1

                            } else {

                                logrus.Error("Dropping message. Expecting step no. ", step_no-s_no)
                                continue
                            }

                        } else { //If signature not verified

                            logrus.Error("Signature by DP ", dp_no+1, " not verified")
                            q_flag = true
                        }

           		//If all DPs have responded
                        if dp_no == no_DPs {

                            step_end = time.Since(step_start)
                            logrus.Info("Step no. ", step_no-s_no, " computing time ", step_end.String())

                            //Set CP1 as broadcasting CP
                            cp_bcast = 1

                            if cp_no == 1 {

                                b_flag = true //Set broadcasting flag of CP1
                            }

                            if step_no == s_no + 4 { //If step no. 4

                                dp_no = 0 //Initialize no. of DPs responded to zero (for inputs)

                                theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_DPs) * (no_CPs) * (bSize+snoSize + sigSize + (2*b*pointSize) + prf_len) ))) //For DP-CP blinded counters

                                theoryStepBytes.Add(theoryStepBytes, big.NewInt(int64( (no_DPs) * (bSize+snoSize + sigSize + (2*b*pointSize) + prf_len) ))) //For theory receive

                                logrus.Info("Step no. ", step_no-s_no, " communication cost ", implStepBytes.String(), " bytes")

                                logrus.Info("Waiting for DPs to send inputs")

                            } else if step_no == s_no + 5 { //If Step No. 5

                                //Iterate over all counters
                                for j := 0; j < b; j++ {

                                    //ElGamal encrypt blinded IP counters with the joint public key
                                    R[j].Add(R[j], suite.Point().Base())

                                    C[j].Add(C[j], suite.Point().Mul(c_i[j], nil))
                                    C[j].Add(C[j], Y)
                                }

                                theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_DPs) * (no_CPs) * (bSize+snoSize + sigSize + (b*scalarSize)) ))) //For DP-CP masked inputs

                                theoryStepBytes.Add(theoryStepBytes, big.NewInt(int64( (no_DPs) * (bSize+snoSize + sigSize + (b*scalarSize)) ))) //For theory receive

                                logrus.Info("Step no. ", step_no-s_no, " communication cost ", implStepBytes.String(), " bytes")
                            }

                            dp_no = 0 //Set no. of DPs responded to 0

                            step_no += 1 //Increment step no.
                        }

                    } else if com_name[0:len(com_name)-1] == "CP" { //If sender is a CP

                        ds_start = time.Now()
                        buf := receiveData(conn) //Receive data
                        conn.Close() //Close connection
                        cp_resp := new(CPres.Response)

                        src,_ := strconv.Atoi(com_name[len(com_name)-1:]) //No. of CP that sent

                        l_buf := len(buf) //Length of buffer

                        r_stepno := binary.BigEndian.Uint32(buf[bSize:bSize+snoSize]) //Step no. in received message

                        data_E := make([][]byte, 2) //Distinct messages received in the previous round

                        no_dm_E := 0 //No. of distinct messages received in previous round

                        //If step no. and broadcast flag verified
                        if r_stepno == step_no && (step_no != s_no + 7 && step_no != s_no + 8) && uint8(buf[0]) == 1 {

                            //Verify sign
                            f := verifySign(src, buf)

                            if f == true { //If signature verified

                                b_msg = buf[:l_buf-sigSize] //Store message received from source

                                //Compute hash
                                h := sha256.New()
                                h.Write(b_msg) //Message

                                //Store signature prepended with hash of message
                                tmp := make([]byte, len(buf[l_buf-sigSize:]))
                                copy(tmp[:], buf[l_buf-sigSize:])
                                s_dmsg[string(h.Sum(nil))] = append(h.Sum(nil), tmp...)

                                no_dmsgs += 1 //Increment no. of distinct messages
                                proto.Unmarshal(buf[bSize+snoSize:l_buf-sigSize], cp_resp) //Store message

                                //Set distinct message to be echoed in 1st round
                                data_E[0] = s_dmsg[string(h.Sum(nil))]
                                no_dm_E = 1

                            } else { //If signature not verified

                                logrus.Error("Dolev-Strong: signature by CP " + strconv.Itoa(src) + " not verified")
                                q_flag = true
                            }

                        } else if r_stepno != step_no { //If not expected step no.

                            logrus.Error("Dolev-Strong: expecting step no. " + strconv.Itoa(int(step_no-s_no)) + ", dropping message.")
                            continue

                        } else if (step_no != s_no + 7 && step_no != s_no + 8) && uint8(buf[0]) != 1 { //If broadcast flag not set

                            logrus.Error("Dolev-Strong: unformatted message by CP " + strconv.Itoa(cp_bcast) + ", dropping message.")
                            continue
                        }

                        if no_dmsgs == 1 || step_no == s_no + 7 || step_no == s_no + 8 { //If broadcast phase over

                            no_rnds := no_CPs - 1 //No. of rounds

                            if step_no == s_no + 7 || step_no == s_no + 8 { //'Broadcasted' message from DP

                                no_rnds = no_CPs
                            }

                            data := make([][]byte, 2) //Distinct messages received in current round

                            no_dm := 0 //No. of distinct messages received in current round

                            for rn := 0; rn < no_rnds; rn++ { //Iterate for no. of rounds

                                if rn != 0 {//If not the 1st round

                                    data_E = make([][]byte, 2)

                                    //Set distinct message to be echoed in this round
                                    for j := 0; j < no_dm; j++ { //Interate over no. of distinct messages received in previous round

                                        tb.Reset() //Buffer reset
                                        suite.Write(&tb, data[j])
                                        data_E[j] = make([]byte, len(tb.Bytes()))
                                        copy(data_E[j][:], tb.Bytes()) //Convert to bytes
                                    }

                                    no_dm_E = 1

                                    //Initialize distinct message received in current round
                                    data = make([][]byte, 2)
                                    no_dm = 0
                                }

                                for i := 0; i < no_CPs; i++ { //Iterate over all CPs

                                    if i+1 == cp_bcast { //If broadcasting CP

                                        continue //Broadcasting CP need not wait for anyone

                                    } else if i+1 != cp_no { //If not current CP's turn to echo

                                        flag := false

                                        e_cp := 1

                                        if (step_no == s_no + 7 || step_no == s_no + 8) && rn == 0 { //If step no. is 7 and 0th round - first CP has already echoed

                                            if (step_no == s_no + 7) { //Step no. 7

                                                s_dmsg[string(s_c[dp_no][:hashSize])] = s_c[dp_no]

                                            } else { //Step no. 8

                                                s_dmsg[string(s_b[dp_no][:hashSize])] = s_b[dp_no]
                                            }

                                            cp_bcast = 0 //DP is the broadcaster

                                            no_dmsgs = 1 //Set no. of distinct messages received so far to 1

                                            flag = true

                                        } else {

                                            conn = acceptConnections(cp_no, sock) //Accept new connections from echoing CP

                                            if conn != nil { //If data is available

                                                //Parse common name
                                                com_name = parseCommonName(conn)

                                                buf = receiveData(conn) //Receive data
                                                conn.Close() //Close connection

                                                e_cp, _ = strconv.Atoi(com_name[len(com_name)-1:]) //No. of CP that echoed

                                                flag = true

                                                implEchoRecvBytes.Add(implEchoRecvBytes, big.NewInt(int64( len(buf) ))) //For echo and heartbeat
                                            }
                                        }

                                        if flag == true {

                                            r_stepno = binary.BigEndian.Uint32(buf[bSize:bSize+snoSize]) //Step no. in received message
                                            rno := uint8(buf[bSize+snoSize+rSize-1]) //Round no.
                                            no_dm := uint8(buf[bSize+snoSize+rSize+dSize-1]) //No. of distinct messages

                                            //If header verified
                                            if r_stepno == step_no && uint8(buf[0]) == 0 && int(rno) == rn {

                                                if no_dm == 0 { //Heartbeat

                                                    continue

                                                } else {

                                                    //Verify sign
                                                    s_f, f := verifyEchoSign(cp_bcast, e_cp, buf, no_CPs)

                                                    index := bSize+snoSize+rSize+dSize //Initialize index (ignore header part)

                                                    for j := 0; j < no_dmsgs; j++ { //Interate over no. of distinct messages received so far

                                                        if s_f[j] == true && f[j] == true { //If signatures verified

                                                            if _, isExist := s_dmsg[string(buf[index:index+hashSize])]; !isExist { //Distinct message

                                                                data[j] = buf[index:index+hashSize+(int(rno+1)*sigSize)] //Store distinct message and signatures

                                                                no_dm = no_dm + 1 //Increment no. of distinct messages received in this round
                                                            }

                                                            s_dmsg[string(buf[index:index+hashSize])] = buf[index:index+hashSize+(int(rno+1)*sigSize)] //Store distinct message and signatures

                                                            index += hashSize+(int(rno+1)*sigSize) //Increment index

                                                        } else {

                                                            logrus.Error("Dolev-Strong: echoed message by CP " + strconv.Itoa(e_cp) + " - some signatures did not verify, dropping message")
                                                            continue
                                                        }
                                                    }

                                                    if len(s_dmsg) > 1 { //If no. of distinct messages received is greater than one

                                                        no_dmsgs = len(s_dmsg) //Set no. of distinct messages received

                                                        q_flag = true //Set quit flag
                                                    }
                                                }

                                            } else {

                                                logrus.Error("Dolev-Strong: unformatted message by CP " + strconv.Itoa(e_cp) + ", dropping message")
                                                continue
                                            }
                                        }

                                    } else if i+1 == cp_no { //If current CP's turn to echo

                                        time.Sleep(500*time.Millisecond)

                                        if no_dm > 1 {

                                            sendDataN_1(step_no, uint8(rn), uint8(no_dm), cp_bcast, i+1, data_E, no_CPs) //Echo distinct messages and signatures received in previous round

                                        } else {

                                            echo_start = time.Now()
                                            if rn == 0 { //If round no. 0

                                                sendDataN_1(step_no, uint8(rn), uint8(no_dm_E), cp_bcast, i+1, data_E, no_CPs) //Echo
                                                implEchoSendBytes.Add(implEchoSendBytes, big.NewInt(int64( (no_CPs-2) * (bSize+snoSize+rSize+dSize + sigSize + len(data_E[0][:])) ))) //For echo

                                            } else {

                                                sendDataN_1(step_no, uint8(rn), uint8(0), cp_bcast, i+1, nil, no_CPs) //Heartbeat
                                                implEchoSendBytes.Add(implEchoSendBytes, big.NewInt(int64( (no_CPs-2) * (bSize+snoSize+rSize+dSize) ))) //For echo
                                            }
                                            echo_end = time.Since(echo_start)
                                            logrus.Info("Step no. ", step_no-s_no, " echo/heartbeat time ", echo_end.String())
                                        }
                                    }
                                }
                            }
                            ds_end = time.Since(ds_start)
                            logrus.Info("Step no. ", step_no-s_no, " Dolev-Strong time ", ds_end.String())
                        }

                        if no_dmsgs > 1 && (step_no == s_no+7 || step_no == s_no+8) { //Fallback phases - remove DP

                            if _, ok := nv_dp[dp_no+1]; !ok { //If zkp verified

                                //Iterate over all counters
                                for i := 0; i < b; i++ {

                                    //Subtract that DP's value
                                    R[i].Sub(R[i], tr[dp_no][i])
                                    R[i].Sub(R[i], suite.Point().Base())

                                    C[i].Sub(C[i], tc[dp_no][i])
                                    C[i].Sub(C[i], Y)
                                }
                            }

                            no_dmsgs = 1 //Set to 1 to continue the protocol
                        }

                        if no_dmsgs == 1 { //If only one message in accept

                            logrus.Info("Dolev-Strong completed")

                            if step_no == s_no + 1 { //If step no. is 1

                                tmp := bytes.NewReader(cp_resp.R[0]) //Temporary
                                y[cp_bcast - 1] = suite.Point()
                                y[cp_bcast - 1].UnmarshalFrom(tmp)

                                //Verify proof
                                rep := proof.Rep("X", "x", "B")
                                public := map[string]kyber.Point{"B": suite.Point().Base(), "X": y[cp_bcast - 1]}
                                verifier := rep.Verifier(suite, public)
                                err := proof.HashVerify(suite, strconv.Itoa(int(step_no)), verifier, cp_resp.Proof[0])

                                //If proof not verified
                                if err != nil {

                                    logrus.Error("Incorrect proof for knowledge of private key by CP ", cp_bcast)
                                    q_flag = true //Set quit flag
                                    break
                                }

                                //Multiply to compute joint public key
                                Y.Add(Y, y[cp_bcast - 1])

                            } else if step_no == s_no + 2 { //If step no. is 2

                                tmp := bytes.NewReader(cp_resp.R[0]) //temporary
                                Ytmp := suite.Point()
                                Ytmp.UnmarshalFrom(tmp)

                                //Verify if echo broadcasted joint public key same as the one computed
                                if !Y.Equal(Ytmp) {

                                    logrus.Error("Joint public key from CP ", cp_bcast, " does not match")
                                    q_flag = true //Set quit flag
                                    break
                                }

                                //Compute hash of broadcater's message
                                h := sha256.New()
                                h.Write(b_msg) //Broadcaster's message

                                hmsg := s_dmsg[string(h.Sum(nil))]//Hashed message appended with signatures

                                s_Y[cp_bcast - 1] = hmsg[len(hmsg)-sigSize:] //Store signed joint public key

                            } else if step_no == s_no + 6 { //If step no. 6

                                //Convert bytes to data
                                for i := 0; i < b; i++ {

                                    tmp := bytes.NewReader(cp_resp.R[i]) //Temporary
                                    tp_R := suite.Point() //Temporary
                                    tp_R.UnmarshalFrom(tmp)

                                    tmp = bytes.NewReader(cp_resp.C[i])
                                    tp_C := suite.Point() //Temporary
                                    tp_C.UnmarshalFrom(tmp)

                                    //Verify if echo broadcasted aggregate same as the one received from DP
                                    if !(tp_R.Equal(R[i]) && tp_C.Equal(C[i])) {

                                        fb_flag = true //Set fallback option flag
                                    }
                                }

                                if fb_flag == true { //If fallback option flag true

                                    logrus.Error("Aggregate of DP ciphertexts from CP ", cp_bcast, " does not match")
                                }

                            } else if step_no == s_no + 9 { //If step no. 9

                                //Convert bytes to data
                                for i := 0; i < n; i++ {


                                    //Assign shuffled ElGamal encrypted noise
                                    tmp := bytes.NewReader(cp_resp.R[2*i]) //Temporary
                                    nr_o[i][0] = suite.Point()
                                    nr_o[i][0].UnmarshalFrom(tmp)

                                    tmp = bytes.NewReader(cp_resp.R[(2*i)+1])
                                    nr_o[i][1] = suite.Point()
                                    nr_o[i][1].UnmarshalFrom(tmp)

                                    tmp = bytes.NewReader(cp_resp.C[2*i]) //Temporary
                                    nc_o[i][0] = suite.Point()
                                    nc_o[i][0].UnmarshalFrom(tmp)

                                    tmp = bytes.NewReader(cp_resp.C[(2*i)+1])
                                    nc_o[i][1] = suite.Point()
                                    nc_o[i][1].UnmarshalFrom(tmp)

                                    //Verify proof
                                    verifier := shuffle.BiffleVerifier(suite, nil, Y, nr[i], nc[i], nr_o[i], nc_o[i])
                                    err := proof.HashVerify(suite, strconv.Itoa(int(step_no))+strconv.Itoa(i), verifier, cp_resp.Proof[i])

                                    //If proof not verified
                                    if err != nil {

                                        q_flag = true //Set quit flag
                                    }
                                }

                                if q_flag == true { //If quit flag true

                                    logrus.Error("Incorrect shuffle proof for noise generation by CP ", cp_bcast)
                                    break
                                }

                                //Iterate over all noise counters
                                for i := 0; i < n; i++ {

                                    //Swap current output as input
                                    nr[i][0] = suite.Point().Set(nr_o[i][0])
                                    nr[i][1] = suite.Point().Set(nr_o[i][1])
                                    nc[i][0] = suite.Point().Set(nc_o[i][0])
                                    nc[i][1] = suite.Point().Set(nc_o[i][1])
                                }

                                //If last CP has broadcasted
                                if cp_bcast == no_CPs {

                                    //Iterate over all noise counters
                                    for i := b; i < b+n; i++ {

                                        //Select 1st coin as noise
                                        R[i] = suite.Point().Set(nr[i-b][0])
                                        C[i] = suite.Point().Set(nc[i-b][0])
                                    }
                                }

                            } else if step_no == s_no + 10 { //If step no. 10

                                //Convert bytes to data
                                for i := 0; i < b+n; i++ {

                                    //Assign shuffled ElGamal encrypted counters
                                    tmp := bytes.NewReader(cp_resp.R[i]) //Temporary
                                    R_O[i] = suite.Point()
                                    R_O[i].UnmarshalFrom(tmp)

                                    tmp = bytes.NewReader(cp_resp.C[i])
                                    C_O[i] = suite.Point()
                                    C_O[i].UnmarshalFrom(tmp)
                                }

                                //Verify proof
                                verifier := shuffle.Verifier(suite, nil, Y, R, C, R_O, C_O)
                                err := proof.HashVerify(suite, strconv.Itoa(int(step_no)), verifier, cp_resp.Proof[0][:])

                                //If not verified
                                if err != nil {
                                    logrus.Error("Incorrect verifiable shuffle proof by CP ", cp_bcast)
                                    q_flag = true //Set quit flag
                                    break
                                }

                                //Iterate over all counters
                                for i := 0; i < b+n; i++ {

                                    //Swap current output as input
                                    R[i] = suite.Point().Set(R_O[i])
                                    C[i] = suite.Point().Set(C_O[i])
                                }

                            } else if step_no == s_no + 11 { //If step no. 11

                                prf := make([]ReRandomizeDecryptProof, b+n)

                                yi := suite.Point().Null() //Partial joint public key

                                //Compute partial joint public key
                                for i := cp_bcast-1; i < no_CPs; i++ {

                                    yi.Add(yi, y[i])
                                }

                                //Convert bytes to data
                                for i := 0; i < b+n; i++ {

                                    //Assign re-randomized decrypted ElGamal encrypted counters
                                    tmp := bytes.NewReader(cp_resp.R[i]) //Temporary
                                    R_O[i] = suite.Point()
                                    R_O[i].UnmarshalFrom(tmp)

                                    tmp = bytes.NewReader(cp_resp.C[i])
                                    C_O[i] = suite.Point()
                                    C_O[i].UnmarshalFrom(tmp)

                                    tmp = bytes.NewReader(cp_resp.Proof[i])
                                    suite.Read(tmp, &prf[i])
                                }

                                //Verify proof
                                err := rerandomizeDecryptVerifyBatch(suite, R, C, nil, yi, y[cp_bcast - 1], R_O, C_O, prf)

                                if err != nil {

                                    logrus.Error("Incorrect re-randomize and decrypt proof by CP ", cp_bcast)

                                    q_flag = true //Set quit flag
                                }

                                for i := 0; i < b+n; i++ {

                                    //If re-randomized with power zero
                                    if R_O[i].Equal(suite.Point().Base()) == true {

                                        logrus.Error("CP ", cp_bcast, " re-randomized with power zero")

                                        q_flag = true //Set quit flag

                                        break
                                    }
                                }

                                if q_flag == true { //If quit flag true

                                    break
                                }

                                for i := 0; i < b+n; i++ {

                                    //Swap current output as input
                                    R[i] = suite.Point().Set(R_O[i])
                                    C[i] = suite.Point().Set(C_O[i])
                                }

                                if cp_bcast == no_CPs {
                                    f_flag = true //Set finish flag
                                    break
                                }
                            }

                            if cp_bcast == 0 { //Fallback phases

                                if dp_no == no_DPs { //If DS of all DPs completed

                                    step_no += 1 //Start next step broadcast

                                } else {

                                    dp_no = dp_no + 1 //Index of DP to run DS
                                }

                                cp_bcast = 1

                            } else if cp_bcast == no_CPs { //If broadcasting CP is last CP

                                if step_no == s_no + 6 && fb_flag == false {

                                    step_no += 3 //Skip fallback option - skip broadcasting hash of all DP responses

                                } else {

                                    step_no += 1 //Start next step broadcast
                                }

                                if step_no != s_no + 3 { //If step no. not 3 (In step no. 3 all CPs can send joint public key to DPs at the same time)

                                    cp_bcast = 1 //Set CP1 as broadcasting CP

                                } else {

                                    cp_bcast = cp_no //Set current CP as Broadcasting CP
                                }

                            } else if cp_bcast != no_CPs {

                                cp_bcast += 1 //Set broadcasting CP as next CP
                            }

                            //Set broadcasting flag of broadcasting CP to true
                            if cp_no == cp_bcast {

                                b_flag = true
                            }

                            s_dmsg = make(map[string][]byte) //Re-initialize
                            no_dmsgs = 0 //Set no. of CPs broadcasted/echoed to 0
                        }
                    }
                }
            }
        } else {
            break
        }
    }
    if q_flag == true {

        logrus.Error("Aborting")

    } else if f_flag == true {

        //Iterate over all Counters
        for i := 0; i < b+n; i++ {

            //If not g^0
            if e_f := C[i].Equal(suite.Point().Null()); e_f == false {

                //Add 1 to aggregate
                agg += 1
            }
        }

        agg -= int64(n/2)

        logrus.Info("Starting duration ", time.Since(start_time).String())
        logrus.Info("Aggregate = ", agg)
        logrus.Info("Finishing")

        end := time.Since(start)
        logrus.Info("Execution time", end.String())

        compCost := new(COMtime.Time)
        compCost.T = make([]string, 1)
        compCost.T[0] = end.String()
        out, _ := proto.Marshal(compCost)
        ioutil.WriteFile(outputPath + "cp" + strconv.Itoa(cp_no) + ".time", out, 0644)

        logrus.Info("CP send communication cost ", implSendBytes, " bytes")
        logrus.Info("CP receive communication cost ", implRecvBytes, " bytes")
        logrus.Info("CP Dolev-Strong echo send communication cost ", implEchoSendBytes.String(), " bytes")
        logrus.Info("CP Dolev-Strong echo receive communication cost ", implEchoRecvBytes.String(), " bytes")

        commCost := new(COMbytes.Bytes)
        commCost.T = make([]string, 1)
        commCost.R = make([]string, 1)
        commCost.S = make([]string, 1)
        commCost.T[0] = theoryBytes.String()
        commCost.R[0] = implRecvBytes.String()
        commCost.S[0] = implSendBytes.String()
        out, _ = proto.Marshal(commCost)
        ioutil.WriteFile(outputPath + "cp" + strconv.Itoa(cp_no) + ".bytes", out, 0644)
    }
    os.Exit(0)
}

//Input: Command-line arguments
//Output: CP no.
//Function: Parse command-line arguments
func parseCommandline(arg []string) (int) {

    cp, _ := strconv.Atoi(os.Args[1]) //CP name

    return cp
}

//Input: Data, Source, Destination
//Function: Send data to destination (if destination is 0, send to DP)
func sendDataToDest(data []byte, src int, dst int) {

    //Load private key and certificate
    cert, err := tls.LoadX509KeyPair("certs/CP" + strconv.Itoa(src) + ".cert", "private/CP" + strconv.Itoa(src)  + ".key")
    checkError(err)

    var addr_port string //Address and port

    if dst == 0 {

     addr_port = dpIP + ":" + dpPort

    } else {

     addr_port = cpIPs[dst-1] + ":" + cpPortPrefix + strconv.Itoa(dst)
    }

    //Dial TCP connection
    config := tls.Config{Certificates: []tls.Certificate{cert}, InsecureSkipVerify: true}
    con,err := net.Dial("tcp", addr_port)
    checkError(err)

    //Convert to TLS connection
    file, err := con.(*net.TCPConn).File()
    err = syscall.SetsockoptInt(int(file.Fd()), syscall.SOL_SOCKET, syscall.SO_REUSEADDR, 1)
    conn := tls.Client(con, &config)

    l := make([]byte, 4) //Length of data sent in bytes
    binary.BigEndian.PutUint32(l, uint32(len(data)))
    data = append(l, data...) //Append length to data
    n, err1 := conn.Write(data) //Send data to destination
    checkError(err1)

    implSendBytes.Add(implSendBytes, big.NewInt(int64(n))) //For echo
}

//Input: Socket, No. of bytes
//Output: Message buffer
//Function: Read exactly n bytes from the socket
func socketReadN(conn net.Conn, n uint32) []byte {
    buf := make([]byte, n)
    _, err := io.ReadFull(conn,buf) //Read n bytes
    checkError(err)

    implRecvBytes.Add(implRecvBytes, big.NewInt(int64(n))) //For echo

    return buf
}

//Input: Socket
//Output: Message
//Function: Read message from socket
func receiveData(conn net.Conn) []byte {
    len_buf := socketReadN(conn, 4) //Read message length
    msg_len := binary.BigEndian.Uint32(len_buf) //Length of message
    msg_buf := socketReadN(conn, msg_len) //Read message
    return msg_buf
}

//Input: Listener
//Output: Socket
//Function: Accept new connections in  socket
func acceptConnections(cp int, listener net.Listener) *tls.Conn {
    //Create server socket
    cert, err := tls.LoadX509KeyPair("certs/CP"+ strconv.Itoa(cp) +".cert", "private/CP" + strconv.Itoa(cp) + ".key")
    checkError(err)

    //Add CA certificate to pool
    caCert, _ := ioutil.ReadFile("../CA/certs/ca.cert")
    caCertPool := x509.NewCertPool()
    caCertPool.AppendCertsFromPEM(caCert)

    //Create TLS listener and accept connection
    config := tls.Config{Certificates: []tls.Certificate{cert}, ClientCAs: caCertPool, ClientAuth: tls.RequireAndVerifyClientCert,}
    conn, err := listener.Accept()
    file, err := conn.(*net.TCPConn).File()
    err = syscall.SetsockoptInt(int(file.Fd()), syscall.SOL_SOCKET, syscall.SO_REUSEADDR, 1)
    sock := tls.Server(conn, &config)

    return sock
}

//Input: CP no.
//Output: Server socket
//Function: Creates server socket
func createServer(cp_no int) net.Listener {

    var addr_port string //Address and port no.

    addr_port = cpIPs[cp_no-1] + ":" + cpPortPrefix + strconv.Itoa(cp_no)

    //Create TCP listener
    listener, _ := net.Listen("tcp", addr_port)

    return listener
}

//Input: Step no., Source, Data, No. of DPs
//Function: Sign and send data to all DPs
func signSendDataToDP(step_no uint32,  src int, data []byte, no_DPs int) {

    //Read private key from file
    in, err := ioutil.ReadFile("schnorr/private/cp" + strconv.Itoa(src) + ".priv")
    checkError(err)
    priv := &Schnorrkey.Priv{}
    err = proto.Unmarshal(in, priv)
    checkError(err)

    //Convert bytes to private key
    x := suite.Scalar().SetBytes(priv.X)

    //Add step no.
    b_s := make([]byte, snoSize)
    binary.BigEndian.PutUint32(b_s, step_no) //Set step no.
    data = append(b_s, data...) //Prepend step no.

    //Compute hash
    h := sha256.New()
    h.Write(data)
    hdata := h.Sum(nil)

    //Iterate over all CPs
    for i := 0; i < no_DPs; i++ {

        //Sign message
        sign, _ := schnorr.Sign(suite, x, hdata)
        sign = append(data, sign...) //Append data

        //Send to destination DP
        sendDataToDest(sign, src, 0)
    }
}

//Input: Step no., Source CP, Data, No. of CPs
//Function: Broadcast data to all CPs
func broadcastData(step_no uint32, src int, data []byte, no_CPs int) {

    //Read private key from file
    in, err := ioutil.ReadFile("schnorr/private/cp" + strconv.Itoa(src) + ".priv")
    checkError(err)
    priv := &Schnorrkey.Priv{}
    err = proto.Unmarshal(in, priv)
    checkError(err)

    //Convert bytes to private key
    x := suite.Scalar().SetBytes(priv.X)

    //Add broadcast flag and step no.
    b_s := make([]byte, bSize+snoSize)
    b_s[0] = byte(1) //Set broadcast flag
    binary.BigEndian.PutUint32(b_s[bSize:], step_no) //Set step no.
    data = append(b_s, data...) //Prepend broadcast flag and step no.

    //Compute hash
    h := sha256.New()
    h.Write(data)
    hdata := h.Sum(nil)

    //Sign message
    sign, _ := schnorr.Sign(suite, x, hdata)
    sign = append(data, sign...) //Prepend data

    //Iterate over all CPs
    for i := 0; i < no_CPs; i++ {

        //Send to all other CPs
        if i + 1 != src {

            sendDataToDest(sign, src, i + 1)
        }
    }
}

//Input: Step No., Round No., No. of distnct messages received, Source (if src is 0, must be from DP (i.e., fallback phase)), Echoing CP, Data, No. of CPs
//Function: Send to All CPs but the Source
func sendDataN_1(step_no uint32, r_no, no_dm uint8, src int, cp int, data [][]byte, no_CPs int) {

    //Read private key from file
    in, _ := ioutil.ReadFile("schnorr/private/cp" + strconv.Itoa(cp) + ".priv")
    priv := &Schnorrkey.Priv{}
    proto.Unmarshal(in, priv)

    //Convert bytes to private key
    x := suite.Scalar().SetBytes(priv.X)

    //Add broadcast flag,step no., round no., and no. of distnct messages received in previous round
    b_s := make([]byte, bSize+snoSize+rSize+dSize)
    b_s[0] = byte(0) //Set broadcast flag to 0
    binary.BigEndian.PutUint32(b_s[1:], step_no) //Set step no.
    b_s[5] = byte(r_no) //Set round no.
    b_s[6] = byte(no_dm) //Add no. of distnct messages received in previous round (send a maximum of 'minDM' messages)

    var sdata []byte //Data to be sent

    if int(no_dm) == 1 || int(no_dm) == 2 { //If no. of distnct messages received in previous round is one or two

        //Iterate over no. of distnct messages received in previous round
        for i := 0; i < int(no_dm); i++ {

            if i == 0 { //If first distinct message, prepend header

                sdata = append(b_s, data[i]...) //Prepend broadcast flag,step no., round no., and no. of distnct messages received in previous round

            } else { //Else append distinct message

                sdata = append(sdata, data[i]...) //Append distinct message
            }

            //Sign message
            sign, _ := schnorr.Sign(suite, x, data[i][:hashSize])
            sdata = append(sdata, sign...) //Append sign
        }

    } else if int(no_dm) == 0 { //If no. of distnct messages received in previous round is one or zero

        //Heartbeat
        sdata = make([]byte, len(b_s))
        copy(sdata[:], b_s)
    }

    //Iterate over all CPs
    for i := 0; i < no_CPs; i++ {

        //Send to other n-1 CPs
        if i + 1 != cp && i + 1 != src {

            sendDataToDest(sdata, cp, i+1)
        }
    }
}

//Input: Source (if source is 0, verify DP sign), Data
//Output: Bool (verified / not)
//Function: Verify sign
func verifySign(src int, data []byte) (bool) {

    var pubkey_fname string //Public key filename

    if src == 0 {

        pubkey_fname = "dp1" //DP public key filename

    } else {

        pubkey_fname = "cp" + strconv.Itoa(src) //CP public key filename
    }

    //Read public key from file
    in, _ := ioutil.ReadFile("schnorr/public/" + pubkey_fname + ".pub")
    buf := &Schnorrkey.Pub{}
    proto.Unmarshal(in, buf)

    y := bytes.NewReader(buf.Y) //Public key in bytes
    pub := suite.Point() //Public key
    pub.UnmarshalFrom(y)

    //Parse signature
    sign := data[len(data)-sigSize:] //Sign

    //Compute hash
    h := sha256.New()
    h.Write(data[:len(data)-sigSize])
    hdata := h.Sum(nil)

    //Verify signed message
    err := schnorr.Verify(suite, pub, hdata, sign)

    var f bool //Flag to be returned

    if err == nil {

        f = true

    } else {

        f = false
    }

    return f
}

//Input: Source CP, Echoing CP, Data, No. of CPs
//Output: Bool (verified / not), Source sign verified or not
//Function: Verify all CP signs in all distinct messages
func verifyEchoSign(src, cp int, data []byte, no_CPs int) ([]bool, []bool) {

    rno := int(data[bSize+snoSize+rSize-1]) //Round no.
    no_dm := int(data[bSize+snoSize+rSize+dSize-1]) //No. of distinct messages

    //Flags to be returned
    f := make([]bool, no_dm)
    s_f := make([]bool, no_dm)

    for i := 0; i < no_dm; i++ { //Iterate over no. of distinct messages received

        //Initialize flags
        f[i] = true
        s_f[i] = true
    }

    pub := make([]kyber.Point, no_CPs) //Public key

    //Iterate over no. of CPs
    for i := 0; i < no_CPs; i++ {

        //Read public key from file
        in, _ := ioutil.ReadFile("schnorr/public/" + "cp" + strconv.Itoa(i+1) + ".pub")
        buf := &Schnorrkey.Pub{}
        proto.Unmarshal(in, buf)

        y := bytes.NewReader(buf.Y) //Public key in bytes
        pub[i] = suite.Point() //Public key
        pub[i].UnmarshalFrom(y)
    }

    index := bSize+snoSize+rSize+dSize //Initialize index (ignore header part)

    //Iterate over no. of distnct messages received
    for i := 0; i < int(no_dm); i++ {

        hdata := data[index:index+hashSize] //Hashed message

        index += hashSize //Increment start index

        var err error

        if src == 0 {

            //Read public key from file
            in, _ := ioutil.ReadFile("schnorr/public/dp1.pub")
            buf := &Schnorrkey.Pub{}
            proto.Unmarshal(in, buf)

            y := bytes.NewReader(buf.Y) //Public key in bytes
            dppub := suite.Point() //Public key
            dppub.UnmarshalFrom(y)

            err = schnorr.Verify(suite, dppub, hdata, data[index:index+sigSize]) //Verify signed message

        } else {

            err = schnorr.Verify(suite, pub[src - 1], hdata, data[index:index+sigSize]) //Verify signed message

        }

        if err != nil {

            s_f[i] = false
        }

        index += sigSize //Increment start index

        //Iterate over no. of signatures
        for j := 0; j < rno - 1; j++ {

            tflag := false //Temporary flag to check if at least one of the CP signatures are verified

            //Iterate over all CPs
            for k := 0; k < no_CPs; k++ {

                //Verify if signature from any of the other 'n - 2' CPs
                if (src == 0 && k + 1 != cp) || (src != 0 && k + 1 != cp && k + 1 != src) {

                    err := schnorr.Verify(suite, pub[k], hdata, data[index:index+sigSize]) //Verify signed message

                    if err == nil {

                        tflag = true
                    }
                }
            }

            if !tflag { //If temporary flag not set

                f[i] = false
            }

            index += sigSize //Increment start index
        }

        err = schnorr.Verify(suite, pub[cp - 1], hdata, data[index:index+sigSize]) //Verify signed message

        if err != nil {

            f[i] = false
        }
    }

    return s_f, f
}

//Input: Points, Points
//Output: Shuffled noise
//Function: Shuffle noise
func shuffleNoise(x, y [2]kyber.Point, Y kyber.Point) ([2]kyber.Point, [2]kyber.Point, proof.Prover) {

    xbar, ybar, proof := shuffle.Biffle(suite, nil, Y, x, y, pseudorand) //Shuffle Noise Vectors

    return xbar, ybar, proof
}

//Input: Client socket
//Output: Common name
//Function: Parse common name from certificate
func parseCommonName(conn net.Conn) string {

    var com_name string //Common name
    tlscon, ok := conn.(*tls.Conn)

    //If TLS connection
    if ok {
        tlscon.Handshake()
        for _, v := range tlscon.ConnectionState().PeerCertificates {
            com_name = v.Subject.CommonName //Get common name
        }
    }

    return com_name
}

//Computes a new NIZK proof for the scalars s and q with respect to base points A and B and publicly known points G, H.
//It therefore randomly selects commitments t1, t2 and t3 and then computes the challenge c = H(q(sG+A),q(sH+B-x(sG+A)),
//t1A+t2G,t1B+t2H+t3(qsG+qA),t3G) and responses r1 = qc+t1, r2 = sqc + t2 and r3 = -xc + t3. Besides the proof, this
//function also returns the re-encrypted, re-randomized, and decrypted base points A1 = q(sG+A) and B1 = q(sH+B)-xA1.
func rerandomizeDecryptProof(suite proof.Suite, A, B, G, H kyber.Point, s, q, x kyber.Scalar) (proof *ReRandomizeDecryptProof, A1 kyber.Point, B1 kyber.Point, err error) {

    // Re-encrypt base points
    A1 = suite.Point().Add(A, suite.Point().Mul(s, G))
    B1 = suite.Point().Add(B, suite.Point().Mul(s, H))

    // Re-randomize base points
    A1.Mul(q, A1)
    B1.Mul(q, B1)

    //Decrypt base point
    B1.Sub(B1, suite.Point().Mul(x, A1))

    //Commitment
    t1 := suite.Scalar().Pick(suite.RandomStream())
    t2 := suite.Scalar().Pick(suite.RandomStream())
    t3 := suite.Scalar().Pick(suite.RandomStream())
    T1 := suite.Point().Mul(t1, A)
    T2 := suite.Point().Mul(t1, B)
    T3 := suite.Point().Mul(t3, G)
    T1.Add(T1, suite.Point().Mul(t2, G))
    T2.Add(T2, suite.Point().Mul(t2, H))
    T2.Add(T2, suite.Point().Mul(t3, A1))

    //Challenge
    h := suite.Hash()
    A1.MarshalTo(h)
    B1.MarshalTo(h)
    T1.MarshalTo(h)
    T2.MarshalTo(h)
    T3.MarshalTo(h)
    cb := h.Sum(nil)
    c := suite.Scalar().Pick(suite.XOF(cb))

    //Response
    r1 := suite.Scalar().Mul(q, c)
    r2 := suite.Scalar().Mul(s, r1)
    r3 := suite.Scalar().Set(t3)
    r1 = r1.Add(r1, t1)
    r2 = r2.Add(r2, t2)
    r3 = r3.Sub(r3, suite.Scalar().Mul(x, c))

    return &ReRandomizeDecryptProof{c, r1, r2, r3}, A1, B1, nil
}

//Computes lists of NIZK re-randomize and decrypt proofs of encrypted base points A1 and B1.
//Note that the challenge is computed over all input values.
func rerandomizeDecryptProofBatch(suite proof.Suite, A, B, A1, B1 []kyber.Point, G, H kyber.Point, s, q []kyber.Scalar, x kyber.Scalar) (proof []ReRandomizeDecryptProof, err error) {
    if len(A) != len(B) || len(A1) != len(B1) || len(s) != len(q) || len(A) != len(A1) || len(A) != len(s) {
        return nil, errors.New("inputs of different lengths")
    }

    n := len(s)
    proofs := make([]ReRandomizeDecryptProof, n)
    t1 := make([]kyber.Scalar, n)
    t2 := make([]kyber.Scalar, n)
    t3 := make([]kyber.Scalar, n)
    T1 := make([]kyber.Point, n)
    T2 := make([]kyber.Point, n)
    T3 := make([]kyber.Point, n)

    for i := 0; i < n; i++ {

        //Commitment
        t1[i] = suite.Scalar().Pick(suite.RandomStream())
        t2[i] = suite.Scalar().Pick(suite.RandomStream())
        t3[i] = suite.Scalar().Pick(suite.RandomStream())
        T1[i] = suite.Point().Mul(t1[i], A[i])
        T2[i] = suite.Point().Mul(t1[i], B[i])
        T3[i] = suite.Point().Mul(t3[i], G)
        T1[i].Add(T1[i], suite.Point().Mul(t2[i], G))
        T2[i].Add(T2[i], suite.Point().Mul(t2[i], H))
        T2[i].Add(T2[i], suite.Point().Mul(t3[i], A1[i]))
    }

    //Challenge
    h := suite.Hash()
    for _, i := range A1 {
        i.MarshalTo(h)
    }
    for _, i := range B1 {
        i.MarshalTo(h)
    }
    for _, i := range T1 {
        i.MarshalTo(h)
    }
    for _, i := range T2 {
        i.MarshalTo(h)
    }
    for _, i := range T3 {
        i.MarshalTo(h)
    }
    cb := h.Sum(nil)
    c := suite.Scalar().Pick(suite.XOF(cb))

    //Responses
    for i := 0; i < n; i++ {
        //Response
        r1 := suite.Scalar().Mul(q[i], c)
        r2 := suite.Scalar().Mul(s[i], r1)
        r3 := suite.Scalar().Set(t3[i])
        r1 = r1.Add(r1, t1[i])
        r2 = r2.Add(r2, t2[i])
        r3 = r3.Sub(r3, suite.Scalar().Mul(x, c))
        proofs[i] = ReRandomizeDecryptProof{c, r1, r2, r3}
    }

    return proofs, nil
}

//Examines the validity of the NIZK re-randomize decrypt proof. The proof is valid if the following three conditions hold:
//r1A + r2G == cA1 + T1
//r1B + r2H + r3A1 == cB1 + T2
//r3G = T3 - cI
func rerandomizeDecryptVerifyBatch(suite proof.Suite, A, B []kyber.Point, G, H, I kyber.Point, A1, B1 []kyber.Point, p []ReRandomizeDecryptProof) error {

    if len(A) != len(B) || len(A1) != len(B1) || len(A) != len(A1) {
        return errors.New("inputs of different lengths")
    }

    n := len(A)
    T1 := make([]kyber.Point, n)
    T2 := make([]kyber.Point, n)
    T3 := make([]kyber.Point, n)

    for i := 0; i < n; i++ {

        r1A := suite.Point().Mul(p[i].R1, A[i])
        r1B := suite.Point().Mul(p[i].R1, B[i])
        r2G := suite.Point().Mul(p[i].R2, G)
        r2H := suite.Point().Mul(p[i].R2, H)
        cA1 := suite.Point().Mul(p[i].C, A1[i])
        cB1 := suite.Point().Mul(p[i].C, B1[i])
        r3A1 := suite.Point().Mul(p[i].R3, A1[i])
        cI := suite.Point().Mul(p[i].C, I)

        T1[i] = suite.Point().Add(r1A, r2G)
        T1[i].Sub(T1[i], cA1)
        T2[i] = suite.Point().Add(r1B, r2H)
        T2[i].Add(T2[i], r3A1)
        T2[i].Sub(T2[i], cB1)
        T3[i] = suite.Point().Mul(p[i].R3, G)
        T3[i].Add(T3[i], cI)
    }

    //Challenge
    h := suite.Hash()
    for _, i := range A1 {
        i.MarshalTo(h)
    }
    for _, i := range B1 {
        i.MarshalTo(h)
    }
    for _, i := range T1 {
        i.MarshalTo(h)
    }
    for _, i := range T2 {
        i.MarshalTo(h)
    }
    for _, i := range T3 {
        i.MarshalTo(h)
    }
    cb := h.Sum(nil)
    c := suite.Scalar().Pick(suite.XOF(cb))

    if !(c.Equal(p[0].C)) {
        return errors.New("invalid proof")
    }

    return nil
}

//Input: Error
//Function: Check error
func checkError(err error){
    if err != nil {
        logrus.Panic(os.Stderr, "Fatal error: %s", err.Error())
        os.Exit(1)
    }
}
