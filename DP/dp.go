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
    "fmt"
    "go.dedis.ch/kyber/v3"
    "go.dedis.ch/kyber/v3/group/edwards25519"
    "go.dedis.ch/kyber/v3/proof"
    "go.dedis.ch/kyber/v3/sign/schnorr"
    "github.com/sirupsen/logrus"
    "github.com/golang/protobuf/proto"
    "io"
    "io/ioutil"
    "math/big"
    //"math/rand"
    "net"
    "os"
    "psc/config"
    "psc/lib/cpres"
    "psc/lib/dpres"
    "psc/lib/combytes"
    "psc/lib/sessionno"
    "psc/lib/schnorrkey"
    "psc/lib/ipcount"
    "strconv"
    "syscall"
    "time"
)


var suite = edwards25519.NewBlakeSHA256Ed25519() //Cipher suite
var pointSize = suite.Point().MarshalSize() //Point size
var scalarSize = suite.Scalar().MarshalSize() //Scalar size
var sigSize = scalarSize + pointSize //Schnorr signature length
var hashSize = sha256.Size
var bSize = 1 //Broadcast flag length (fixed)
var snoSize = 4 //Step no. length (fixed)

var theoryBytes = big.NewInt(0) //Theoretical communication cost
var implRecvBytes = big.NewInt(0) //Implementation receive communication cost
var implSendBytes = big.NewInt(0) //Implementation send communication cost
var theoryStepBytes = big.NewInt(0) //Theoretical step communication cost
var implStepBytes = big.NewInt(0) //Implementation step communication cost

var step_start time.Time //Step start time
var step_end time.Duration //Step end time
var step_avg time.Time //Step average time

var waitTime = config.WaitTime //Wait time to send commitments
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

    b := config.B //No. of entries in IP table
    no_CPs := config.NoCPs //No.of CPs
    no_DPs := config.NoDPs //No. of DPs
    outputPath := config.OutputPath

    cpIPs = make([]string, no_CPs) //Initialize

    //Iterate over all CPs
    for j := 0; j < no_CPs; j++ {

        cpIPs[j] = config.CP_IPs[j] //Initialize with CP IP addresses
    }

    var s_no uint32 //Session no.
    var step_no uint32 //Step no.
    agg := 0 //Actual aggregate
    jpk_no := 0 //No. of joint public key response received from CP so far
    dp_resp_no := make([]int, no_CPs) //A list to keep track of no. of DP responses each CP has sent
    ver_jpk := make(map[int]([]byte)) //A map to keep track of verified joint public key for each DP

    uniqIPList := make([]int64, b)
    pseudorand := suite.RandomStream()

    f_flag := false //Finish flag
    q_flag := false //Quit flag

    //Set session no.
    in, err := ioutil.ReadFile("../session/session.no")
    checkError(err)
    sno := &Sessionno.SNo{}
    err = proto.Unmarshal(in, sno)
    checkError(err)
    s_no = *sno.S

    //Read DP public key from file
    in, _ = ioutil.ReadFile("schnorr/public/dp1.pub")
    dp_pub := &Schnorrkey.Pub{}
    proto.Unmarshal(in, dp_pub)

    Y := suite.Point() //CP joint public key

    tmp := suite.Scalar() //temporary

    //Iterate over all CPs
    for i := 0; i < no_CPs; i++ {

        dp_resp_no[i] = 0 //Initialize no. of DP responses (for each CP) to zero
    }

    //Set step no.
    step_no = s_no + 3 //CPs send signed joint public key in step 3

    logrus.Info("Started server")

    //Listen to the TCP port
    sock := createServer()

    for{
        //If quit flag not true
        if q_flag == false && f_flag == false {

            //If step no. is 3
            if  step_no == s_no + 3 {

                //If data is available
                if conn := acceptConnections(sock); conn != nil {

                    //Parse common name
                    com_name := parseCommonName(conn)

                    if com_name[0:len(com_name)-1] == "CP" { //If sender is a CP

                        buf := receiveData(conn) //Receive data
                        conn.Close() //Close connection
                        cp_resp := new(CPres.Response)

                        if jpk_no == 0 {

                            theoryStepBytes = big.NewInt(0) //Theoretical step communication cost
                            implStepBytes = big.NewInt(0) //Implementation step communication cost

                            step_avg = time.Time{} //Step average time
                        }

                        step_start = time.Now() //Step start time

                        cp_no, _ := strconv.Atoi(com_name[len(com_name)-1:]) //No. of CP that sent

                        implStepBytes.Add(implStepBytes, big.NewInt(int64( len(buf[:]) ))) //For receive implementation

                        //Verify sign
                        f := verifySign(cp_no, buf)

                        if f == true { //If signature verified

                            l_buf := len(buf) //Length of buffer

                            //Step no. in received message
                            r_stepno := binary.BigEndian.Uint32(buf[:snoSize])

                            //If step no. verified
                            if r_stepno == step_no {

                                dp_no := dp_resp_no[cp_no-1]
                                r_msg := buf[snoSize:l_buf-sigSize] //Received message
                                m_jpk := r_msg[bSize+snoSize:len(r_msg)-((no_CPs-1)*sigSize)] //Marshalled joint public key (Received message appended with (n-1) CP signatures and prepended with CP broadcast flag and CP step no.)

                                if verjpk, ok := ver_jpk[dp_no]; ok == true { //Extract previous verified response (if any)

                                    if !bytes.Equal(verjpk, m_jpk) {

                                        if isCPmisbehaving(cp_no, step_no-1, r_msg, no_CPs) == true { //Current CP is misbehaving

                                            logrus.Error("CP ", cp_no, " is misbehaving")

                                        } else {

                                            m_cp := "CP" //Misbehaving CP names

                                            //Iterate over all CPs
                                            for i := 0; i < no_CPs; i++ {

                                                if i != cp_no-1 { //All other CPs are misbehaving

                                                    m_cp = m_cp + strconv.Itoa(i+1)

                                                    if i != no_CPs-1 { //Add comma

                                                        m_cp = m_cp + ", "
                                                    }
                                                }
                                            }

                                            logrus.Error("CPs ", m_cp, " are misbehaving")
                                        }

                                        q_flag = true
                                        break
                                    }

                                } else {

                                    if isCPmisbehaving(cp_no, step_no-1, r_msg, no_CPs) == true { //Current CP is misbehaving

                                        logrus.Error("CP ", cp_no, " is misbehaving")
                                        q_flag = true
                                        break
                                    }

                                    ver_jpk[dp_no] = m_jpk //Store verified response
                                }

                                dp_resp_no[cp_no-1] = dp_resp_no[cp_no-1] + 1 //Increment no. of DP responses received
                                jpk_no = jpk_no + 1 //Increment the number of joint public key responses received from CPs so far

                                if jpk_no == no_CPs * no_DPs {

                                    logrus.Info("Step no. ", step_no-s_no, " average time ", step_avg.Sub(time.Time{}).String(),"/",no_DPs)

                                    //Compute joint public key
                                    proto.Unmarshal(m_jpk, cp_resp) //Unmarshalling

                                    //Convert bytes to public key
                                    tmp := bytes.NewReader(cp_resp.R[0])
                                    Y.UnmarshalFrom(tmp)

                                    theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_CPs) * (no_DPs) * (bSize+snoSize + sigSize + (((no_CPs-1)*sigSize) + pointSize)) ))) //For CP-DP communication

                                    theoryStepBytes.Add(theoryStepBytes, big.NewInt(int64( (no_CPs) * (no_DPs) * (bSize+snoSize + sigSize + (((no_CPs-1)*sigSize) + pointSize)) ))) //For receive implementation

                                    logrus.Info("Step no. ", step_no-s_no, " communication cost ", implStepBytes.String(), " bytes")

                                    //Increment step no.
                                    step_no = step_no + 1
                                }

                                step_end = time.Since(step_start) //Step end time
                                logrus.Info("Step no. ", step_no-s_no, " computing time ", step_end.String())

                                step_avg = step_avg.Add(step_end) //Step average time

                            } else {

                                logrus.Error("Dropping message. Expecting step no. ", step_no-s_no)
                                continue
                            }

                        } else { //If signature not verified

                            logrus.Error("Signature on joint public key by CP ", cp_no, " not verified")
                            q_flag = true
                            break
                        }

                    } else {

                        logrus.Error("Dropping message. ", com_name, " is not a CP.")
                        continue
                    }
                }

            } else {

                theoryStepBytes = big.NewInt(0) //Theoretical step communication cost
                implStepBytes = big.NewInt(0) //Implementation step communication cost

                c := make([][]kyber.Scalar, no_DPs) //Masked IP counters list for all DPs
                prf_len := 0 //Proof length to compute theoretical communication cost

                //Iterate over all DPs
                for i := 0; i < no_DPs; i++ {

                    if i == 0 {

                       step_avg = time.Time{} //Step average time
                    }

                    //ElGamal encrypted blinding values list
                    R := make([]kyber.Point, b)
                    C := make([]kyber.Point, b)

                    c[i] = make([]kyber.Scalar, b) //Initialice IP counters list

                    dp_resp := make([]DPres.Response, no_DPs) //DP Response
                    dp_resp[i].R = make([][]byte, b)
                    dp_resp[i].C = make([][]byte, b)
                    dp_resp[i].Proof = make([][]byte, b)
                    var tb bytes.Buffer

                    step_start = time.Now() //Step start time

                    //Iterate over all counters
                    for j := 0; j < b; j++ {

                        //Initialize counters to ElGamal encryption of random blinding values
                        tmp.Pick(pseudorand)
                        R[j] = suite.Point().Mul(tmp, nil)

                        //Convert to bytes
                        tb.Reset() //Buffer reset
                        _,_ = R[j].MarshalTo(&tb)
                        dp_resp[i].R[j] = make([]byte, len(tb.Bytes()))
                        copy(dp_resp[i].R[j][:], tb.Bytes()) //Convert to bytes

                        //Create proof
                        rep := proof.Rep("X", "x", "B")
                        secret := map[string]kyber.Scalar{"x": tmp}
                        public := map[string]kyber.Point{"B": suite.Point().Base(), "X": R[j]}
                        prover := rep.Prover(suite, secret, public, nil)
                        prf, _ := proof.HashProve(suite, strconv.Itoa(int(step_no))+strconv.Itoa(i)+strconv.Itoa(j), prover)
                        dp_resp[i].Proof[j] = make([]byte, len(prf))
                        copy(dp_resp[i].Proof[j][:], prf)

                        prf_len += len(prf)

                        //Initialize counters to ElGamal encryption of random blinding values
                        C[j] = suite.Point().Mul(tmp, Y)
                        tmp.Pick(pseudorand) //Random blinding value
                        C[j].Add(C[j], suite.Point().Mul(tmp, nil))

                        //Convert to bytes
                        tb.Reset() //Buffer reset
                        _,_ = C[j].MarshalTo(&tb)
                        dp_resp[i].C[j] = make([]byte, len(tb.Bytes()))
                        copy(dp_resp[i].C[j][:], tb.Bytes()) //Convert to bytes

                        //Initialize IP counters
                        c[i][j] = suite.Scalar().Zero()
                        c[i][j].Sub(c[i][j], tmp) //Negative of random blinding value
                    }

                    //Convert to bytes
                    dp_resp1, _ := proto.Marshal(&dp_resp[i])

                    step_end = time.Since(step_start) //Step end time
                    logrus.Info("Step no. ", step_no-s_no, " computing time ", step_end.String())

                    step_avg = step_avg.Add(step_end) //Step average time

                    implStepBytes.Add(implStepBytes, big.NewInt(int64( (no_CPs) * (bSize+snoSize + sigSize + len(dp_resp1[:])) ))) //For send encrypted blinding values implementation
                    theoryStepBytes.Add(theoryStepBytes, big.NewInt(int64( (no_CPs) * (bSize+snoSize + sigSize + ((2*b*pointSize) + prf_len)) ))) //For send encrypted blinding values theory

                    signSendDataToCP(step_no, dp_resp1, no_CPs, false) //Send encrypted blinding values to CP
                }

                logrus.Info("Step no. ", step_no-s_no, " average time ", step_avg.Sub(time.Time{}).String(),"/",no_DPs)
                theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_DPs) * (no_CPs) * (bSize+snoSize + sigSize + ((2*b*pointSize) + prf_len)) ))) //For send encrypted blinding values

                logrus.Info("Step no. ", step_no-s_no, " communication cost ", implStepBytes.String(), " bytes")

                //DP update oblivious counters
                for i := 0; i < no_DPs; i++ { //Iterate over all DPs

                    //Read IPs count from file
                    in, err := ioutil.ReadFile("unique_ip_count/original/dp" + strconv.Itoa(int(i)) + ".in")
                    checkError(err)
                    uniq_IP_List := &IPcount.UniqIP{}
                    err = proto.Unmarshal(in, uniq_IP_List)
                    checkError(err)

                    //Faster way to generate counts than reading from files
                    /*seed := rand.NewSource(time.Now().UnixNano())
                    rnd := rand.New(seed)

                    no_of_uniqIPs := rnd.Intn(1000 - 1) + 1
                    uniq_IP_List := new(IPcount.UniqIP)
                    uniq_IP_List.C = make([]int64, b)

                    for j := 0; j < no_of_uniqIPs; j++ {
                        seed := rand.NewSource(time.Now().UnixNano())
                        rnd := rand.New(seed)
                        uniq_IP_List.C[rnd.Int63n(int64(b))] = 1
                    }*/

                    //Iterate over all IP counters
                    for j := 0; j < b; j++ {

                        //If the IP is observed
                        if uniq_IP_List.C[j] == 1 {

                            uniqIPList[j] = 1 //Set to 1 to compute actual aggregate
                            c[i][j] = suite.Scalar().Pick(pseudorand) //Assign a random number
                        }
                    }
                }

                logrus.Info("Waiting for CP Dolev-Strong protocol...")
                time.Sleep(time.Duration(waitTime) * time.Minute)

                //Increment step no.
                step_no = step_no + 1

                theoryStepBytes = big.NewInt(0) //Theoretical step communication cost
                implStepBytes = big.NewInt(0) //Implementation step communication cost

                //Iterate over all DPs
                for i := 0; i < no_DPs; i++ {

                    if i == 0 {

                       step_avg = time.Time{} //Step average time
                    }

                    step_start = time.Now() //Step start time

                    dp_resp := make([]DPres.Response, no_DPs) //DP Response
                    dp_resp[i].R = make([][]byte, b)
                    var tb bytes.Buffer

                    //Iterate over all IP counters
                    for j := 0; j < b; j++ {

                        //Convert to bytes
                        tb.Reset() //Buffer reset
                        _,_ = c[i][j].MarshalTo(&tb)
                        dp_resp[i].R[j] = make([]byte, len(tb.Bytes()))
                        copy(dp_resp[i].R[j][:], tb.Bytes()) //Convert to bytes
                    }

                    //Convert to bytes
                    dp_resp1, _ := proto.Marshal(&dp_resp[i])

                    step_end = time.Since(step_start) //Step end time
                    logrus.Info("Step no. ", step_no-s_no, " computing time ", step_end.String())

                    step_avg = step_avg.Add(step_end) //Step average time

                    implStepBytes.Add(implStepBytes, big.NewInt(int64( (no_CPs) * (bSize+snoSize + sigSize + len(dp_resp1[:])) ))) //For send blinded IP count values implementation
                    theoryStepBytes.Add(theoryStepBytes, big.NewInt(int64( (no_CPs) * (bSize+snoSize + sigSize + (b*scalarSize)) ))) //For send blinded IP count values theory

                    signSendDataToCP(step_no, dp_resp1, no_CPs, true) //Send blinded IP count values to CP
                }

                f_flag = true //Set finish flag

                logrus.Info("Step no. ", step_no-s_no, " average time ", step_avg.Sub(time.Time{}).String(),"/",no_DPs)

                theoryBytes.Add(theoryBytes, big.NewInt(int64( (no_DPs) * (no_CPs) * (bSize+snoSize + sigSize + (b*scalarSize)) ))) //For send blinded IP count values

                logrus.Info("Step no. ", step_no-s_no, " communication cost ", implStepBytes.String(), " bytes")
            }
        } else {
            break
        }
    }

    if q_flag == true {

        logrus.Error("Aborting")

    } else if f_flag == true {

        //Compute unnoised aggregate
        for i := 0; i < b; i++ {

            if(uniqIPList[i] == 1) {
                agg += 1
            }
        }

        logrus.Info("Aggregate = ", agg)
        logrus.Info("Finishing")

        logrus.Info("DP send communication cost ", implSendBytes, " bytes")
        logrus.Info("DP receive communication cost ", implRecvBytes, " bytes")

        comCost := new(COMbytes.Bytes)
        comCost.T = make([]string, 1)
        comCost.R = make([]string, 1)
        comCost.S = make([]string, 1)
        comCost.T[0] = theoryBytes.String()
        comCost.R[0] = implRecvBytes.String()
        comCost.S[0] = implSendBytes.String()
        out, _ := proto.Marshal(comCost)
        ioutil.WriteFile(outputPath + "dp.bytes", out, 0644)
    }
    os.Exit(0)
}


//Output: Server socket
//Function: Creates server socket
func createServer() net.Listener {

    //Create TCP Listener
    listener, _ := net.Listen("tcp", dpIP + ":" + dpPort)

    return listener
}

//Input: Listener
//Output: Socket
//Function: Accept new connections in socket
func acceptConnections(listener net.Listener) *tls.Conn {
    //Load DP certificate and private key
    cert, err := tls.LoadX509KeyPair("certs/DP1.cert", "private/DP1.key")
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

//Input: Socket, Number of bytes
//Output: Message buffer
//Function: Read exactly n bytes from the socket
func socketReadN(conn net.Conn, n uint32) []byte {
    buf := make([]byte, n)
    _, err := io.ReadFull(conn,buf) //Read n Bytes
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

//Input: Source, Data
//Output: Bool (verified / not)
//Function: Verify source sign
func verifySign(src int, data []byte) (bool) {

    //Read public key from file
    in, _ := ioutil.ReadFile("schnorr/public/cp" + strconv.Itoa(src) + ".pub")
    buf := &Schnorrkey.Pub{}
    proto.Unmarshal(in, buf)

    y := bytes.NewReader(buf.Y) //Public key in bytes
    pub := suite.Point() //Public key
    pub.UnmarshalFrom(y)

    //Parse signed message
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

//Input: CP No., Step no., Data, No. of CPs
//Output: Bool (if current CP misbehaving or not)
//Function: Verify if CP is misbehaving
func isCPmisbehaving(cp_no int, step_no uint32, data []byte, no_CPs int) (bool) {

    cp_mflag := false //CP misbehaving flag (to be returned)

    //Parse data and compute hash
    h := sha256.New()
    h.Write(data[:len(data)-((no_CPs-1)*sigSize)]) //Message
    hdata := h.Sum(nil)

    //Iterate over all CPs
    for i := 1; i < no_CPs; i++ {

        var pubkey_fname string //Public key filename

        //CP public key filename (Current CP's sign is prepended)
        if i >= cp_no {

            pubkey_fname = strconv.Itoa(i+1) //CP public key filename

        } else {

            pubkey_fname = strconv.Itoa(i) //CP public key filename
        }

        //Read public key from file
        in, _ := ioutil.ReadFile("schnorr/public/cp" + pubkey_fname + ".pub")
        buf := &Schnorrkey.Pub{}
        proto.Unmarshal(in, buf)

        y := bytes.NewReader(buf.Y) //Public key in bytes
        pub := suite.Point() //Public key
        pub.UnmarshalFrom(y)

        //Parse signed message
        sign := data[len(data)-((no_CPs-i)*sigSize):len(data)-((no_CPs-i-1)*sigSize)] //Sign

        //Verify signed message
        err := schnorr.Verify(suite, pub, hdata, sign)

        if err != nil {

            cp_mflag = true
            break
        }
    }

    return cp_mflag
}

//Input: Step no., Data, No. of CPs, Reverse flag (To iterate over CPs in reverse order - a signal that all CPs have received inputs from all DPs)
//Function: Sign and send data to all CPs
func signSendDataToCP(step_no uint32, data []byte, no_CPs int, reverse bool) {

    //Read private key from file
    in, err := ioutil.ReadFile("schnorr/private/dp1.priv")
    checkError(err)
    priv := &Schnorrkey.Priv{}
    err = proto.Unmarshal(in, priv)
    checkError(err)

    //Convert bytes to private Key
    x := suite.Scalar().SetBytes(priv.X)

    //Add broadcast flag and step no. (//Since, for fallback phases, DPs are the broadcaster)
    b_s := make([]byte, bSize+snoSize)
    b_s[0] = byte(1) //Set broadcast flag
    binary.BigEndian.PutUint32(b_s[bSize:], step_no) //Set step no.
    data = append(b_s, data...) //Prepend broadcast flag and step no.

    //Compute hash
    h := sha256.New()
    h.Write(data)
    hdata := h.Sum(nil)

    if reverse { //If reverse flag set

        //Iterate over all CPs
        for j := no_CPs - 1; j >= 0; j-- {

            //Sign message
            sign, _ := schnorr.Sign(suite, x, hdata)
            sign = append(data, sign...) //Append data

            //Send to destination CP
            sendDataToCP(sign, j+1)
        }

    } else {

        //Iterate over all CPs
        for j := 0; j < no_CPs; j++ {

            //Sign message
            sign, _ := schnorr.Sign(suite, x, hdata)
            sign = append(data, sign...) //Append data

            //Send to destination CP
            sendDataToCP(sign, j+1)
        }
    }
}

//Input: Data, Destination CP
//Function: Send data to destination CP
func sendDataToCP(data []byte, dst int) {

    //Load private key and certificate
    cert, err := tls.LoadX509KeyPair("certs/DP1.cert", "private/DP1.key")
    checkError(err)

    //Dial TCP connection
    config := tls.Config{Certificates: []tls.Certificate{cert}, InsecureSkipVerify: true}
    con,err := net.Dial("tcp", cpIPs[dst-1] + ":" + cpPortPrefix + strconv.Itoa(dst))
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

//Input: Error
//Function: Check Error
func checkError(err error) {
    if err != nil {
        logrus.Error(os.Stderr, "Fatal error: %s", err.Error())
        os.Exit(1)
    }
}
