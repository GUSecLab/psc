/*
Created on Apr 18, 2017
@author: Akshaya Mani, Georgetown University
*/

package main

import (
    "bytes"
    "fmt"
    "go.dedis.ch/kyber/v3/group/edwards25519"
    "github.com/golang/protobuf/proto"
    "io/ioutil"
    "psc/lib/schnorrkey"
    "strconv"
)

func main() {

    for i := 0; i < 10; i++ {

        suite := edwards25519.NewBlakeSHA256Ed25519()
        rand := suite.RandomStream()

        x := suite.Scalar().Pick(rand)
	y := suite.Point().Mul(x, nil)

        priv := new(Schnorrkey.Priv)
        pub := new(Schnorrkey.Pub)

        //Convert to private key to bytes
        var tb bytes.Buffer //Temporary buffer
        _,_ = x.MarshalTo(&tb)
        priv.X = tb.Bytes()

        out, err := proto.Marshal(priv)
        check(err)
        err = ioutil.WriteFile("private/cp" + strconv.Itoa(i + 1) + ".priv", out, 0644)
        check(err)
        fmt.Printf("%q \n",x.String())

        tb.Reset()
        _,_ = y.MarshalTo(&tb)
        pub.Y = tb.Bytes()

        out, err = proto.Marshal(pub)
        check(err)
        err = ioutil.WriteFile("public/cp" + strconv.Itoa(i + 1) + ".pub", out, 0644)
        check(err)
        fmt.Printf("%q \n",y.String())

        in, err := ioutil.ReadFile("private/cp" + strconv.Itoa(i + 1) + ".priv")
        check(err)
        priv1 := &Schnorrkey.Priv{}
        err = proto.Unmarshal(in, priv1)
        check(err)
        x1 := suite.Scalar().SetBytes(priv1.X)
        fmt.Printf("%q \n",x1.String())

        in, err = ioutil.ReadFile("public/cp" + strconv.Itoa(i + 1) + ".pub")
        check(err)
        pub1 := &Schnorrkey.Pub{}
        err = proto.Unmarshal(in, pub1)
        check(err)
        y1 := bytes.NewReader(pub1.Y)
        y2 := suite.Point()
        y2.UnmarshalFrom(y1)
        fmt.Printf("%q \n",y2.String())
    }
}

//Check Error
func check(e error) {
    if e != nil {
        panic(e)
    }
}
