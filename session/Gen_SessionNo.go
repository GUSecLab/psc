/*
Created on Apr 18, 2017
@author: Akshaya Mani, Georgetown University
*/

package main

import (
    "fmt"
    "github.com/golang/protobuf/proto"
    "io/ioutil"
    "math/rand"
    "psc/lib/sessionno"
    "time"
)

func main() {

    seed := rand.NewSource(time.Now().UnixNano())
    rnd := rand.New(seed)

    var s_no uint32 //Session No.
    s_no = uint32(0)
    for s_no == uint32(0) {
        s_no = uint32(rnd.Int31()) //Set Session No. to Non-Zero Random Number
    }

    sno := new(Sessionno.SNo)

    sno.S = &s_no
    out, err := proto.Marshal(sno)
    check(err)
    err = ioutil.WriteFile("session.no", out, 0644)
    check(err)
    fmt.Printf("%d \n", s_no)

    in, err := ioutil.ReadFile("session.no")
    check(err)
    sno1 := &Sessionno.SNo{}
    err = proto.Unmarshal(in, sno1)
    check(err)
    fmt.Printf("%d \n", *sno1.S)
}

//Check Error
func check(e error) {
    if e != nil {
        panic(e)
    }
}


