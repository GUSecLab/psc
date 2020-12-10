package config

import ("math")

const WaitTime = 5 //Wait time to send commitments
const B = 500000 //No. of inputs
const NoDPs = 30 //No. of DPs
const NoCPs = 5 //No. of CPs
const Epsilon = 0.3 //Epsilon
var Delta = math.Pow(10, -12) //Delta
var DP_IP = "localhost" //DP IP address
var CP_IPs = [NoCPs]string{"localhost", "localhost", "localhost", "localhost", "localhost"} //CP IP addresses
var DP_Port = "7070" //Dp Port
var CP_PortPrefix = "606" //CP port prefix
var OutputPath = "../output/" //Output path
