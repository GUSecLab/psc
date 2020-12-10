## Accountable Private Set-Union Cardinality

# Description

This project, a collaborative effort between researchers at Georgetown University, U.S. Naval Academy, and the U.S. Naval Research Lab, is an extension of the Private Set-Union Cardinality (PSC) project. PSC is a cryptographic protocol used to privately measure the number of events that are collectively observed by a large distributed set of data collectors during an observation period.

PSC allows for secure and useful statistics gathering in privacy-preserving distributed systems such as anonymity networks; for example, it allows operators of anonymity networks such as Tor to securely answer the questions: How many unique users are using the network? and How many unique hidden services are being accessed?

While PSC is suitable for many applications, it does not provide fairness or accountability, and any Computation Party (CP) (a server that aggregates the observation) can cause the protocol to abort without blame or attribution. Moreover, malicious CPs can anonymously add any event to the aggregate at any point in time.

This accountable extension of the PSC protocol ensures that these anonymous attacks by the CPs are no longer possible. Additionally, this version of the protocol combines previously separate phases for added performance improvements.

# Paper

For more information about accountable PSC, refer:

```
  Accountable Private Set Cardinality for Distributed Measurement (in submission)
  Ellis Fenske, Akshaya Mani, Aaron Johnson, and Micah Sherr
```

# Installation

A PSC network consists at least two Computation Parties (CPs) and one or more Data Parties (DPs). 

### Install virtual environment

    git clone https://github.com/ekalinin/envirius.git
    cd envirius
    make install

Add following to your ~/.bashrc:

    [ -f "$HOME/.envirius/nv" ] && . ~/.envirius/nv

Restart your terminal.

### Check available versions of go

    nv ls-versions --go-prebuilt

### Create an environment <goenvironment_name> with go 1.14 or later

    nv mk <goenvironment_name> --go-prebuilt=1.14.9

### Activate environment

    nv on <goenvironment_name>

### Set Go environment variable

    export GOPATH=~/.envirius/envs/<goenvironment_name>

### Download PSC

    cd $GOPATH
    mkdir src && cd src
    git clone git@github.com:GUSecLab/psc.git

### Install PSC dependancies

    cd psc
    go mod init
    go get -u ./...

### Upgrade PSC

    cd $GOPATH/src/psc
    git pull

### Deactivate environment

    nv off
