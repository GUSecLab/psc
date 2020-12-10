sudo openssl req -newkey rsa:4096 -keyout CP$1.key -out CP$1.csr -config openssl.cnf -days 3650
openssl rsa -in CP$1.key -out CP$1.key.insecure
sudo mv CP$1.key.insecure CP$1.key
sudo openssl ca -in CP$1.csr -config openssl.cnf
sudo mv CP/certs/$2.pem CP/certs/CP$1.cert
sudo mv CP$1.csr CP/csr/
sudo mv CP$1.key CP/private/
