#!/usr/bin/python3
n=7
for i in range(pow(2,n)):
    print(f'0{bin(i)[2:].zfill(n)}:1,0,0,0,1 1{bin(pow(2,n)-1-i)[2:].zfill(n)}:1,0,0,0,1 *:0,0,0,0,0')
    print(f'0{bin(i)[2:].zfill(n)}:1,0,0,0,1 1{bin(pow(2,n)-1-i)[2:].zfill(n)}:-1,0,0,0,1 *:0,0,0,0,0')