## IronRaft - Key-Value Store

```
dotnet bin/CreateIronServiceCerts.dll outputdir=certs name=MyKV type=IronRaftKV addr1=127.0.0.1 port1=4001 addr2=127.0.0.1 port2=4002 addr3=127.0.0.1 port3=4003
```

Then, run each of the following three server commands, each in a different window:
```
dotnet bin/IronRaftKVServer.dll certs/MyKV.IronRaftKV.service.txt certs/MyKV.IronRaftKV.server1.private.txt safeguard=false
dotnet bin/IronRaftKVServer.dll certs/MyKV.IronRaftKV.service.txt certs/MyKV.IronRaftKV.server2.private.txt safeguard=false
dotnet bin/IronRaftKVServer.dll certs/MyKV.IronRaftKV.service.txt certs/MyKV.IronRaftKV.server3.private.txt safeguard=false
```

Finally, run this client command in yet another window:
```
dotnet bin/IronRaftKVClient.dll certs/MyKV.IronRaftKV.service.txt nthreads=10 duration=30 setfraction=0.25 deletefraction=0.05 print=true
```
