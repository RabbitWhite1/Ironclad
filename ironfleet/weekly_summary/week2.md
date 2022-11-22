#### Last Week

- Impl:
  - message parsing and marshaling
    - grammar
    - demarshal (bytearray -> datatype)
    - define marshallable (all kinds of sizes should be limited) and valid (semantically valid)
    - marshal (datatype -> bytearray)
  - NetRaft.i.dfy: 
    - marshal and send Raft Package
    - receive and demarshall to Raft Package
  - actions:
    - action0: general receiving, reading clock, and replying
      - if follower receives heartbeat, reset election timeout 
    - action1: general timeout checking
      - if leader: send heartbeat 
  - Program.cs: the driver for Raft Server

#### This Week Plan

- implement a simple KV storage service interface
- implement client request and reply
- add Client.cs
- implement `appendEntries` and `appendEntriesReply`

