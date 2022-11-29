#### Last Week

- Complete the election part; And now we can run a Raft cluster.

#### This Week Plan

- Complete the `protocol` part
  - The difference between protocol and implementation
    - Protocol doesn't contains send/recv details; only need to specify sent/received packets (without marshalling/demarshalling)
    - Protocol only need to specify the `predicate`s that each actions should hold (including `requires` and `predicate` itself)
- Prove refinement from `implementation` to `protocol` (shall be easier because they are basically one-to-one corresponding)
- Prove refinement from `protocol` to `service`

#### Problems

- For `protocol` -> `service`, where to start?