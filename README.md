# CP-Raft: _Concise and Generalized Design of Parallel Raft Protocol_
Authors: Haiwen Du, Dongjie Zhu, Yulan Zhou, and Zhaoshuo Tian
## Features

- A TLA+ verified consistency protocol that support out-of-order apply and out-of-order commit.
- Align the gap recovering and confirming with Raft voting process.
- Supports pre-vote mechanism to solve the availability problem when node rejoin the cluster.

## TLA+ Verification Methods

Please use [TLA+ toolbox](https://lamport.azurewebsites.net/tla/toolbox.html#installing) or [tla2tools.jar](https://tla.msr-inria.inria.fr/tlatoolbox/dist/tla2tools.jar) in command line to verify the tla+ code.


## Verification Results

### LEADER COMPLETENES (Pre-vote)

```
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 5.5E-5
  based on the actual fingerprints:  val = 4.2E-6
86541870 states generated, 13973698 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 38.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 9 and the 95th percentile is 3).
Finished in 07min 30s at (2022-07-02 00:01:32)
```

### LEADER COMPLETENES (Vote and Full-vote)
```
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 2.3E-11
50417 states generated, 10691 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 62.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 5 and the 95th percentile is 3).
Finished in 05s at (2022-07-02 00:15:16)
```
### 'GHOST LOGS' SECURITY (Replicating)
```
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 2.3E-11
61403 states generated, 7999 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 29.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 5 and the 95th percentile is 3).
Finished in 09s at (2022-07-31 17:20:52)
```

### 'GHOST LOGS' SECURITY (Pre-vote, Vote and Full-vote)
```
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 6.2E-11
32240914 states generated, 5462251 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 54.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 5 and the 95th percentile is 3).
Finished in 09s at (2022-07-31 17:55:34)
```
