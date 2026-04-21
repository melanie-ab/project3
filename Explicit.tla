-------------------------- MODULE Explicit --------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS W, P, N

VARIABLES buffer, head, tail, count,
          jobsRemaining, jobsProcessed, initJobs,
          pc

vars == <<buffer, head, tail, count,
          jobsRemaining, jobsProcessed, initJobs,
          pc>>

Producers == 1..W
Consumers == 1..P

(*****************************************************************)
(* Type correctness *)
(*****************************************************************)
TypeOK ==
    /\ buffer \in [1..N -> {"Empty", "Job"}]
    /\ head \in 1..N
    /\ tail \in 1..N
    /\ count \in 0..N
    /\ jobsRemaining \in [Producers -> 0..3]
    /\ jobsProcessed \in [Consumers -> Nat]
    /\ initJobs \in [Producers -> 0..3]
    /\ pc \in [Producers \cup Consumers -> {"start", "check", "write"}]

(*****************************************************************)
(* Initial state *)
(*****************************************************************)
Init ==
    /\ buffer = [i \in 1..N |-> "Empty"]
    /\ head = 1
    /\ tail = 1
    /\ count = 0
    /\ jobsRemaining \in [Producers -> 0..3]
    /\ initJobs = jobsRemaining
    /\ jobsProcessed = [p \in Consumers |-> 0]
    /\ pc = [i \in Producers \cup Consumers |-> "start"]

(*****************************************************************)
(* Producer steps *)
(*****************************************************************)
ProducerStep(w) ==
    /\ w \in Producers
    /\ pc[w] = "start"
    /\ pc' = [pc EXCEPT ![w] = "check"]
    /\ UNCHANGED <<buffer, head, tail, count,
                   jobsRemaining, jobsProcessed, initJobs>>

ProducerCheck(w) ==
    /\ w \in Producers
    /\ pc[w] = "check"
    /\ jobsRemaining[w] > 0
    /\ count < N
    /\ pc' = [pc EXCEPT ![w] = "write"]
    /\ UNCHANGED <<buffer, head, tail, count,
                   jobsRemaining, jobsProcessed, initJobs>>

(* FIXED: re-check conditions to avoid race conditions *)
ProducerWrite(w) ==
    /\ w \in Producers
    /\ pc[w] = "write"
    /\ jobsRemaining[w] > 0
    /\ count < N
    /\ buffer' = [buffer EXCEPT ![tail] = "Job"]
    /\ tail' = IF tail = N THEN 1 ELSE tail + 1
    /\ count' = count + 1
    /\ jobsRemaining' = [jobsRemaining EXCEPT ![w] = @ - 1]
    /\ pc' = [pc EXCEPT ![w] = "start"]
    /\ UNCHANGED <<head, jobsProcessed, initJobs>>

(*****************************************************************)
(* Consumer steps *)
(*****************************************************************)
ConsumerStep(p) ==
    /\ p \in Consumers
    /\ pc[p] = "start"
    /\ pc' = [pc EXCEPT ![p] = "check"]
    /\ UNCHANGED <<buffer, head, tail, count,
                   jobsRemaining, jobsProcessed, initJobs>>

ConsumerCheck(p) ==
    /\ p \in Consumers
    /\ pc[p] = "check"
    /\ count > 0
    /\ pc' = [pc EXCEPT ![p] = "write"]
    /\ UNCHANGED <<buffer, head, tail, count,
                   jobsRemaining, jobsProcessed, initJobs>>

(* FIXED: re-check condition to avoid race conditions *)
ConsumerWrite(p) ==
    /\ p \in Consumers
    /\ pc[p] = "write"
    /\ count > 0
    /\ buffer[head] = "Job"
    /\ buffer' = [buffer EXCEPT ![head] = "Empty"]
    /\ head' = IF head = N THEN 1 ELSE head + 1
    /\ count' = count - 1
    /\ jobsProcessed' = [jobsProcessed EXCEPT ![p] = @ + 1]
    /\ pc' = [pc EXCEPT ![p] = "start"]
    /\ UNCHANGED <<tail, jobsRemaining, initJobs>>

(*****************************************************************)
(* Next-state relation *)
(*****************************************************************)
Next ==
    \/ \E w \in Producers : ProducerStep(w)
    \/ \E w \in Producers : ProducerCheck(w)
    \/ \E w \in Producers : ProducerWrite(w)
    \/ \E p \in Consumers : ConsumerStep(p)
    \/ \E p \in Consumers : ConsumerCheck(p)
    \/ \E p \in Consumers : ConsumerWrite(p)

(*****************************************************************)
(* Specification *)
(*****************************************************************)
Spec ==
    Init /\ [][Next]_vars

=============================================================================
