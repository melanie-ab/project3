-------------------------- MODULE Simple --------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS W, P, N

VARIABLES buffer, head, tail, count, jobsRemaining, jobsProcessed, initJobs

vars == <<buffer, head, tail, count, jobsRemaining, jobsProcessed, initJobs>>

TypeOK ==
    /\ buffer \in [1..N -> {"Empty", "Job"}]
    /\ head \in 1..N
    /\ tail \in 1..N
    /\ count \in 0..N
    /\ jobsRemaining \in [1..W -> 0..3]
    /\ jobsProcessed \in [1..P -> Nat]
    /\ initJobs \in [1..W -> 0..3]

Init ==
    /\ buffer = [i \in 1..N |-> "Empty"]
    /\ head = 1
    /\ tail = 1
    /\ count = 0
    /\ jobsRemaining \in [1..W -> 0..3]
    /\ initJobs = jobsRemaining
    /\ jobsProcessed = [p \in 1..P |-> 0]

RECURSIVE SumFunction(_, _)
SumFunction(f, i) ==
    IF i = 0 THEN 0
    ELSE f[i] + SumFunction(f, i - 1)

Produce(w) ==
    /\ w \in 1..W
    /\ jobsRemaining[w] > 0
    /\ count < N
    /\ buffer' = [buffer EXCEPT ![tail] = "Job"]
    /\ tail' = IF tail = N THEN 1 ELSE tail + 1
    /\ head' = head
    /\ count' = count + 1
    /\ jobsRemaining' = [jobsRemaining EXCEPT ![w] = @ - 1]
    /\ jobsProcessed' = jobsProcessed
    /\ initJobs' = initJobs

Consume(p) ==
    /\ p \in 1..P
    /\ count > 0
    /\ buffer[head] = "Job"
    /\ buffer' = [buffer EXCEPT ![head] = "Empty"]
    /\ head' = IF head = N THEN 1 ELSE head + 1
    /\ tail' = tail
    /\ count' = count - 1
    /\ jobsProcessed' = [jobsProcessed EXCEPT ![p] = @ + 1]
    /\ jobsRemaining' = jobsRemaining
    /\ initJobs' = initJobs

Next ==
    \/ \E w \in 1..W : Produce(w)
    \/ \E p \in 1..P : Consume(p)

Fairness ==
    /\ \A w \in 1..W : WF_vars(Produce(w))
    /\ \A p \in 1..P : WF_vars(Consume(p))

Spec ==
    Init /\ [][Next]_vars /\ Fairness

TotalJobs ==
    SumFunction(initJobs, W)

TotalProcessed ==
    SumFunction(jobsProcessed, P)

TotalRemaining ==
    SumFunction(jobsRemaining, W)

TotalSubmitted ==
    TotalJobs - TotalRemaining

NoLoss ==
    TotalSubmitted = TotalProcessed + count

BufferNeverOverflow ==
    count <= N

BufferNeverUnderflow ==
    count >= 0

Inv ==
    /\ TypeOK
    /\ BufferNeverOverflow
    /\ BufferNeverUnderflow
    /\ NoLoss

Termination ==
    <> ( /\ count = 0
         /\ \A w \in 1..W : jobsRemaining[w] = 0 )

Consistency ==
    <> (TotalProcessed = TotalJobs)

=============================================================================
