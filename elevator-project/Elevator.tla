----------------------------- MODULE Elevator -----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANT NumFloors
ASSUME NumFloors \in 1..10

VARIABLES
    pos,
    pending,
    door_open

(* ================= VARIABLES TUPLE ================= *)
vars == <<pos, pending, door_open>>

(* ================= TYPE INVARIANT ================= *)
TypeOK ==
    /\ pos \in 1..NumFloors
    /\ pending \subseteq 1..NumFloors
    /\ door_open \in {TRUE, FALSE}

(* ================= INITIAL STATE ================= *)
Init ==
    /\ pos = 1
    /\ pending = {}
    /\ door_open = FALSE

(* ================= REQUEST ACTIONS ================= *)
CallFloor(floor) ==
    /\ floor \in 1..NumFloors
    /\ pending' = pending \cup {floor}
    /\ UNCHANGED <<pos, door_open>>

PressCabinButton(floor) ==
    /\ floor \in 1..NumFloors
    /\ pending' = pending \cup {floor}
    /\ UNCHANGED <<pos, door_open>>

EnvRequest ==
    \E floor \in 1..NumFloors:
        \/ CallFloor(floor)
        \/ PressCabinButton(floor)

(* ================= MOVEMENT ================= *)
MoveUp ==
    /\ ~door_open
    /\ pos < NumFloors
    /\ pos' = pos + 1
    /\ UNCHANGED <<pending, door_open>>

MoveDown ==
    /\ ~door_open
    /\ pos > 1
    /\ pos' = pos - 1
    /\ UNCHANGED <<pending, door_open>>

Move ==
    \/ MoveUp
    \/ MoveDown

(* ================= DOORS ================= *)
OpenDoors == 
    /\ ~door_open
    /\ pos \in pending
    /\ door_open' = TRUE
    /\ pending' = pending \ {pos}
    /\ UNCHANGED pos

CloseDoors ==
    /\ door_open
    /\ door_open' = FALSE
    /\ UNCHANGED <<pos, pending>>

(* ================= NEXT STATE ================= *)
Next ==
    \/ EnvRequest
    \/ Move
    \/ OpenDoors
    \/ CloseDoors

(* ================= FAIRNESS ================= *)
Fairness ==
    /\ WF_vars(Move)
    /\ WF_vars(OpenDoors)

(* ================= SPEC ================= *)
Spec == Init /\ [][Next]_vars /\ Fairness

(* ================= SAFETY ================= *)
Safety == TypeOK

(* ================= LIVENESS ================= *)
Liveness_EveryRequestServed == 
    \A floor \in 1..NumFloors:
        [](floor \in pending => <> (floor \notin pending))

=============================================================================
