EXTENDS Integers, FiniteSets, TLC

CONSTANT NumFloors
ASSUME NumFloors \in 1..10

VARIABLES
    pos,
    pending,
    door_open

TypeOK ==
    /\ pos \in 1..NumFloors
    /\ pending\subseteq 1..NumFloors
    /\ door_open \in {TRUE, FALSE}

Init ==
    /\ pos = 1
    /\ pending = {}
    /\ door_open = FALSE

CallFloor(floor) ==
    /\ floor \in 1..NumFloors
    /\ pending' = pending \cup {floor}
    /\ UNCHANGED <<pos, door_open>>

PressCabinButton(floor) ==
    /\ floor \in 1..NumFloors
    /\ pending' = pending \cup {floor}
    /\ UNCHANGED <<pos, door_open>>

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
//need to fill out

OpenDoors == 
    /\ ~door_open
    /\ pos \in pending
    /\ door_open' = TRUE
    /\ UNCHANGED <<pos, pending>>

CloseDoors ==
    /\ door_open
    /\ pending' = pending \ {pos}
    /\ door_open' = FALSE
    /\ UNCHANGED pos

EnvRequest ==
//need to fill out

Next ==
    \/ EnvRequest
    \/ Move
    \/ OpenDoors
    \/ CloseDoors

Fairness ==
//need to fill out

Spec == Init /\ [][Next]_vars /\ Fairness

// Safety Properties

Safety_DoorsOpenOnlyAtFloor ==
    door_open => pos \in pending

Safety_DoorsSynchronized
    door_open => pos \in pending

Safety = Safety_DoorsOpenOnlyAtFloor

//Liveness Properties

Liveness_EveryRequestServed == 
    \A floor \in 1..NumFloors:
        (floor \in pending) ~> (floor \notin pending)

//Extra Credit

CallFloorRestricted(floor) == 
    /\ floor \ in 1..NumFloors \ RestrictedFloors
    /\ pending ' = pending \cup {floor}
    /\ UNCHANGED <<pos, door_open>>