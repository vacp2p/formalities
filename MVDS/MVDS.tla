------------------------------- MODULE MVDS ---------------------------------
(***************************************************************************)
(*        TLA+ specification of Minimum Viable Data Synchronization        *)
(*                     https://specs.vac.dev/mvds.html                     *)
(***************************************************************************)
EXTENDS Naturals, Sequences, TLC

CONSTANTS N \* the set of all possible nodes

Node == 1 .. N \* the nodes participating

VARIABLES state, \* the state of every node
          network, \* the network with which nodes pass messages to each other
          syncstate, \* the sync state for the node
          epoch \* the epochs for nodes

\* add retransmissions
\* retransmissions will require better usage of state

State == { "-", "offered", "delivered" }

(***************************************************************************)
(* Messages used in MVDS                                                   *)
(***************************************************************************)
OFFER == "offer"
REQUEST == "request"
MSG == "msg"
ACK == "ack"

Type == {"-", OFFER, REQUEST, MSG}

OfferMessage(msg) == [type |-> OFFER, id |-> msg]
RequestMessage(msg) == [type |-> REQUEST, id |-> msg]
MsgMessage(msg) == [type |-> MSG, id |-> msg]
AckMessage(msg) == [type |-> ACK, id |-> msg]

Message ==
  {OfferMessage(msg) : msg \in Node} \union
  {RequestMessage(msg) : msg \in Node} \union
  {MsgMessage(msg) : msg \in Node} \union
  {AckMessage(msg) : msg \in Node}

(***************************************************************************)
(* Synchronization State used in MVDS                                      *)
(***************************************************************************)
SyncState == [type: Type, SendCount: Nat, SendEpoch: Nat]
InitialSyncState(t) == [type |-> t, SendCount |-> 0, SendEpoch |-> 0]

(***************************************************************************)
(* The type correctness predicate.                                         *)
(***************************************************************************)
TypeOK ==
  /\ network \in [Node -> [Node -> Seq(Message)]]
  /\ state \in [Node -> [Node -> State]]
  /\ syncstate \in [Node -> [Node ->  [N -> SyncState]]]

(***************************************************************************)
(* The initial state predicate.                                            *)
(***************************************************************************)
Init ==
  /\ network = [s \in Node |-> [r \in Node |-> <<>> ]]
  /\ state = [s \in Node |-> [r \in Node |-> "-" ]]
  /\ syncstate = [s \in Node |-> [r \in Node |-> [i \in N |-> InitialSyncState("-") ]]]

(***************************************************************************)
(* Node `n` sends a message `m` to `r`.                                    *)
(* The message may either be dropped or transmitted                        *)
(***************************************************************************)
AppendMessage(n, r, m) ==
  /\ \/ /\ network' = [network EXCEPT ![n][r] = Append(@, m)]
     \/ /\ TRUE
        /\ UNCHANGED network

(***************************************************************************)
(* Node `n` adds offer sync state for `r`                                  *)
(***************************************************************************)
OfferV2(n, r) ==
    /\ syncstate[n][r][n].type = "-"
    /\ syncstate' = [syncstate EXCEPT ![n][r][n] = InitialSyncState(OFFER)]
    /\ UNCHANGED <<network, epoch>>

(***************************************************************************)
(* Node `n` receives an offer from `r` and adds request sync state for `r` *)
(***************************************************************************)
OnOfferV2(n, r) ==
    /\ syncstate[n][r][n].type = ""
    /\ syncstate' = [syncstate EXCEPT ![n][r][n] = InitialSyncState(REQUEST)]
    /\ UNCHANGED <<network, epoch>>

(***************************************************************************)
(* Node `n` receives a request from `r`                                    *)
(* and adds message sync state for `r`                                     *)
(***************************************************************************)
OnRequestV2(n, r) ==
    /\ syncstate[n][r][n].type = ""
    /\ syncstate' = [syncstate EXCEPT ![n][r][n] = InitialSyncState(MSG)]
    /\ UNCHANGED <<network, epoch>>

(***************************************************************************)
(* Node `n` sends an offer to `r`                                          *)
(***************************************************************************)
Offer(n, r) == \* @TODO this should only append to the sync state, there is then a send function that sends everything in state
  /\ state[n][r] = "-"
  /\ network' = [network EXCEPT ![n][r] = Append(@, OfferMessage(n))]
  /\ state' = [state EXCEPT ![n][r] = "offered"]

(***************************************************************************)
(* Node `n` receives an offer from `s`                                     *)
(***************************************************************************)
ReceiveOffer(n, s) ==
  /\ network[s][n] # << >>
  /\ LET m == Head(network[s][n])
     IN /\ m.type = OFFER
        /\ network' = [network EXCEPT ![s][n] = Tail(@),
                                      ![n][s] = Append(@, RequestMessage(s))]
        /\ UNCHANGED state

(***************************************************************************)
(* Node `n` receives a request from `s`                                    *)
(***************************************************************************)
ReceiveRequest(n, s) ==
  /\ network[s][n] # << >>
  /\ LET m == Head(network[s][n])
     IN /\ m.type = REQUEST
        /\ network' = [network EXCEPT ![s][n] = Tail(@),
                                      ![n][s] = Append(@, MsgMessage(n))]
        /\ UNCHANGED state

(***************************************************************************)
(* Node `n` receives a message from `s`                                    *)
(***************************************************************************)
ReceiveMessage(n, s) ==
  /\ network[s][n] # << >>
  /\ LET m == Head(network[s][n])
     IN /\ m.type = MSG
        /\ network' = [network EXCEPT ![s][n] = Tail(@),
                                      ![n][s] = Append(@, AckMessage(s))]
        /\ UNCHANGED state

(***************************************************************************)
(* Node `n` receives a ack from `s`                                        *)
(***************************************************************************)
ReceiveAck(n, s) ==
  /\ network[s][n] # << >>
  /\ LET m == Head(network[s][n])
     IN /\ m.type = ACK
        /\ network' = [network EXCEPT ![s][n] = Tail(@)]
        /\ state' = [state EXCEPT ![s][n] = "delivered"]

(***************************************************************************)
(* Next-state relation.                                                    *)
(***************************************************************************)
Next ==
  \/ \E n \in Node : \E s \in Node \ {n} :
    Offer(n, s) \/ ReceiveOffer(n, s) \/ ReceiveRequest(n, s) \/
    ReceiveMessage(n, s) \/ ReceiveAck(n, s)

vars == <<network, state>>

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

(***************************************************************************)
(* A state constraint useful for validating the specification,             *)
(* asserts that all messages are delivered.                                *)
(***************************************************************************)
AllMessagesDelivered ==
  /\ \A n \in Node : \A s \in Node \ {n} : state[n][s] # "delivered"

=============================================================================
