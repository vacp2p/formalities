------------------------------- MODULE MVDS ---------------------------------
(***************************************************************************)
(*        TLA+ specification of Minimum Viable Data Synchronization        *)
(*                     https://specs.vac.dev/mvds.html                     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS N \* the set of all possible nodes

Node == 1 .. N \* the nodes participating

VARIABLES network, \* the network with which nodes pass messages to each other
          syncstate, \* the sync state for the node
          epoch \* the epochs for nodes

\* add retransmissions
\* retransmissions will require better usage of state

(***************************************************************************)
(* Messages used in MVDS                                                   *)
(***************************************************************************)
OFFER == "offer"
REQUEST == "request"
MSG == "msg"
ACK == "ack"

Type == {"-", OFFER, REQUEST, MSG, "done"}

OfferMessage(msg) == [type |-> OFFER, id |-> msg]
RequestMessage(msg) == [type |-> REQUEST, id |->  msg]
MsgMessage(msg) == [type |-> MSG, id |->  msg]
AckMessage(msg) == [type |-> ACK, id |->  msg]

Message ==
  {OfferMessage(msg) : msg \in Node} \union
  {RequestMessage(msg) : msg \in Node} \union
  {MsgMessage(msg) : msg \in Node} \union
  {AckMessage(msg) : msg \in Node}

(***************************************************************************)
(* Synchronization State used in MVDS                                      *)
(***************************************************************************)
SyncState == [type |-> Type, SendCount |-> Nat, SendEpoch |-> Nat]
InitialSyncState(t) == [type |-> t, SendCount |-> 0, SendEpoch |-> 0]
EmptySyncState == [type |-> "-", SendCount |-> 0, SendEpoch |-> 0]

(***************************************************************************)
(* The type correctness predicate.                                         *)
(***************************************************************************)
TypeOK ==
  /\ network \in [Node -> [Node -> Seq(Message)]]

(***************************************************************************)
(* The initial state predicate.                                            *)
(***************************************************************************)
Init ==
  /\ network = [s \in Node |-> [r \in Node |-> <<>> ]]
  /\ syncstate = [s \in Node |-> [r \in Node |-> EmptySyncState ]]
  /\ epoch = [s \in Node |-> 0]

(***************************************************************************)
(* Node `n` sends a message `m` to `r`.                                    *)
(* The message may either be dropped or transmitted                        *)
(***************************************************************************)
AppendMessage(n, r, m) ==
  /\ Append(network[n][r], m)
     \*\/ /\ TRUE
      \*  /\ UNCHANGED network

(***************************************************************************)
(* Node `n` adds offer sync state for `r`                                  *)
(***************************************************************************)
OfferV2(n, r) ==
  /\ syncstate[n][r].type = "-"
  /\ syncstate' = [syncstate EXCEPT ![n][r] = InitialSyncState(OFFER)]
  /\ UNCHANGED <<network, epoch>>

(***************************************************************************)
(* Node `n` receives an offer from `s` and adds request sync state for `s` *)
(***************************************************************************)
OnOfferV2(n, s) ==
  /\ network[s][n] # << >>
  /\ syncstate[n][s].type # REQUEST
  /\ LET m == Head(network[s][n])
     IN /\ m.type = OFFER
        /\ network' = [network EXCEPT ![s][n] = Tail(@)]
        /\ syncstate' = [syncstate EXCEPT ![n][s] = InitialSyncState(REQUEST)]
  /\ UNCHANGED <<epoch>>

(***************************************************************************)
(* Node `n` receives a request from `s`                                    *)
(* and adds message sync state for `s`                                     *)
(***************************************************************************)
OnRequestV2(n, s) ==
  /\ network[s][n] # << >>
  /\ LET m == Head(network[s][n])
     IN /\ m.type = REQUEST
        /\ network' = [network EXCEPT ![s][n] = Tail(@)]
        /\ syncstate' = [syncstate EXCEPT ![n][s] = InitialSyncState(MSG)]
  /\ UNCHANGED <<epoch>>

(***************************************************************************)
(* Node `n` receives a message from `s` and sends an ack to `s`            *)
(***************************************************************************)
OnMessageV2(n, s) ==
  /\ network[s][n] # << >>
    /\ LET m == Head(network[s][n])
       IN /\ m.type = MSG
          /\ network' = [network EXCEPT ![s][n] = Tail(@), ![n][s] = Append(@, AckMessage(m.id))]
  /\ UNCHANGED <<epoch, syncstate>>

(***************************************************************************)
(* Node `n` receives an ack from `s`                                       *)
(***************************************************************************)
OnAckV2(n, s) ==
  /\ network[s][n] # << >>
    /\ LET m == Head(network[s][n])
       IN /\ m.type = ACK
          /\ network' = [network EXCEPT ![s][n] = Tail(@)]
          /\ syncstate' = [syncstate EXCEPT ![n][s] = InitialSyncState("done")]
  /\ UNCHANGED <<epoch>>

(***************************************************************************)
(* Node `n` sends all sync messages to `r`                                 *)
(***************************************************************************)
Send(n, r) ==
  /\ syncstate[n][r].type # "-"
  /\ syncstate[n][r].type # "done"
  \* /\ syncstate[n][r].SendEpoch <= epoch[n]
  /\ syncstate' = [syncstate EXCEPT ![n][r] = [type |-> @.type, SendCount |-> @.SendCount + 1, SendEpoch |-> @.SendEpoch + 1]]
  /\ LET msg == syncstate[n][r]
     IN CASE msg.type = OFFER -> network' = [network EXCEPT ![n][r] = Append(@, OfferMessage(n))]
          [] msg.type = REQUEST -> network' = [network EXCEPT ![n][r] = Append(@, RequestMessage(n))]
          [] msg.type = MSG -> network' = [network EXCEPT ![n][r] = Append(@, MsgMessage(n))]
  /\ UNCHANGED <<epoch>>

(***************************************************************************)
(* Node `n` transitions to next epoch                                      *)
(***************************************************************************)
NextEpoch(n) ==
    /\ epoch' = [epoch EXCEPT ![n] = @ + 1]
    /\ UNCHANGED <<syncstate, network>>

(***************************************************************************)
(* Next-state relation.                                                    *)
(***************************************************************************)
Next ==
  \/ \E n \in Node : \E s \in Node \ {n} : OfferV2(n, s)
  \/ \E n \in Node : \E s \in Node \ {n} :
        OnOfferV2(n, s) \/ OnRequestV2(n, s) \/ OnMessageV2(n, s) \/ OnAckV2(n, s) \/ Send(n, s)

vars == <<network, epoch, syncstate>>

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

(***************************************************************************)
(* A state constraint useful for validating the specification,             *)
(* asserts that all messages are delivered.                                *)
(***************************************************************************)
AllMessagesDelivered == syncstate[2][1].type # "done"

=============================================================================
