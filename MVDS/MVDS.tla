------------------------------- MODULE MVDS ---------------------------------
(***************************************************************************)
(*        TLA+ specification of Minimally Viable Data Sychronization       *)
(*                     https://specs.vac.dev/mvds.html                     *)
(***************************************************************************)
EXTENDS Naturals, Sequences, TLC

Node == 1 .. 2 \* the nodes participating

VARIABLES state, \* the state of every node
          network \* the network with which nodes pass messages to each other

\* add retransmissions
\* retransmissions will require better usage of state

(***************************************************************************)
(* Messages used in MVDS                                                   *)
(***************************************************************************)
OFFER == "offer"
REQUEST == "request"
MSG == "msg"
ACK == "ack"

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
(* The type correctness predicate.                                         *)
(***************************************************************************)
TypeOK ==
  /\ network \in [Node -> [Node -> Seq(Message)]]
  /\ state \in [Node -> [Node -> STRING]]

(***************************************************************************)
(* The initial state predicate.                                            *)
(***************************************************************************)
Init ==
  /\ network = [s \in Node |-> [r \in Node |-> <<>> ]]
  /\ state = [s \in Node |-> [r \in Node |-> "" ]]

(***************************************************************************)
(* Node `n` sends an offer to `r`                                          *)
(***************************************************************************)
Offer(n, r) ==
  /\ state[n][r] = ""
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

=============================================================================
