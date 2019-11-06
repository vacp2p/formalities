-------------------------------- MODULE MVDS --------------------------------

EXTENDS Integers, TLC

(* --algorithm mvds

variables messages = <<>>;

fair process OFFER = "OFFER"
    begin OFFER:
    while TRUE do
        await /\ messages = <<>>;
        messages := <<<<"msg">>>>
    end while;
end process

end algorithm; *)
\* BEGIN TRANSLATION
\* Label OFFER of process OFFER at line 11 col 5 changed to OFFER_
VARIABLE messages

vars == << messages >>

ProcSet == {"OFFER"}

Init == (* Global variables *)
        /\ messages = <<>>

OFFER == /\ /\ messages = <<>>
         /\ messages' = <<<<"msg">>>>

Next == OFFER

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(OFFER)

\* END TRANSLATION

=============================================================================
