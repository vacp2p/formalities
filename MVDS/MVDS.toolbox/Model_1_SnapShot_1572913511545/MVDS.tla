-------------------------------- MODULE MVDS --------------------------------

EXTENDS Sequences, Naturals, Integers, TLC

(* --algorithm mvds

variables messages = <<>>,
          message_index = 0;

macro send(input, m) begin    
    either
        m := Append(m, input);
    or
        skip;
    end either;
end macro 


fair process OFFER = "OFFER"
    begin OFFER:
    while TRUE do
        await /\ messages = <<>>;
        send(<<"OFFER", message_index>>, messages);
    end while;
end process

fair process OnOffer = "OnOffer"
    begin OnOffer:
    while TRUE do
        await /\ messages # <<>>;
        if Head(messages)[1] = "OFFER" then 
                messages := <<<<"REQUEST", message_index>>>>
        end if;
    end while;
end process

fair process OnRequest = "OnRequest"
    begin OnRequest:
    while TRUE do
        await /\ messages # <<>>;
        if Head(messages)[1] = "REQUEST" then 
                messages := <<<<"MESSAGE", message_index>>>>
        end if;
    end while;
end process

end algorithm; *)
\* BEGIN TRANSLATION
\* Label OFFER of process OFFER at line 21 col 5 changed to OFFER_
\* Label OnOffer of process OnOffer at line 29 col 5 changed to OnOffer_
\* Label OnRequest of process OnRequest at line 39 col 5 changed to OnRequest_
VARIABLES messages, message_index

vars == << messages, message_index >>

ProcSet == {"OFFER"} \cup {"OnOffer"} \cup {"OnRequest"}

Init == (* Global variables *)
        /\ messages = <<>>
        /\ message_index = 0

OFFER == /\ /\ messages = <<>>
         /\ \/ /\ messages' = Append(messages, (<<"OFFER", message_index>>))
            \/ /\ TRUE
               /\ UNCHANGED messages
         /\ UNCHANGED message_index

OnOffer == /\ /\ messages # <<>>
           /\ IF Head(messages)[1] = "OFFER"
                 THEN /\ messages' = <<<<"REQUEST", message_index>>>>
                 ELSE /\ TRUE
                      /\ UNCHANGED messages
           /\ UNCHANGED message_index

OnRequest == /\ /\ messages # <<>>
             /\ IF Head(messages)[1] = "REQUEST"
                   THEN /\ messages' = <<<<"MESSAGE", message_index>>>>
                   ELSE /\ TRUE
                        /\ UNCHANGED messages
             /\ UNCHANGED message_index

Next == OFFER \/ OnOffer \/ OnRequest

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(OFFER)
        /\ WF_vars(OnOffer)
        /\ WF_vars(OnRequest)

\* END TRANSLATION

=============================================================================
