----------------------------- MODULE telephone -----------------------------
EXTENDS Sequences, TLC

(*--algorithm telephone {
variables
    to_send = <<1, 2, 3>>,
    received = <<>>,
    in_transit = {};
{
    while (Len(received) # 3) {
        if (to_send # <<>>) {
            in_transit := in_transit \union {Head(to_send)};
            to_send := Tail(to_send);
        };
        
        either {
            with (msg \in in_transit) {
                received := Append(received, msg);
                in_transit := in_transit \ {msg};
            }
        } or {
            skip;
        }
    }
}

}*)
\* BEGIN TRANSLATION (chksum(pcal) = "3536c4a9" /\ chksum(tla) = "9e66b9c4")
VARIABLES to_send, received, in_transit, pc

vars == << to_send, received, in_transit, pc >>

Init == (* Global variables *)
        /\ to_send = <<1, 2, 3>>
        /\ received = <<>>
        /\ in_transit = {}
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(received) # 3
               THEN /\ IF to_send # <<>>
                          THEN /\ in_transit' = (in_transit \union {Head(to_send)})
                               /\ to_send' = Tail(to_send)
                          ELSE /\ TRUE
                               /\ UNCHANGED << to_send, in_transit >>
                    /\ \/ /\ pc' = "Lbl_2"
                       \/ /\ TRUE
                          /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << to_send, in_transit >>
         /\ UNCHANGED received

Lbl_2 == /\ pc = "Lbl_2"
         /\ \E msg \in in_transit:
              /\ received' = Append(received, msg)
              /\ in_transit' = in_transit \ {msg}
         /\ pc' = "Lbl_1"
         /\ UNCHANGED to_send

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun Jan 02 22:40:25 JST 2022 by ryo
\* Created Sun Jan 02 22:34:43 JST 2022 by ryo
