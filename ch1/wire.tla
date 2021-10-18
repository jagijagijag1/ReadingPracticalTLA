-------------------------------- MODULE wire --------------------------------
EXTENDS Integers

(*--algorithm wire

variables
    people = {"alice", "bob"},
    acc = [p \in people |-> 5], \* function (dict/map in general programming), use like acc["alice"]
    sender = "alice",
    receiver = "bob",
    amount = 3;

define
    NoOverdrafts == \A p \in people: acc[p] >= 0    \* def of operator
end define;

begin
Withdraw:
        acc[sender] := acc[sender] - amount;
    Deposite:
        acc[receiver] := acc[receiver] + amount;

end algorithm;*)

\* BEGIN TRANSLATION (chksum(pcal) = "510b4818" /\ chksum(tla) = "4680c904")
VARIABLES people, acc, sender, receiver, amount, pc

(* define statement *)
NoOverdrafts == \A p \in people: acc[p] >= 0


vars == << people, acc, sender, receiver, amount, pc >>

Init == (* Global variables *)
        /\ people = {"alice", "bob"}
        /\ acc = [p \in people |-> 5]
        /\ sender = "alice"
        /\ receiver = "bob"
        /\ amount = 3
        /\ pc = "Withdraw"

Withdraw == /\ pc = "Withdraw"
            /\ acc' = [acc EXCEPT ![sender] = acc[sender] - amount]
            /\ pc' = "Deposite"
            /\ UNCHANGED << people, sender, receiver, amount >>

Deposite == /\ pc = "Deposite"
            /\ acc' = [acc EXCEPT ![receiver] = acc[receiver] + amount]
            /\ pc' = "Done"
            /\ UNCHANGED << people, sender, receiver, amount >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Withdraw \/ Deposite
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Mon Oct 18 22:30:37 JST 2021 by ryo
\* Created Mon Oct 18 22:20:17 JST 2021 by ryo
