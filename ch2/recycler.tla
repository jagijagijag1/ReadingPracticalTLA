------------------------------ MODULE recycler ------------------------------
EXTENDS Sequences, Integers, TLC

BinTypes == {"trash", "recycle"}
SetsOfFour(set) == set \X set \X set \X set
Items == [type: BinTypes, size: 1..6]

(*
--algorithm recycler {

variables
    capacity \in [trash: 1..10, recycle: 1..10],
    bins = [trash |-> <<>>, recycle |-> <<>>],
    count = [trash |-> 0, recycle |-> 0],
    item \in SetsOfFour(Items),
    items \in item \X item \X item \X item,
    curr = "";

define {
    NoBinOverflow == capacity.trash >= 0 /\ capacity.recycle >= 0
    CountsMatchUp == Len(bins.trash) = count.trash /\ Len(bins.recycle) = count.recycle
};

macro add_item(type) {
    bins[type] := Append(bins[type], curr);
    capacity[type] := capacity[type] - curr.size;
    count[type] := count[type] + 1;    
};

{
    while (items /= <<>>) {
        curr := Head(items);
        items := Tail(items);
                
        if (curr.type = "recycle" /\ curr.size < capacity.recycle) {
            add_item("recycle")
        } else if (curr.size < capacity.trash) {
            add_item("trash")
        };
    };
    
    assert NoBinOverflow /\ CountsMatchUp;
}

}*)
\* BEGIN TRANSLATION (chksum(pcal) = "de6bff" /\ chksum(tla) = "dcdc2bdf")
VARIABLES capacity, bins, count, item, items, curr, pc

(* define statement *)
NoBinOverflow == capacity.trash >= 0 /\ capacity.recycle >= 0
CountsMatchUp == Len(bins.trash) = count.trash /\ Len(bins.recycle) = count.recycle


vars == << capacity, bins, count, item, items, curr, pc >>

Init == (* Global variables *)
        /\ capacity \in [trash: 1..10, recycle: 1..10]
        /\ bins = [trash |-> <<>>, recycle |-> <<>>]
        /\ count = [trash |-> 0, recycle |-> 0]
        /\ item \in SetsOfFour(Items)
        /\ items \in item \X item \X item \X item
        /\ curr = ""
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF items /= <<>>
               THEN /\ curr' = Head(items)
                    /\ items' = Tail(items)
                    /\ IF curr'.type = "recycle" /\ curr'.size < capacity.recycle
                          THEN /\ bins' = [bins EXCEPT !["recycle"] = Append(bins["recycle"], curr')]
                               /\ capacity' = [capacity EXCEPT !["recycle"] = capacity["recycle"] - curr'.size]
                               /\ count' = [count EXCEPT !["recycle"] = count["recycle"] + 1]
                          ELSE /\ IF curr'.size < capacity.trash
                                     THEN /\ bins' = [bins EXCEPT !["trash"] = Append(bins["trash"], curr')]
                                          /\ capacity' = [capacity EXCEPT !["trash"] = capacity["trash"] - curr'.size]
                                          /\ count' = [count EXCEPT !["trash"] = count["trash"] + 1]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << capacity, bins, 
                                                          count >>
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(NoBinOverflow /\ CountsMatchUp, 
                              "Failure of assertion at line 42, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << capacity, bins, count, items, curr >>
         /\ item' = item

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue Jan 04 23:52:11 JST 2022 by ryo
\* Created Sun Oct 24 22:18:07 JST 2021 by ryo
