------------------------------ MODULE recycler ------------------------------
EXTENDS Sequences, Integers, TLC, FiniteSets

(*
--algorithm recycler {

variables
    capacity = [trash |-> 10, recycle |-> 10],
    bins = [trash |-> {}, recycle |-> {}],
    count = [trash |-> 0, recycle |-> 0],
    items = <<
        [type |-> "recycle", size |-> 5],
        [type |-> "trash", size |-> 5],
        [type |-> "recycle", size |-> 4],
        [type |-> "recycle", size |-> 3]
    >>,
    curr = "";

macro add_item(type) {
    bins[type] := bins[type] \union {curr};
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
    
    assert capacity.trash >= 0 /\ capacity.recycle >= 0;
    assert Cardinality(bins.trash) = count.trash;
    assert Cardinality(bins.recycle) = count.recycle;
}

}*)
\* BEGIN TRANSLATION (chksum(pcal) = "8f98d9a4" /\ chksum(tla) = "411f77dd")
VARIABLES capacity, bins, count, items, curr, pc

vars == << capacity, bins, count, items, curr, pc >>

Init == (* Global variables *)
        /\ capacity = [trash |-> 10, recycle |-> 10]
        /\ bins = [trash |-> {}, recycle |-> {}]
        /\ count = [trash |-> 0, recycle |-> 0]
        /\ items =         <<
                       [type |-> "recycle", size |-> 5],
                       [type |-> "trash", size |-> 5],
                       [type |-> "recycle", size |-> 4],
                       [type |-> "recycle", size |-> 3]
                   >>
        /\ curr = ""
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF items /= <<>>
               THEN /\ curr' = Head(items)
                    /\ items' = Tail(items)
                    /\ IF curr'.type = "recycle" /\ curr'.size < capacity.recycle
                          THEN /\ bins' = [bins EXCEPT !["recycle"] = bins["recycle"] \union {curr'}]
                               /\ capacity' = [capacity EXCEPT !["recycle"] = capacity["recycle"] - curr'.size]
                               /\ count' = [count EXCEPT !["recycle"] = count["recycle"] + 1]
                          ELSE /\ IF curr'.size < capacity.trash
                                     THEN /\ bins' = [bins EXCEPT !["trash"] = bins["trash"] \union {curr'}]
                                          /\ capacity' = [capacity EXCEPT !["trash"] = capacity["trash"] - curr'.size]
                                          /\ count' = [count EXCEPT !["trash"] = count["trash"] + 1]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << capacity, bins, 
                                                          count >>
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(capacity.trash >= 0 /\ capacity.recycle >= 0, 
                              "Failure of assertion at line 37, column 5.")
                    /\ Assert(Cardinality(bins.trash) = count.trash, 
                              "Failure of assertion at line 38, column 5.")
                    /\ Assert(Cardinality(bins.recycle) = count.recycle, 
                              "Failure of assertion at line 39, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << capacity, bins, count, items, curr >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun Oct 24 22:58:24 JST 2021 by ryo
\* Created Sun Oct 24 22:18:07 JST 2021 by ryo
