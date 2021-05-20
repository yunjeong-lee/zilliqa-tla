------------------------------ MODULE TCommit ------------------------------
(***************************************************************************)
(* This specification is explained in "Transaction Commit", Lecture 5 of   *)
(* the TLA+ Course (http://lamport.azurewebsites.net/video/videos.html).   *)
(***************************************************************************)
CONSTANT RM       \* The set of participating resource managers

VARIABLE rmState  \* rmState[r] is the state of resource manager r.
-----------------------------------------------------------------------------
TCTypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
    \* This is an array, indexed over elements of the set RM
    \* In general, arrays are defined as comprehensions
        
TCInit ==   rmState = [r \in RM |-> "working"]
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (* [r \in RM |-> "working"] refers to the array with index set RM s.t.   *)
  (* the array applied to rm ([r \in RM |-> "working"][rm]) equals to      *)
  (* "working" for all rm in RM.                                           *)
  (*************************************************************************)

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}
  (*************************************************************************)
  (* True iff all RMs are in the "prepared" or "committed" state.          *)
  (*************************************************************************)

notCommitted == \A r \in RM : rmState[r] # "committed" 
  (*************************************************************************)
  (* True iff no resource manager has decided to commit.                   *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the RMs, and then    *)
(* define the complete next-state action of the specification to be the    *)
(* disjunction of the possible RM actions.                                 *)
(***************************************************************************)
Prepare(r) == /\ rmState[r] = "working"
              /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Decide(r)  == \/ /\ rmState[r] = "prepared"
                 /\ canCommit
                 /\ rmState' = [rmState EXCEPT ![r] = "committed"]
              \/ /\ rmState[r] \in {"working", "prepared"}
                 /\ notCommitted
                 /\ rmState' = [rmState EXCEPT ![r] = "aborted"]


TCNext == \E r \in RM : Prepare(r) \/ Decide(r)
  (*************************************************************************)
  (* The next-state action.                                                *)
  (*************************************************************************)
-----------------------------------------------------------------------------
TCConsistent ==  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.  It is an invariant of the specification.      *)
  (*************************************************************************)
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following part  will be explained later                             *)
(***************************************************************************)
TCSpec == TCInit /\ [][TCNext]_rmState
\* The subscript enumerates essential variables (remember Forward simulations)
\* In other words, anyone who refines this spec is allowed the "stuttering"
\* steps that don't modify rmState
\* [TCNext]_rmState is a shortcut for TCNext \/ (UNCHANGED rmState)
  (*************************************************************************)
  (* The complete specification of the protocol written as a temporal      *)
  (* formula.                                                              *)
  (*************************************************************************)

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
  (*************************************************************************)
  (* This theorem asserts the truth of the temporal formula whose meaning  *)
  (* is that the state predicate TCTypeOK /\ TCInvariant is an invariant   *)
  (* of the specification TCSpec.  Invariance of this conjunction is       *)
  (* equivalent to invariance of both of the formulas TCTypeOK and         *)
  (* TCConsistent.                                                         *)
  (*************************************************************************)

=============================================================================