--------------------------- MODULE BFTConsensus ---------------------------
EXTENDS TLC, Integers, FiniteSets

(***************************************************************************)
(* This specification is built upon the "Two-Phase Commit" of the TLA+     *)
(* Video Course. The leader coordinates backups, while the backups sponta- *)
(* neously issue Prepared messages. As in the case with TLA+ Video Course, *)
(* we ignore the Prepare messages that the leader can send to the backups. *)
(*                                                                         *)
(* For simplicity, we also eliminate Abort messages sent by a backup when  *)
(* it decides to abort. Such a message would cause the leader to abort the *)
(* transaction, an event represented here by leader spontaneously deciding *)
(* to abort.                                                               *)
(***************************************************************************)
CONSTANT Backup  \* The set of backup nodes

VARIABLES
  backupState,    \* buState[r] is the state of backup node n.
  leaderState,    \* The state of the leader node.
  leaderPrepared, \* The set of backups from which the leader has received
                  \* "Prepared" messages.
  msgs            \* The set of all messages that have ben sent, ie, message soup
    (***********************************************************************)
    (* A message is sent by adding it to the set msgs. For simplicity,     *) 
    (* messages are never removed from msgs. It allows receipt of same msg *)
    (* twice (or more) is allowed, but not a problem in this protocol.     *)
    (***********************************************************************)

Messages ==
  (*************************************************************************)
  (* The set of all possible messages.  Messages of type "Prepared" are    *)
  (* sent from the backups indicated by the message's backupNode field.    *)
  (* Messages of type "Commit" and "Abort" are broadcast by the leader, to *)
  (* be received by all backups. The set msgs contains just a single copy  *)
  (* of such a message.                                                    *)
  (*************************************************************************)
  [type : {"Prepared"}, backupNode : Backup]  \cup  [type : {"Commit", "Abort"}]
   
BFTTypeOK ==  
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ backupState \in [Backup -> {"working", "prepared", "committed", "aborted"}]
  /\ leaderState \in {"init", "done"}
  /\ leaderPrepared \subseteq Backup
  /\ msgs \subseteq Messages

BFTInit ==   
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ backupState = [r \in Backup |-> "working"]
  /\ leaderState = "init"
  /\ leaderPrepared   = {}
  /\ msgs = {}
-----------------------------------------------------------------------------

(***************************************************************************)
(*                                Actions                                  *)
(***************************************************************************)

LeaderRcvPrepared(n) ==
  (*************************************************************************)
  (* The leader receives a "Prepared" message from backup node n.          *)
  (*************************************************************************)
  /\ leaderState = "init" \* Enabling condition
  /\ [type |-> "Prepared", backup |-> n] \in msgs \* Another enabling condition
  /\ leaderPrepared' = leaderPrepared \cup {n}
  /\ UNCHANGED <<backupState, leaderState, msgs>> \* The values in the new state are the same

LeaderCommit ==
  (*************************************************************************)
  (* The leader commits the transaction; enabled iff the leader is in its  *)
  (* initial state and every backup has sent a "Prepared" message.         *)
  (*************************************************************************)
  /\ leaderState = "init"
  /\ Cardinality(leaderPrepared) > Cardinality(Backup) \div 2 \* a majority is prepared
  /\ leaderState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<backupState, leaderPrepared>>

LeaderAbort ==
  (*************************************************************************)
  (* The leader spontaneously aborts the transaction.                      *)
  (*************************************************************************)
  /\ leaderState = "init"
  /\ leaderState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<backupState, leaderPrepared>>

BackupPrepare(n) == 
  (*************************************************************************)
  (* Backup n prepares.                                                    *)
  (*************************************************************************)
  /\ backupState[n] = "working"
  /\ backupState' = [backupState EXCEPT ![n] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", backupNode |-> n]}
  /\ UNCHANGED <<leaderState, leaderPrepared>>
  
BackupChooseToAbort(n) ==
  (*************************************************************************)
  (* Resource manager r spontaneously decides to abort.  As noted above, r *)
  (* does not send any message in our simplified spec.                     *)
  (*************************************************************************)
  /\ backupState[n] = "working"
  /\ backupState' = [backupState EXCEPT ![n] = "aborted"]
  /\ UNCHANGED <<leaderState, leaderPrepared, msgs>>
  (* note : in practice, backup would inform leader that it has aborted so *)
  (* leader knows it should abort the transaction. But that optimization   *) 
  (* isn't relevant for implementing this BFT consensus here               *)
  (* (me) Q is when would backup ever decide to abort? why would it abort? *)

BackupRcvCommitMsg(n) ==
  (*************************************************************************)
  (* Backup node n is told by the leader to commit.                        *)
  (*************************************************************************)
  /\ [type |-> "Commit"] \in msgs
  /\ backupState' = [backupState EXCEPT ![n] = "committed"]
  /\ UNCHANGED <<leaderState, leaderPrepared, msgs>>

BackupRcvAbortMsg(n) ==
  (*************************************************************************)
  (* Backup node n is told by the leader to abort.                         *)
  (*************************************************************************)
  /\ [type |-> "Abort"] \in msgs
  /\ backupState' = [backupState EXCEPT ![n] = "aborted"]
  /\ UNCHANGED <<leaderState, leaderPrepared, msgs>>

BFTNext ==
  \/ LeaderCommit \/ LeaderAbort
  \/ \E r \in Backup : 
       LeaderRcvPrepared(r) \/ BackupPrepare(r) \/ BackupChooseToAbort(r)
         \/ BackupRcvCommitMsg(r) \/ BackupRcvAbortMsg(r)
-----------------------------------------------------------------------------

BFTSpec == 
    [][BFTNext]_<<backupState, leaderState, leaderPrepared, msgs>> /\ BFTInit
  (*************************************************************************)
  (* The complete spec of the BFT Consensus protocol.                      *)
  (*************************************************************************)

BFTConsistent ==  
  (*************************************************************************)
  (* A state predicate asserting that two backups have not arrived at      *)
  (* conflicting decisions.  It is an invariant of the specification.      *)
  (*************************************************************************)
  \A r1, r2 \in Backup :  ~ /\ backupState[r1] = "aborted"
                            /\ backupState[r2] = "committed"

THEOREM BFTSpec => [](BFTTypeOK /\ BFTConsistent)
  (*************************************************************************)
  (* Theorem asserts that the state predicate BFTTypeOK /\ BFTInvariant    *)
  (* is an invariant of the specification BFTSpec.                         *)
  (*************************************************************************)
-----------------------------------------------------------------------------

(* Definitions for symmetry set-based reduction *)
\* CONSTANTS
\* n1, n2, n3
\* symm == Permutations({n1, n2, n3})

=============================================================================