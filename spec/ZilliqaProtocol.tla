---------------------------- MODULE ZilliqaProtocol -------------------------
EXTENDS TLC, Integers, FiniteSets, Sequences, Randomization

(******************* parameters of Zilliqa Protocol ************************)

shardID == {0, 1, 2}

NodeID ==
    {"n1", "n2", "n3", "n4", "n5", "n6", "n7", "n8", "n9", "n10", "n11", "n12",
     "n13", "n14", "n15", "n16", "n17", "n18", "n19", "n20"}

TxID ==
    {"tx1", "tx2", "tx3", "tx4", "tx5", "tx6", "tx7", "tx8"}

CONSTANTS
    Node,                  (* set of nodes (node pool) *)
    Tx,                    (* set of transactions (transaction pool) *)
    initialNodes,          (* set of initial nodes already part of the protocol *)
    initShardStructure,    (* shard ID mapped to element nodes in the beginning *)
    shardSizeMin,          (* lower bound of shard size *)
    shardSizeMax           (* upper bound of shard size *)

ASSUME
    /\ Node                 \subseteq NodeID \X Nat \X BOOLEAN
    /\ Tx                   \subseteq TxID \X BOOLEAN
    /\ initialNodes         \subseteq Node
    /\ shardSizeMin         \in Nat
    /\ shardSizeMax         \in Nat
    /\ Cardinality(Node) \leq Cardinality(shardID) * shardSizeMax 
        (* enough space for all available nodes to join *)
    /\ \A id \in shardID : Len(initShardStructure[id]) \geq 0
        (* all the shards already exist from the beginning *)
    /\ \A id \in shardID : /\ (Len(initShardStructure[id]) \geq shardSizeMin)
                           /\ (Len(initShardStructure[id]) \leq shardSizeMax)
        (* size of every shard is within the acceptable range *)

VARIABLE epoch              (* current DS epoch term *)
VARIABLE nodesZilliqa       (* set of nodes participating in the protocol *)
VARIABLE shardStructure     (* set of shards participating in the protocol *)
    (* e.g.,
       (0 :> << <<"n1", 11, TRUE>>, <<"n2", 12, TRUE>>, <<"n3", 13, TRUE>>, <<"n4", 14, TRUE>> >> @@ 
        1 :> << <<"n5", 15, TRUE>>, <<"n6", 16, TRUE>>, <<"n7", 17, TRUE>>, <<"n7", 18, TRUE>> >>) *)
VARIABLE microBlocks        (* data blocks processed by shards at current epoch *)
    (* e.g.,
       (0 :> [epochTerm |-> 1, txsAgreed |-> {<<"tx1", TRUE>>}]) *)
VARIABLE historyOfBlocks    (* history of data blocks processed and stored *)
    (* e.g., 
       { [epochTerm |-> 1, txsCollated |-> {<<"tx1", TRUE>>, <<"tx2", TRUE>>}], ... } *)
VARIABLE timeCounter        (* increment counter by 1 per action, used to notify a timeout *)
VARIABLE numTxsRcvd         (* number of transactions received (to update DS committee) *)
VARIABLE txsProcessed       (* set of txs committed to the historyOfBlocks *)
VARIABLE faultyTxs          (* set of faulty txs being recorded, very specific to this design *)

zilvars == <<epoch, nodesZilliqa, shardStructure, microBlocks, historyOfBlocks, timeCounter, numTxsRcvd, txsProcessed, faultyTxs>>

(********************** parameters of TCommit *****************************)

VARIABLE cnsState

cnsvars == <<cnsState>>

cnsNodes == {"n1", "n2", "n3"}
    \* suppose only the nodes from DS shard are participating

TC == INSTANCE TCommit WITH RM <- cnsNodes, rmState <- cnsState

-----------------------------------------------------------------------------

TypeOK ==
    /\ epoch            \in {0} \cup Nat 
    /\ nodesZilliqa     \subseteq Node
    /\ timeCounter      \in {0} \cup Nat
    /\ numTxsRcvd       \in {0} \cup Nat
    /\ txsProcessed     \subseteq Tx
    /\ faultyTxs        \subseteq Tx
    /\ \A id \in shardID : 
       (Len(shardStructure[id]) \geq shardSizeMin) /\ (Len(shardStructure[id]) \leq shardSizeMax)

Init ==
    /\ TC!TCInit
    /\ epoch            = 0
    /\ nodesZilliqa     = initialNodes
    /\ shardStructure   = initShardStructure
    /\ microBlocks      = [id \in shardID |-> [epochTerm |-> epoch, txsAgreed |-> <<>>]]
    /\ historyOfBlocks  = {}
    /\ timeCounter      = 0
    /\ numTxsRcvd       = 0
    /\ txsProcessed     = {}
    /\ faultyTxs        = {}

-----------------------------------------------------------------------------

nonParticipating == Node \ nodesZilliqa
Participating == Node \ nonParticipating
notReceivedSofar == Tx \ txsProcessed

\* helpers
IsElementInSet(set, elem) == \E x \in set : x = elem

\* check element e's membership of sequence 
SeqContains(s, e) == \E i \in 1..Len(s) : s[i] = e

\* Go through shardStructure, return shardID based on the given node (technically, sender's address)
FindShardIDofNode(node) == 
    CHOOSE sId \in shardID : SeqContains(shardStructure[sId], node)

(***************************************************************************)
(*                                Actions                                  *)
(***************************************************************************)

(* ----------------------------------------------- *)
(* -- Every new node does a PoW to join Zilliqa -- *)
(* ----------------------------------------------- *)
RECURSIVE ProofOfWork(_)
ProofOfWork(node) ==
    LET 
    \* hash based on node and gen shardNum (based on randomness)
       hash == RandomElement(1..10) + RandomElement(1..node[2])
       difficulty == node[2] \* if too difficult, running TLC becomes slower
       shardnum == node[2] % Cardinality(shardID)
       prevMembers == shardStructure[shardnum]
    IN
       IF (hash \geq difficulty) /\ (Len(prevMembers) # shardSizeMax)
       THEN shardnum
       ELSE ProofOfWork(node)
       (* notes : in this design shard ID is not entirely random, but dependent on node's address
        *         assuming that addresses are universally distributed random numbers
        *         modulus will equally distribute newly joining nodes across shards
        *         considered the possibility of newNode joining DS shard directly *)

(* **************************** *)
(*   Main #1 : new node joins   *)
(* **************************** *)

NewNodeJoins(newNode) ==
  (*************************************************************************)
  (* ACTION: a new node does PoW and gets assigned to shard with shardNum  *)
  (*         update the shard structure and list of Zilliqa nodes          *)
  (*************************************************************************)
    IF IsElementInSet(nodesZilliqa, newNode)
    THEN
        /\ UNCHANGED zilvars 
        /\ UNCHANGED cnsvars
    ELSE
        /\ timeCounter' = timeCounter + 1
        /\ nodesZilliqa' = nodesZilliqa \cup {newNode}
        /\
          LET shardNum == ProofOfWork(newNode)
              prevMembers == shardStructure[shardNum]
          IN
            shardStructure' = 
              [shardStructure EXCEPT ! [shardNum] = Append(shardStructure[shardNum], newNode)]
            /\ UNCHANGED <<epoch, microBlocks, historyOfBlocks, numTxsRcvd, txsProcessed, faultyTxs>>
            /\ UNCHANGED cnsvars

-----------------------------------------------------------------------------

\* Check we're at the right epoch term before updating microBlocks and DSBlock
AtTheRightEpochTerm == \A sId \in shardID : microBlocks[sId].epochTerm = epoch

(* ----------------------------------------------- *)
(* ---- Run consensus and verify transaction ----- *)
(* ----------------------------------------------- *)

\* each of all shards run pBFT, gen microBlock [epochTerm : Nat, Tx : tx]
ShardProcessTx(snum, tx) ==
    CASE tx[2] = TRUE -> \* simplified verification procedure
        LET
            txAgrd == tx
            TxsAppended == microBlocks[snum].txsAgreed \o <<txAgrd>>
            existEpoch == microBlocks[snum].epochTerm
        IN
            /\ TC!TCNext
            /\ microBlocks' = [microBlocks EXCEPT ! [snum] =
                            [epochTerm |-> existEpoch, txsAgreed |-> TxsAppended]]
            /\ txsProcessed' = txsProcessed \cup {tx}
            /\ UNCHANGED <<faultyTxs>>
    []OTHER -> 
        /\ faultyTxs' = faultyTxs \cup {tx}
        /\ UNCHANGED <<microBlocks, txsProcessed>>
        /\ UNCHANGED cnsvars

(* **************************** *)
(*    Main #2 : new tx rcv'd    *)
(* **************************** *)

NewTxRcvd(tx, sender) ==
  (*************************************************************************)
  (* ACTION: Zilliqa receives a new transaction from the 'sender' node     *)
  (*         it processes the tx only when the sender is a Zilliqa node    *)
  (*         if \E enough micro blocks, then collate and commit to history *)
  (*************************************************************************)
    IF 
      /\ IsElementInSet(nodesZilliqa, sender)
      /\ IsElementInSet(Tx \ txsProcessed, tx)
    THEN
        /\ numTxsRcvd' = numTxsRcvd + 1   \* increment numTxsRcvd by 1
        /\ timeCounter' = timeCounter + 1 \* increment timeCounter by 1
        /\ AtTheRightEpochTerm             \* enabling condition
        /\ IsElementInSet(Tx \ txsProcessed, tx)       \* enabling condition
        /\ 
            \* update microBlock of a relevant shard
            LET shardIDNum == FindShardIDofNode(sender)
            IN ShardProcessTx(shardIDNum, tx)
        /\ UNCHANGED <<epoch, nodesZilliqa, shardStructure, historyOfBlocks>>
    ELSE
        /\ UNCHANGED zilvars
        /\ UNCHANGED cnsvars

(* note : txs submitted should come by sender who is participating in the protocol
 *        ie, no txs sent by non-participating node will be processed by the protocol
 *        this condition is checked as an enabling condition above *)

-----------------------------------------------------------------------------

(* ----------------------------------------------- *)
(* ---- Check if there are enough MicroBlocks ---- *)
(* ----------------------------------------------- *)
Pick(S) == CHOOSE s \in S : TRUE

RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_,_), S, value) ==
    IF S = {} THEN value
    ELSE
        LET s == Pick(S)
        IN  IF Op(s, value) = Op(value, s)
            THEN SetReduce(Op, S \ {s}, Op(s, value))
            ELSE Assert(FALSE, "oh no, not communitative Op")

Sum(S) == LET _op(a, b) == a + b IN SetReduce(_op, S, 0)

Max(S) == CHOOSE x \in S: 
            \A y \in S: y <= x

RECURSIVE CombineLengths(_,_)
CombineLengths(set, shID) ==
    IF shID \leq Max(shardID)
    THEN LET tempSet == set \cup {Len(microBlocks[shID].txsAgreed)}
         IN CombineLengths(tempSet, (shID + 1))
    ELSE set

\* Condition to trigger DS to gen dsBlock
EnoughMicroBlocks(n) ==
    LET setLengths == CombineLengths({}, 1) \* provide empty set and 0 as inputs
    IN Sum(setLengths) \geq n \* reduced to 3, otherwise too slow to run TLC

(* ----------------------------------------------- *)
(* --- Generate DS Block and commit to history --- *)
(* ----------------------------------------------- *)
DSRunBFTConsensus(leader, backups, txs) ==
    txs

\* traverse microBlocks and collect all the transactions into txsCollated
RECURSIVE CollateMicroBlocksTxs(_,_)
CollateMicroBlocksTxs(seq, sID) ==
    IF sID \leq Max(shardID)
    THEN LET tempSeq == seq \o microBlocks[sID].txsAgreed
         IN 
            CollateMicroBlocksTxs(tempSeq, (sID + 1))
            \* /\ \A i \in 1..Len(tempSeq) : txsProcessed' = txsProcessed \cup tempSeq[i]
    ELSE seq

\* DS Committee runs BFT and gen dsBlock (to add to historyOfBlocks)
DSAgreesOnFinalBlock ==
    LET
      leaderDS == Head(shardStructure[0])
      backupsDS == Tail(shardStructure[0])
      transactionsCollated == DSRunBFTConsensus(leaderDS, backupsDS, CollateMicroBlocksTxs(<<>>, 0))
    IN 
      [epochTerm |-> epoch, txsCollated |-> transactionsCollated]

(* **************************** *)
(*  Main #3 : commit to history *)
(* **************************** *)

CommitToHistoryPerMBs(numMB) ==
    IF
      EnoughMicroBlocks(numMB) \* condition to trigger DS to gen DSBlock
    THEN 
      LET 
        dsBlock == DSAgreesOnFinalBlock \* collate txs and commit to history
      IN
        /\ historyOfBlocks' = historyOfBlocks \cup {dsBlock}
        /\ \A id \in shardID : \* upon pushing to history, empty the microBlocks
                microBlocks' = [microBlocks EXCEPT ! [id].txsAgreed = <<>>] 
        /\ UNCHANGED <<epoch, nodesZilliqa, shardStructure, faultyTxs>>
        /\ UNCHANGED cnsvars
    ELSE 
      /\ UNCHANGED zilvars
      /\ UNCHANGED cnsvars

-----------------------------------------------------------------------------

\* condition refers to "after cnt number of timeCounter (global clock variable)"
EnoughTimePassed(cnt) ==
    /\ timeCounter # 0
    /\ timeCounter % cnt = 0

(* **************************** *)
(*      Main #4 : time out      *)
(* **************************** *)

TimeOut ==
  (*************************************************************************)
  (* ACTION: system times out, so move onto the next epoch                 *)
  (*         set the global glock timeCounter to 0                         *)
  (*         keep microBlocks, to be committed to history in next epoch    *)
  (*************************************************************************)
    IF EnoughTimePassed(3)
    THEN /\ epoch' = epoch + 1
         /\ \* synchronize epoch across the protocol by updating epochTerm for every shard ID
           \A sID \in shardID : microBlocks' = [microBlocks EXCEPT ! [sID] =
                                [epochTerm |-> microBlocks[sID].epochTerm + 1,
                                 txsAgreed |-> microBlocks[sID].txsAgreed]]
         /\ UNCHANGED <<nodesZilliqa, shardStructure, historyOfBlocks, numTxsRcvd, txsProcessed, faultyTxs>>
         /\ UNCHANGED cnsvars
    ELSE 
      /\ UNCHANGED zilvars
      /\ UNCHANGED cnsvars

-----------------------------------------------------------------------------

\* condition refers to "for every 'num' number of transactions received"
ReceivedNumTxs(num) ==
    /\ numTxsRcvd # 0
    /\ numTxsRcvd % num = 0

\* select a non-DS random shard and avoid selecting a shard whose seq is empty
RECURSIVE ChooseNonDSNonEmptyShardID(_)
ChooseNonDSNonEmptyShardID(toExclude) ==
    LET tempID == RandomElement(shardID \ toExclude)
    IN 
      IF shardStructure[tempID] # <<>>
      THEN tempID
      ELSE 
        LET updatedToExclude == toExclude \cup {tempID}
        IN ChooseNonDSNonEmptyShardID(updatedToExclude)
    (* Note : not necessary given that shard size remains in [minSize, maxSize]
     *        also recursive function slows down the model checking process *)

(* **************************** *)
(*   Main #5 : update DS shard  *)
(* **************************** *)

UpdateDSCommittee(othershID) ==
    IF ReceivedNumTxs(3)
    THEN     
        LET 
            oldestMemberDS == Head(shardStructure[0])
            restPrevMembersDS == Tail(shardStructure[0])
            oldestMemberOther == Head(shardStructure[othershID])
            restPrevMembersOther == Tail(shardStructure[othershID])
        IN
          /\ shardStructure' = [shardStructure EXCEPT ! [othershID] = Append(restPrevMembersOther, oldestMemberDS),
                                                      ! [0] = Append(restPrevMembersDS, oldestMemberOther)]
          /\ timeCounter' = timeCounter + 1
          /\ UNCHANGED <<epoch, nodesZilliqa, microBlocks, historyOfBlocks, numTxsRcvd, txsProcessed, faultyTxs>>
          \* sequence works in FIFO order so head refers to oldest, etc.
          /\ UNCHANGED cnsvars
    ELSE 
        /\ UNCHANGED zilvars \* tuple of all the global variables
        /\ UNCHANGED cnsvars

-----------------------------------------------------------------------------

nonFaulty == Tx \ faultyTxs

Next ==
  (*************************************************************************)
  (* POSSIBLE MOVES:                                                       *)
  (*  1. a new non-participating node joins the protocol                   *)
  (*  2. the protocol receives a new transaction                           *)
  (*  3. given enough micro blocks, a ds block is committed to history     *)
  (*  4. if enough time has passed, then time out and move to next epoch   *)
  (*  5. upon receiving some number of txs, the DS committee is updated    *)
  (*************************************************************************)
    \/ \E newNode \in Node : NewNodeJoins(newNode)
    \/ \E newTx \in nonFaulty, sndr \in Node : NewTxRcvd(newTx, sndr)
    \/ CommitToHistoryPerMBs(5)
    \/ TimeOut
    \/ UpdateDSCommittee(RandomElement(shardID \ {0}))

-----------------------------------------------------------------------------

\* myview == <<epoch, microBlocks, shardStructure, txsProcessed, numTxsRcvd, historyOfBlocks, timeCounter>>

\* notes :
\* - initially excluded : microBlocks, timeCounter
\* - below makes checking via TLC intractable
\*   myview == <<microBlocks>>
\* - checked below separately
  myview == <<epoch, nodesZilliqa, shardStructure>>
\*   myview == <<epoch, nodesZilliqa, shardStructure, txsProcessed>>

-----------------------------------------------------------------------------

(* **************************** *)
(*    Correctness properties    *)
(* **************************** *)

\* once in microBlocks, it will be committed to the historyOfBlocks
\* this property implies that the protocol prevents double spending attacks
TransactionFinality ==
    \A id \in shardID :
        \A index \in 1..Len(microBlocks[id].txsAgreed) :
          LET txElem == microBlocks[id].txsAgreed[index]
          IN \E block \in historyOfBlocks :
                \* \E ind \in 1..Len(block.txsCollated) :
                    SeqContains(block.txsCollated, txElem) 
               
               \* changed above 3 lines from below
               \* IsElementInSet(txsProcessed, txElem)


\* once rcv tx, it should not be processed by two different shards
\* that is once rcv tx, it will be processed by a single shard

\* txs that are eventually committed to the history are correct
\* note : currently once txs are commmitted, 
\*        there is no way to verify their original senders
CorrectTxsCommitted ==
    \A blck \in historyOfBlocks : 
       \A ind \in 1..Len(blck.txsCollated) :
            blck.txsCollated[ind][2] = TRUE
    
    (* note : above version makes more sense than below
     * \A tx \in txsProcessed : (tx[2] = TRUE) /\ (tx \notin faultyTxs) *)

-----------------------------------------------------------------------------

(* State-space constraints to make checking of this model via TLC tractable *)

\* stop after some # of DS blocks is commited to the history
DSCommitConstr ==
    Cardinality(historyOfBlocks) < 2

\* stop after sufficient amount of time has passed
TimeConstr ==
    epoch < 2

\* invariant to see scenario when all available nodes join the protocol
AllNodesJoinedZilliqa ==
    Cardinality(nodesZilliqa) # Cardinality(Node)

AfterSomeTime ==
    epoch # 1 \* numTxsRcvd # 20

-----------------------------------------------------------------------------

(* Limitations of the current model
 * - Because backup nodes participating in the pBFT consensus are fixed,
 *   we cannot verify a property that "nodes who are not participating
 *   should not play any role in consensus"
 * - Since it lacks specification of possible misbehavior of byzantine nodes,
 *   we cannot verify how presence of byzantine nodes can lead to committing faulty txs
 *)

\* additional comment (To remove later)
\* DSBlock == [epochTerm : Nat, txsCollated : Tx]
\* note : separate definition of DS Block removed
\*        it is implicit structure in the history set, no need for a separate definition

=============================================================================