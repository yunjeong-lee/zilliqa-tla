---------------------------- MODULE ZilliqaProtocol -------------------------
EXTENDS TLC, Integers, FiniteSets, Sequences, Randomization

(******************* parameters of Zilliqa Protocol ************************)

shardID == {0, 1, 2}

NodeID ==
    {"n1", "n2", "n3", "n4", "n5", "n6", "n7", "n8", "n9", "n10", "n11", "n12",
     "n13", "n14", "n15", "n16", "n17", "n18", "n19", "n20"}

TxID ==
    {"tx1", "tx2", "tx3", "tx4", "tx5", "tx6", "tx7", "tx8", "tx9", "tx10", "tx11", "tx12"}

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

VARIABLE consenState
consenNodes == {"n1", "n2", "n3"}
    \* suppose only the DS nodes employ TCommit to agree on final block

cnsvars == <<consenState>>

TC == INSTANCE TCommit WITH RM <- consenNodes, rmState <- consenState

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

\* condition "after cnt number of timeCounter (global clock variable)"
EnoughTimePassed(cnt) ==
    /\ timeCounter # 0
    /\ timeCounter % cnt = 0

\* condition "after cnt number of txs is received"
EnoughTxsRcvd(cnt) ==
    /\ numTxsRcvd # 0
    /\ numTxsRcvd % cnt = 0

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
(*    Action : new node joins   *)
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

\* traverse microBlocks and collect all the transactions into txsCollated
RECURSIVE CollateMicroBlocksTxs(_,_)
CollateMicroBlocksTxs(seq, sID) ==
    IF sID < Cardinality(shardID)
    THEN LET tempSeq == seq \o microBlocks[sID].txsAgreed
         IN 
            CollateMicroBlocksTxs(tempSeq, (sID + 1))
            \* /\ \A i \in 1..Len(tempSeq) : txsProcessed' = txsProcessed \cup tempSeq[i]
    ELSE seq

CollateAlternative ==
    (microBlocks[0].txsAgreed \o microBlocks[1].txsAgreed) \o microBlocks[2].txsAgreed

\* DS Committee runs BFT and gen dsBlock (to add to historyOfBlocks)
DSAgreesOnFinalBlock ==
    LET transactionsCollated == CollateMicroBlocksTxs(<<>>, 0) \* seq of txs collected from microblocks
    IN [epochTerm |-> epoch, txsCollated |-> transactionsCollated] \* final block to commit

EmptyMicroBlock(shardid) ==
    microBlocks' = [microBlocks EXCEPT ![shardid].txsAgreed = <<>>]

-----

\* Check we're at the right epoch term before updating microBlocks and DSBlock
AtTheRightEpochTerm == \A sId \in shardID : microBlocks[sId].epochTerm = epoch

\* each shard runs some consensus protocol, gen microBlock [epochTerm : Nat, Tx : tx]
ShardProcessTx(snum, tx) ==
    LET
        txAgrd == tx
        TxsAppended == microBlocks[snum].txsAgreed \o <<txAgrd>>
        existEpoch == microBlocks[snum].epochTerm
    IN
        \* note since running TCommit is done by DS Committee in current version
        \* as the nodes participating in TCommit are statically declared as DS members
        /\ microBlocks' = [microBlocks EXCEPT ! [snum] =
                            [epochTerm |-> existEpoch, txsAgreed |-> TxsAppended]]
        /\ txsProcessed' = txsProcessed \cup {tx}

(* **************************** *)
(*     Action : new tx rcv'd    *)
(* **************************** *)

CommitToHistory ==
    /\ EnoughTxsRcvd(3)
    /\ TC!TCNext \* DS nodes run consensus before committing final blcok
    /\ historyOfBlocks' = historyOfBlocks \cup 
            {[epochTerm |-> epoch, txsCollated |-> CollateAlternative]} \* [prev] CollateMicroBlocksTxs(<<>>, 0)
    /\ epoch' = epoch + 1
    \* /\ \A id \in shardID : EmptyMicroBlock(id) \* changed to below just to be sure
    /\ microBlocks' =
        [microBlocks EXCEPT ! [0] = [epochTerm |-> microBlocks[0].epochTerm, txsAgreed |-> <<>>],
                            ! [1] = [epochTerm |-> microBlocks[1].epochTerm, txsAgreed |-> <<>>],
                            ! [2] = [epochTerm |-> microBlocks[2].epochTerm, txsAgreed |-> <<>>]]
    /\ UNCHANGED <<nodesZilliqa, shardStructure, numTxsRcvd, txsProcessed, faultyTxs, timeCounter>>

NewTxRcvd(tx, sender) ==
  (*************************************************************************)
  (* ACTION: Zilliqa receives a new transaction from the 'sender' node     *)
  (*         per some num of txs rcv'd, collate txs into a microblock and  *)
  (*         commit the microblock to the historyOfBlocks                  *)
  (*         it processes the tx only when the sender is a Zilliqa node    *)
  (*         and when the tx has not been processed already                *)
  (*************************************************************************)
    /\ IsElementInSet(nodesZilliqa, sender)     \* enabling condition
    /\ IsElementInSet(Tx \ txsProcessed, tx)    \* enabling condition
    /\ AtTheRightEpochTerm                      \* enabling condition
    /\ numTxsRcvd' = numTxsRcvd + 1
    /\ timeCounter' = timeCounter + 1
    /\ 
        \/  \* commit to history
            /\ EnoughTxsRcvd(3)             \* enabling condition for committing to history
            /\ TC!TCNext                    \* DS nodes run consensus before committing final blcok
            /\ historyOfBlocks' = historyOfBlocks \cup 
                    {[epochTerm |-> epoch, txsCollated |-> CollateAlternative]} \* [prev] CollateMicroBlocksTxs(<<>>, 0)
            /\ epoch' = epoch + 1
            /\ microBlocks' =
                [microBlocks EXCEPT ! [0] = [epochTerm |-> microBlocks[0].epochTerm, txsAgreed |-> <<>>],
                                    ! [1] = [epochTerm |-> microBlocks[1].epochTerm, txsAgreed |-> <<>>],
                                    ! [2] = [epochTerm |-> microBlocks[2].epochTerm, txsAgreed |-> <<>>]]
        \/  \* do not commit to history
            /\ UNCHANGED <<historyOfBlocks, epoch, microBlocks>>
            /\ UNCHANGED cnsvars
    /\
        \* simplified verification + process procedure
        \/  /\ tx[2] = TRUE \* update microBlock of a relevant shard
            /\ ShardProcessTx(FindShardIDofNode(sender), tx)
            /\ UNCHANGED <<faultyTxs>>
        \/  /\ tx[2] = FALSE
            /\ faultyTxs' = faultyTxs \cup {tx}
            /\ UNCHANGED <<txsProcessed>>
    /\ UNCHANGED <<nodesZilliqa, shardStructure>>                    

-----------------------------------------------------------------------------

(* **************************** *)
(*       Action : time out      *)
(* **************************** *)

TimeOut ==
  (*************************************************************************)
  (* ACTION: system times out, so move onto the next epoch                 *)
  (*         set the global glock timeCounter to 0                         *)
  (*         keep microBlocks, to be committed to history in next epoch    *)
  (*************************************************************************)
    /\ EnoughTimePassed(4) \* (timeCounter % 5 = 0) /\ (timeCounter # 0) \* enabling condition
    /\ epoch' = epoch + 1
    /\ \* synchronize epoch across the protocol by updating epochTerm for every shard ID
       microBlocks' =
        [microBlocks EXCEPT ! [0] = [epochTerm |-> microBlocks[0].epochTerm + 1, txsAgreed |-> microBlocks[0].txsAgreed],
                            ! [1] = [epochTerm |-> microBlocks[1].epochTerm + 1, txsAgreed |-> microBlocks[1].txsAgreed],
                            ! [2] = [epochTerm |-> microBlocks[2].epochTerm + 1, txsAgreed |-> microBlocks[2].txsAgreed]]
    /\ timeCounter' = timeCounter + 1
    /\ UNCHANGED <<nodesZilliqa, shardStructure, historyOfBlocks, numTxsRcvd, txsProcessed, faultyTxs>>
    /\ UNCHANGED cnsvars

-----------------------------------------------------------------------------

nonFaulty == Tx \ faultyTxs

Next ==
  (*************************************************************************)
  (* POSSIBLE MOVES:                                                       *)
  (*  1. a new node joins the protocol                                     *)
  (*  2. a new transaction is received                                     *)
  (*     - given enough microblocks, DS block is committed to history      *)
  (*  3. if enough time has passed, then time out and move to next epoch   *)
  (*************************************************************************)
    \/ \E newNode \in Node : NewNodeJoins(newNode)
    \/ \E newTx \in Tx, sndr \in Node : NewTxRcvd(newTx, sndr)
    \/ TimeOut

-----------------------------------------------------------------------------

(* **************************** *)
(*       Safety properties      *)
(* **************************** *)

\* if a node is participating in Zilliqa, then one of the shards contains the node
\* if a node is not participating in Zilliqa, then none of the shards contains it
NodeConsistent ==
    \A n \in Node : 
        \/
            /\ n \in Participating
            /\ \E id \in shardID : SeqContains(shardStructure[id], n)
        \/
            /\ n \in nonParticipating
            /\ \A id \in shardID : ~SeqContains(shardStructure[id], n)

\* no same node can join multiple nodes
NoNodeJoinsTwoShards ==
    \A n1, n2 \in Participating : 
        \E id1, id2 \in shardID :
            ~ /\ n1 = n2
              /\ id1 # id2
              /\ SeqContains(shardStructure[id1], n1)
              /\ SeqContains(shardStructure[id2], n2) 

\* no same transaction should be processed by two different shards
\* i.e., once rcv tx, it will be processed by a single shard
TxConsistent ==
    \A tx1, tx2 \in txsProcessed : 
        \E id1, id2 \in shardID : 
            ~ /\ tx1 = tx2
              /\ id1 # id2
              /\ SeqContains(microBlocks[id1].txsAgreed, tx1) 
              /\ SeqContains(microBlocks[id2].txsAgreed, tx2) 

\* once in microBlocks, it will be committed to the historyOfBlocks
\* this property implies that the protocol prevents double spending attacks
TransactionFinality ==
    \A id \in shardID :
        \A index \in 1..Len(microBlocks[id].txsAgreed) :
          LET txElem == microBlocks[id].txsAgreed[index]
          IN
            /\ IsElementInSet(txsProcessed, txElem)
            \* comment :
            \*  since it takes to commit to history (\E gap), we cannot write the following
            \*      \E block \in historyOfBlocks : SeqContains(block.txsCollated, txElem)

\* txs that are eventually committed to the history are correct
CorrectTxsCommitted ==
    \A blck \in historyOfBlocks : 
       \A ind \in 1..Len(blck.txsCollated) :
            blck.txsCollated[ind][2] = TRUE
    \* comment :
    \*  currently once txs are commmitted, there is no way to verify their original senders
    \*  so we do not say "all txs sent by honest nodes are correct"
    \*  also note that there can be correct txs sent by malicious nodes,
    \*  assuming that byzantine node may or may not send faulty txs
    
    (* note : above version is an alternative from the original version below
     *          \A tx \in txsProcessed : (tx[2] = TRUE) /\ (tx \notin faultyTxs) *)

-----------------------------------------------------------------------------

\* view to verify actions NewNodeJoins and TimeOut
\* myview == <<epoch, shardStructure, microBlocks, historyOfBlocks, timeCounter, txsProcessed, faultyTxs>>

\* view to verify action NewTxRcvd which leads to committing to history
myview == <<epoch, numTxsRcvd, txsProcessed, faultyTxs, numTxsRcvd, timeCounter>>

\* historyOfBlocks, 

(* Notes on variables
 1 epoch : included, to verify TimeOut
 2 nodesZilliqa : excluded, required when performing NewNodeJoins
 3 shardStructure : excluded, required when performing NewNodeJoins
 4 microBlocks : excluded, being a bottleneck
 5 historyOfBlocks : included, to verify blocks being committed and check relevant invariants
 6 timeCounter : included, meaningful when performing TimeOut
 7 numTxsRcvd : included, needed to commit to history (in the future work, to update DS committee)
 8 txsProcessed : included, needed to verify safety property TransactionFinality
 9 faultyTxs : included, meaningful when performing NewTxRcvd
 *)

-----------------------------------------------------------------------------

(* State-space constraints to make checking of this model via TLC tractable *)

\* stop after some # of DS blocks is commited to the history
DSCommitConstr == Cardinality(historyOfBlocks) < 2

\* stop after sufficient amount of time has passed
TimeConstr == epoch < 5

(* Invariants to make checking of this model via TLC tractable *)

\* invariant to print out what is committed to the history
DSCommitRecord == Cardinality(historyOfBlocks) # 2

\* invariant to print out what happens after some time passes
AfterSomeTime == epoch # 2

\* invariant to see scenario when all available nodes join the protocol
AllNodesJoinedZilliqa == Cardinality(nodesZilliqa) # Cardinality(Node)

-----------------------------------------------------------------------------

(* Limitations of the current model
 * - Because backup nodes participating in the pBFT consensus are fixed,
 *   we cannot verify a property that "nodes who are not participating
 *   should not play any role in consensus"
 * - Since it lacks specification of possible misbehavior of byzantine nodes,
 *   we cannot verify how presence of byzantine nodes can lead to committing faulty txs
 * - For some reason, TLC needs to explore so many paths to finally let microblocks to be committed to history
 *   So this part can be re-worked (possibly further simplified) on to make it more tractable.
 *)

\* additional comment (To remove later)
\* DSBlock == [epochTerm : Nat, txsCollated : Tx]
\* note : separate definition of DS Block removed
\*        it is implicit structure in the history set, no need for a separate definition

-----------------------------------------------------------------------------

\* Below are additional actions to be incorporated in future work

\* condition refers to "for every 'num' number of transactions received"
ReceivedNumTxs(num) ==
    /\ numTxsRcvd # 0
    /\ numTxsRcvd % num = 0

(* **************************** *)
(*   Action : update DS shard   *)
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

=============================================================================