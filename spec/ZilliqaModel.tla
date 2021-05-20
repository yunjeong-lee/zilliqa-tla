---- MODULE ZilliqaModel ----

EXTENDS ZilliqaProtocol, TLC

myNodes ==
    {<<"n1", 11, TRUE>>, <<"n2", 12, TRUE>>, <<"n3", 13, TRUE>>, 
     <<"n4", 14, TRUE>>, <<"n5", 15, TRUE>>, <<"n6", 16, TRUE>>,
     <<"n7", 17, TRUE>>, <<"n8", 18, TRUE>>, <<"n9", 19, TRUE>>,
     <<"n10", 20, TRUE>>, <<"n11", 21, FALSE>>, <<"n12", 22, TRUE>>,
     <<"n13", 23, TRUE>>, <<"n14", 24, FALSE>>, <<"n15", 25, TRUE>>,
     <<"n16", 26, TRUE>>, <<"n17", 27, TRUE>>, <<"n18", 28, TRUE>>}

myTxs ==
    {<<"tx1", TRUE>>, <<"tx2", TRUE>>, <<"tx3", FALSE>>, <<"tx4", TRUE>>,
     <<"tx5", TRUE>>, <<"tx6", TRUE>>, <<"tx7", TRUE>>, <<"tx8", TRUE>>}

myInitNodes ==
    {<<"n1", 11, TRUE>>, <<"n2", 12, TRUE>>, <<"n3", 13, TRUE>>,
     <<"n4", 14, TRUE>>, <<"n5", 15, TRUE>>, <<"n6", 16, TRUE>>,
     <<"n7", 17, TRUE>>, <<"n8", 18, TRUE>>, <<"n9", 19, TRUE>>}

myInitShardStructure ==
    (0 :> << <<"n1", 11, TRUE>>, <<"n2", 12, TRUE>>, <<"n3", 13, TRUE>> >> @@
     1 :> << <<"n4", 14, TRUE>>, <<"n5", 15, TRUE>>, <<"n6", 16, TRUE>> >> @@
     2 :> << <<"n7", 17, TRUE>>, <<"n8", 18, TRUE>>, <<"n9", 19, TRUE>> >>)

myShardSizeMin          == 3
myShardSizeMax          == 6

=============================