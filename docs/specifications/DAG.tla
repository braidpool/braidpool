-------------------------------- MODULE DAG --------------------------------

(***************************************************************************)
(* Specification of a directed acyclic graph taken from Lamport's          *)
(* Specifying Systems book.  We only took the operators we want to use.    *)
(***************************************************************************)

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

-----------------------------------------------------------------------------

Path(G) == \* The set of paths in G, where a path is represented as a sequence of nodes
    {p \in Seq(G.nodes): /\ p # <<>>
                         /\ \A i \in 1..(Len(p) - 1): <<p[i], p[i+1] \in G.edge>>}

AreConnected(m, n, G) == \* True if there is a path from m to n in G
    \exists p \in Path(G) : (p[1] = m) /\ (p[Len(p)] = n)
    

=============================================================================
