-------------------------------- MODULE DAG --------------------------------

(***************************************************************************)
(* DiGraph operators taken from https://github.com/nano-o/TLA-Library/blob/master/DiGraph.tla *)
(***************************************************************************)

EXTENDS FiniteSets, Naturals, Sequences

-----------------------------------------------------------------------------
(*
The following two operators are from the Specifying Systems book, though 
I can't make Path work because of Seq being infinite and non-enumerable.
*)

Path(G) == \* The set of paths in G, where a path is represented as a sequence of nodes
    {p \in Seq(G.node): /\ p # <<>>
                        /\ \A i \in 1..(Len(p) - 1): <<p[i], p[i+1] \in G.edge>>}

AreConnected(m, n, G) == \* True if there is a path from m to n in G
    \exists p \in Path(G) : (p[1] = m) /\ (p[Len(p)] = n)  

(***************************************************************************)
(* A digraph is a set of vertices and a set of edges, where an edge is a   *)
(* pair of vertices.                                                       *)
(***************************************************************************)
Vertices(G) == G.node
Edges(G) == G.edge
IsDigraph(G) == Edges(G) \subseteq (Vertices(G) \times Vertices(G))


(***************************************************************************)
(* Recursive implementation of Dominates(v1,v2,G).                         *)
(***************************************************************************)
RECURSIVE DominatesRec(_,_,_,_)
DominatesRec(v1, v2, G, acc) ==
    \/ <<v1,v2>> \in Edges(G)
    \/ \E v \in Vertices(G) : 
        /\ \neg v \in acc
        /\ <<v1,v>> \in Edges(G)
        /\ DominatesRec(v, v2, G, acc \cup {v1}) 

(***************************************************************************)
(* True when there exists a path from v1 to v2 in the graph G              *)
(***************************************************************************)
Dominates(v1, v2, G) ==
    DominatesRec(v1,v2,G,{})
    
(***************************************************************************)
(* All the paths of length smaller or equal to n in graph G                *)
(***************************************************************************)
RECURSIVE Paths(_, _)
Paths(n, G) ==
    IF n = 1
    THEN 
        Edges(G)
    ELSE
        LET nextVs(p) == 
                { e[2] : e \in {e \in Edges(G) : e[1] = p[Len(p)]} }
            nextPaths(p) == { Append(p,v) : v \in nextVs(p) }
        IN
            UNION { nextPaths(p) : p \in Paths(n-1, G)}
            \cup Paths(n-1, G)
    
=============================================================================
