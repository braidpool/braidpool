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

SeqOf(set, n) ==
  (***************************************************************************)
  (* All sequences up to length n with all elements in set.  Includes empty  *)
  (* sequence.                                                               *)
  (***************************************************************************)
  UNION {[1..m -> set] : m \in 0..n}

ToSet(s) ==
  (*************************************************************************)
  (* The image of the given sequence s. Cardinality(ToSet(s)) <= Len(s)    *)
  (* see https://en.wikipedia.org/wiki/Image_(mathematics)                 *)
  (*************************************************************************)
  { s[i] : i \in DOMAIN s }

Contains(s, e) ==
  (**************************************************************************)
  (* TRUE iff the element e \in ToSet(s).                                   *)
  (**************************************************************************)
  \E i \in 1..Len(s) : s[i] = e

SimplePath(G) ==
    \* A simple path is a path with no repeated nodes.
    {p \in SeqOf(G.node, Cardinality(G.node)) :
             /\ p # << >>
             /\ Cardinality({ p[i] : i \in DOMAIN p }) = Len(p)
             /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in G.edge}

NodesInSimplePath(G, from, to) ==
    \* All nodes in a simple path betwee `from` and `to`
            UNION{ToSet(s): s \in
                    {p \in SimplePath(G):
                         (/\ p[1] = from)
                          /\ (p[Len(p)] = to)}}

AreConnected(m, n, G) == \* True if there is a path from m to n in G
    \exists p \in Path(G) : (p[1] = m) /\ (p[Len(p)] = n)  

    
=============================================================================
