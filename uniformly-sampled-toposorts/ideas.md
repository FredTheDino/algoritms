# Some ideas for algoritms other then the ones implemented in `sketch.py`
```

G := A graph

# We know there exists a valid topological sorting if it is infact a graph
assert graph_is_dag(G)


# Version A
# Probably wrong, but at least how I would first attack the problem.
#
# Potentially we generate a lot of random numbers, 
#
# I'm not su
@memoise
def random_topological_sort(
    V: A vertex to start from
    G: The graph we are searching in
):  Returns: A random topological sorting of the children of V in G

    sorting := []
    for C in children_of(V, G)
        sub_sorting := random_topological_sort(C, G)
        sorting := keep_last_instance(merge_sorting(sorting, sub_sorting))
    return sorting

# Not sure this is correct
def merge_sorting(
    A: A sorting
    B: Another sorting
):  Returns a merged sorting which keeps the uniform random distribution
    if A == [] return B
    if B == [] return A

    if coin_flip()
    then merge_sorting(A[:-1]) ++ A[-1]
    else merge_sorting(B[:-1]) ++ B[-1]

def keep_last_instance(
    S: A sorting with duplicates
):  Returns a sorting without the duplicates, keeps the last one
    Seen := Set()
    Out := []
    for X in reversed(S):
        if X not in Seen:
            Out := append(Out, X)
            Seen := add(Seen, X)
    return Out
 
# Version B
# Very slow but will work, and works well for unconstrained graphs.
def is_valid_topological_sort(
    S: A topological sorting of the graph
    G: The graph itself
):  Returns if the sorting is valid or not
    Seen := Set()
    for X in S:
        if is_sub_set_of(parents(X), Seen)
        then Seen := add(Seen, X)
        else return False
    return True

def random_topological_sort(G):
    Tries := N
    while Tries > 0 do
        S := random_suffle_of_nodes(G)
        if is_valid_topological_sort(S)
        then return S
        else Tries := Tries - 1
    return FAILED

# Version C
# This idea isn't completely finished cooking. BUT, the main idea is:
#  - Walk a random path for all V in G
#  - Rejection sample all these paths, skipping all added nodes, until a node where all parents are added is found
# This is simple, but also a random algorithm. It might not be fast enough. It's like a merge between A and B,
# but I'm not sure we keep both of their strengths.

# Version D
# Not entirely finished either, but might be smarter
#  - Generate a random sorting
#  - Look for mistakes, if we find one, swap the positions of the nodes
# 
# This will work. If we know the parent's this is sorting (Right?) and probably quite easy to implement.
```
