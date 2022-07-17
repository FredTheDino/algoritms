# A small sketch program used to test the algoritm.
# Quickly sketched together to try to disprove it.
# The algoritm can be implemented a lot faster if you use some pointers,
# but this is good enough to test it out. :)

from itertools import permutations, chain
import random
from collections import defaultdict
import functools
import graph

nodes = set([0, 1, 2, 3, 5])
edges = set([(0, 1), (0, 2), (1, 3), (2, 5)])

#printx = print
printx = lambda *a, **kw: None

def pupper(nodes, edges):
    """
    todo: find a function :: line -> line -> line
    todo: caching: line :: { length :: Int, members :: List elem }
    todo: n-way merge can probably be done faster than repeated 2-way merge, at least in single threaded execution

    - start with any smallest fork-join sequence you can find, e.g. a diamond shape of 4 nodes
    - merge them in any random order into a linear order
    - repeat until there's just one line, and we're done


    different views of the same problem:

    # poset -> oset
    We have a partially ordered set, we want a fully ordered (acyclic) set. Computing the transitive constraints means each pair of nodes will be in one of three states; LT, EQ, GT. We want to add constraints until none of them are EQ.

    # v shape -> line
    We have a V shape (`Head1 -> Meet <- Head2` or dual of this), where the two tops don't have an ordering relative to each other. We want to find a random total ordering for our toposort. Thus, for each V shape, we sort the two Head nodes by adding another arrow between them. There are exactly two choices for exactly one arrow to add; which direction should it point? Afterwards, any incoming arrows into either Head is moved to the topmost Head (the one furthest away from the Meet node).

    How do we find a V shape?
    line node: a node with at most one incoming and at most one outgoing edge
    join node: any node that's not a line node
    line: sequence of connected line nodes

    # walk from Head1 to Meet to Head2
    1. pick any line node
    2. walk down the only outgoing edge until we find a join node
    3. walk up that path until we find another join node
    4. we have the three points of our V shape, now uniformly merge the V into a line

    # walk from Meet to Head1, and from Meet to Head2
    1. pick any meet node
    2. walk down one outgoing path until we find another join node
    2. walk down another outgoing path until we find a third join node
    4. we have the three points of our V shape, now uniformly merge the V into a line

    # Merging a V shape:
    1. uniformly randomly n choose k, e.g. https://cs.stackexchange.com/questions/104930/efficient-n-choose-k-random-sampling, literally randomly choosing k things out of n
    2. use the sampling above to figure out where to insert the nodes of the shorter line into the longer line (or vice versa)
    3. let HeadAfter = the head that ended up furthest from the join after the merge
    4. let HeadInner = the head that isn't HeadAfter
    5. all incoming(HeadInner) edges get moved to incoming(HeadAfter)
    6. optionally add pointers between HeadAfter and the node next to Join, so we don't have to traverse that part again

    The graph dual of the above algorithm should also work fine, swapping all incoming for outgoing etc.

    caching opportunities:
    - line nodes can hold pointers to the other side of the line, so we can find the other end of a line in constant time

    """

    g = graph.Graph.from_nodes_and_edges(nodes, edges)

    # x 1. is there a smaller fork/join between the two given nodes? if so, recurse and modify the graph in there
    # x 1.1. there's a smaller fork/join if there's any edge in/out from this graph which we haven't considered

    # 1. is there a smaller join between the two given nodes? if so, recurse and modify the graph in there
    # 1.1. there's a smaller join if there's any edge in/out from this graph which we haven't considered

    def handleFork(fork, nexts):
        return functools.reduce(lambda a, b: handleFork2(fork, a, b), nexts)

    def handleFork2(fork, child1, child2):
        printx(f"handleFork2(child1:{child1}, child2:{child2})")
        lca = g.findLCA(child1, child2)
        printx("handleFork2: lca is", lca)
        return merge2(fork, child1, child2)

    def merge2(fork, head1, head2):
        """
        pick a random point in the graph, walk down until you find a join, walk up another path from that join until you find another join/fork/end, merge that V shape into a line like so:
        - head1
        - head2
        - join

        - move all incoming(head1) + incoming(head2) to incoming(headAfter)
        """

        # invariants:
        printx(head1, head2, g)
        assert len(g.outgoing(head1)) == 1, (g, head1)
        assert len(g.outgoing(head2)) == 1, (g, head2)
        paths = g.findLCA_with_paths(head1, head2)
        join = paths.lca
        printx(f"paths:{paths}")

        printx(f"merge2(head1:{head1}, head2:{head2}, join:{join})")
        r1 = paths.path1
        r2 = paths.path2

        p1 = []
        for e in r1:
            if e == join:
                break
            ine = g.incoming(e)
            if len(ine) >= 2:
                print("inner join in p1")
                0 / 0
            p1 += [e]
        p2 = []
        for e in r2:
            if e == join:
                break
            ine = g.incoming(e)
            if len(ine) >= 2:
                print("inner join in p2")
                0 / 0
            p2 += [e]

        printx(f"merge2({head1}, {head2}, join:{join}) -> p1:{p1} p2:{p2}")

        nep = g.get_all_nodes_and_edge_pairs()

        res = uniformly_random(nep.nodes, nep.edges)

        printx("res", res)
        printx("nodes1", g)

        g.zip(nep.edges, res)

        print("nodes2", g)

    # the core impl

    # data Solution = Line { length :: Int, members :: List NodeId } | MeetJoin { children :: List NodeId, parents :: List NodeId }

    # TODO[fh]: check incoming edges to bail out if either line is not a line? what's the algorithm for that? solve the sub-problem where the join point is the new head, and then backtrack to merging the subproblem into the original problem? probably works.

    for node in nodes:
        if len(g.outgoing(node)) >= 2:
            printx("fork node", node)
            m = handleFork(node, set(g.outgoing(node)))

            # todo[fh]: update outgoing

            printx("fork merged", node, "g", g)
        if len(g.incoming(node)) >= 2:
            printx("join node", node)

    pass


def is_valid_order(constraints):
    def inner(order):
        picked = set()
        available = set(order) - set(map(lambda x: x[1], constraints))
        for o in order:
            if o not in available:
                return False
            picked.add(o)
            for oo in order:
                if all((x in picked or y != oo) for (x, y) in constraints):
                    available.add(oo)
        return True

    return inner


def list_permutations(nodes, edges):
    return list(filter(is_valid_order(edges), permutations(nodes)))


def size(node, edges):
    # This can be speed up substatially
    return 1 + sum(size(b, edges) for (a, b) in edges if a == node)


def uniformly_random(nodes, edges):
    assert isinstance(nodes, set)
    assert isinstance(edges, set)
    possible = {}

    def weighted_random(p):
        # This can be done a lot faster

        # NOTE[ed]: If you change this to `random.randint(0, sum(p.values()))` and `n <= 0`, the algoritm does not work at all since the sampling is biased towards the first element. It's worth taking extra care making sure this sampling is uniform.
        n = random.randint(1, sum(p.values()))
        for (a, w) in p.items():
            n -= w
            if n <= 0:
                return a
        assert False, "Reached unreachable code"

    picked = set()
    order = []
    while picked != nodes:
        # Update weights for pickable nodes, this can be done a lot faster
        for a in nodes:
            if a in picked: continue
            if a in possible: continue
            if all((x in picked or y != a) for (x, y) in edges):
                possible[a] = size(a, edges)

        q = weighted_random(possible)
        assert q not in picked, "Picking the same node twice!"
        picked.add(q)
        order.append(q)
        possible.pop(q)

    order = tuple(order)
    assert is_valid_order(edges)(order), "Not a valid order..."
    printx(f"uniformly_random(nodes:{nodes}, edges:{edges}) -> {order}")
    return order


def check_randomness(nodes, edges):
    num_samples = 100000
    samples = defaultdict(int)
    for _ in range(num_samples):
        # idx = uniformly_random(nodes, edges)
        idx = pupper(nodes, edges)
        samples[idx] += 1
        #exit(42)

    all_of_them = list_permutations(nodes, edges)
    assert (len(all_of_them) == len(samples)), f"Cannot generate all orders ans:{all_of_them}, given:{list(samples.keys())}"

    expected = num_samples / len(samples)
    variances = []
    for a, b in samples.items():
        # You probably want to use a Beta-distribution here, to see the likelyhood of the distribution being uniform.
        # But this crude test is probably (pun very much intended) good enough.
        if abs(b - expected) > expected * 0.05:
            print(f"Outlier! {a}, with {b} but expected ~{expected}")
        variances.append((b - expected) ** 2)

    return sum(variances) ** 0.5, samples


print("Diamond")
print(check_randomness(set(range(3 + 1))
                       , set([(0, 1), (0, 2), (1, 3), (2, 3)])
                       ))

print("DoubleSeqDiamond")
print(check_randomness(set(range(6 + 1))
                       , set([(0, 1), (0, 2), (1, 3), (2, 3), (3, 4), (3, 5), (4, 6), (5, 6)])
                       ))

print("DoubleParDiamond")
print(check_randomness(set(range(6 + 1))
                       , set([(0, 1), (0, 2), (1, 3), (2, 3), (4, 2), (2, 6), (4, 5), (5, 6)])
                       ))

print("free 4")
print(check_randomness(set(range(3 + 1))
                       , set([])
                       ))

print("line 4")
print(check_randomness(set(range(3 + 1))
                       , set([(0, 1), (1, 2), (2, 3), (3, 4)])
                       ))

print("First test!")
print(check_randomness(set(range(5 + 1))
                       , set([(0, 1), (0, 2), (1, 3), (2, 5)])
                       ))

print("Second test!")
print(check_randomness(set(range(6 + 1))
                       , set([(0, 1), (1, 2), (1, 3), (0, 4), (4, 5), (5, 6)])
                       ))

print("Third test!")
print(check_randomness(set(range(7 + 1))
                       , set([(0, 1), (1, 2), (1, 3), (3, 4), (4, 5), (5, 6), (0, 7)])
                       ))

print("Fourth test!")
print(check_randomness(set(range(8 + 1))
                       , set([(0, 1), (1, 2), (1, 3), (3, 4), (4, 5), (5, 6), (0, 7)])
                       ))

# print("Fifth test!")
# print(check_randomness(set(range(4 + 1))
#                       , set([(0, 1), (0, 2), (1, 3), (2, 3), (3, 4)])
#                       ))

## https://bjpcjp.github.io/pdfs/math/topological-sort-ADM.pdf
print("topo-sort adm example graph, join-only version, skipping the right child if there's two")
print(check_randomness(set(range(10 + 1)),
                       set([
                           (8, 4),
                           (4, 2),
                           (10, 5),
                           # (10, 2),
                           (6, 2),
                           # (6, 3),
                           (9, 3),
                           (5, 1),
                           (2, 1),
                           (3, 1),
                           (7, 1),
                           (1, 0)  # this 1 -> 0 edge is extra, because they number 1-10 and we 0-n, so I added an extra zero here
                       ])
                       ))

## https://bjpcjp.github.io/pdfs/math/topological-sort-ADM.pdf
# print("topo-sort adm example graph")
# print(check_randomness(set(range(10 + 1)),
#                       set([
#                           (8, 4),
#                           (4, 2),
#                           (10, 5),
#                           (10, 2),
#                           (6, 2),
#                           (6, 3),
#                           (9, 3),
#                           (5, 1),
#                           (2, 1),
#                           (3, 1),
#                           (7, 1),
#                           (1, 0) # this 1 -> 0 edge is extra, because they number 1-10 and we 0-n, so I added an extra zero here
#                       ])
#                       ))

# m = 5
# print("--- 1 ---")
# for n in range(1, m):
#     print(n)
#     list_permutations( set(chain(range(0, n)))
#                      , set(chain(zip(range(0, n), range(1, n))))
#                      )
#
# print("--- 2 ---")
# for n in range(1, m):
#     print(n)
#     list_permutations( set(chain(range(0, n), range(n, 2*n)))
#                      , set(chain(zip(range(0, n), range(1, n)), zip(range(n, 2*n), range(n+1, 2*n))))
#                      )
#
# print("--- 3 ---")
# for n in range(1, m):
#     print(n)
#     list_permutations( set(chain(range(0, n), range(n, 2*n), range(2*n, 3*n)))
#                      , set(chain(zip(range(0, n), range(1, n)), zip(range(n, 2*n), range(n+1, 2*n)), zip(range(2*n, 3*n), range(2*n+1, 3*n))))
#                      )
