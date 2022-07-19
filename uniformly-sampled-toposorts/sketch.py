"""
Already solved, e.g. in:
Fast perfect sampling from linear extensions, by Mark Huber

In this paper, we study the problem of sampling (exactly) uniformly from the set of linear extensions of an arbitrary partial order. Previous Markov chain techniques have yielded algorithms that generate approximately uniform samples. Here, we create a bounding chain for one such Markov chain, and by using a non-Markovian coupling together with a modified form of coupling from the past, we build an algorithm for perfectly generating samples. The expected running time of the procedure is `O(n^3 * ln(n))`, making the technique as fast as the mixing time of the Karzanov/Khachiyan chain upon which it is based.

https://www.sciencedirect.com/science/article/pii/S0012365X06000033

"""

# A small sketch program used to test the algoritm.
# Quickly sketched together to try to disprove it.
# The algoritm can be implemented a lot faster if you use some pointers,
# but this is good enough to test it out. :)

from itertools import permutations, chain
import random
from collections import defaultdict
import functools
from functools import partial
import graph
from time import sleep
import time
import os
import subprocess

nodes = set([0, 1, 2, 3, 5])
edges = set([(0, 1), (0, 2), (1, 3), (2, 5)])

last_file_contents = None

# printx = print
printx = lambda *a, **kw: None
printy = lambda *a, **kw: None
to_dot_file_enabled = False


def pupper(name, nodes, edges):
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
    printy(f"pupper(name:{name}, nodes:{nodes}, edges:{edges})")

    g = graph.Graph.from_nodes_and_edges(nodes, edges)

    a = "unique value so we don't accidentally use these again"
    b = "unique value so we don't accidentally use these again"

    # assert that it's correctly built
    nep = g.get_all_nodes_and_edge_pairs()
    assert edges == nep.edges, (edges, "^", nep.edges, "=", edges ^ nep.edges)
    assert nodes == nep.nodes, (nodes, "^", nep.nodes, "=", nodes ^ nep.nodes)

    printy(f"g:{g}")

    # x 1. is there a smaller fork/join between the two given nodes? if so, recurse and modify the graph in there
    # x 1.1. there's a smaller fork/join if there's any edge in/out from this graph which we haven't considered

    # 1. is there a smaller join between the two given nodes? if so, recurse and modify the graph in there
    # 1.1. there's a smaller join if there's any edge in/out from this graph which we haven't considered

    def to_dot_file(transposed):
        global to_dot_file_enabled
        if not to_dot_file_enabled:
            return

        global last_file_contents
        nep = g.get_all_nodes_and_edge_pairs()
        if last_file_contents == nep:
            return
        last_file_contents = nep

        t = time.time_ns()
        name2 = name.replace(" ", "_").replace(",", ".")
        transposed_text = "transposed" if transposed else ""
        filename = f"graph-{name2}-{t}-{transposed_text}.dot"
        printy(f"to_dot_file:uniformly-sampled-toposorts/{filename}.png")
        f = open(filename, mode="w")
        f.write("digraph {\n")
        for a in nep.nodes:
            f.write(f"  {a};\n")
        f.write(f"\n")
        for (a, b) in nep.edges:
            f.write(f"  {a} -> {b};\n")
        f.write("}")
        f.close()
        subprocess.run(f"dot -Tpng {filename} >{filename}.png", shell=True)
        os.remove(filename)

    def validate_partial_ordering(transpose):
        for (a, b) in edges:
            if transpose:
                (a,b) = (b,a)
            assert b in g.transitive_children(a), ("broken constraint", a, b, g)

    def handleJoin(join):
        printy(f"handleJoin(join:{join})")
        # sleep(1)
        # 1. find a V shape, if any
        parents = g.incoming(join)
        if len(parents) == 0:
            return None
        elif len(parents) == 1:
            # TODO[fh]: tail call this?
            return handleJoin(list(parents)[0])
        elif len(parents) >= 2:
            # we have our V join, pick out two parents paths to merge
            printy("many parents", join, parents)
            for p1 in parents:
                for p2 in parents:
                    if p1 >= p2:
                        continue
                    handleJoin2(join, p1, p2)
            return

    def walk_while_line(a, banned_nodes):
        res = []
        df = set(g.incoming(a))
        while True:
            if a in banned_nodes:
                return res

            if len(g.outgoing(a)) >= 2:
                res += [a]
                return res
            elif len(df) == 0:
                res += [a]
                return res
            elif len(df) == 1:
                res += [a]
                a = df.pop()
                continue
            elif len(df) >= 2:
                res += [a]
                return res

    def uniform_merge(ax, bx):
        # assuming ax is usually smaller than bx
        if len(ax) > len(bx):
            uniform_merge(bx, ax)

        ax = list(ax)
        bx = list(bx)
        res = []
        while ax != [] or bx != []:
            # 0 1 2
            #        3 4 5
            # 3 + 3
            pos = random.randint(0, len(ax)-1 + len(bx))
            if pos < len(ax):
                a = ax.pop()
                res += [a]
            else:
                b = bx.pop()
                res += [b]
        assert len(ax) == 0 and len(bx) == 0, [pos, ax, bx, res]
        return res

    def handleJoin2(join, a, b):
        aparents = g.transitive_parents(a)
        bparents = g.transitive_parents(b)

        al = walk_while_line(a, set(bparents))
        bl = walk_while_line(b, set(aparents))

        if al == [] or bl == []:
            printy(f"skipping {name} handleJoin2(join:{join}, a:{a}, b:{b}) with al:{al}, bl:{bl}, g:{g}")
            return

        printy(f"handleJoin2(join:{join}, a:{a}, b:{b})")

        merged = uniform_merge(al, bl)

        al_join = al + [join]
        bl_join = bl + [join]
        merged_join = merged + [join]

        head_after = merged_join[0]
        printy(f"al:{al}, bl:{bl}, merged:{merged}, after:{merged + [join]}")
        head_inner = al_join[0] if bl_join[0] == head_after else bl_join[0]
        assert len(set([head_after, head_inner, join])) == 3, [head_after, head_inner, join]

        printy(f"1-head_after:{head_after}, head_inner:{head_inner}, merged:{merged}, g:{g}")

        # move incoming edges from the old two heads to incoming on the new head
        # inner_parents = g.transitive_parents(head_inner)
        # for n in g.incoming(head_inner) - set([head_after]):
        #    if n in inner_parents:
        #        printy("mv", n, g.incoming(head_inner))
        #        g.del_edge(n, head_inner)
        #        g.add_edge(n, head_after)
        # del edges now transitively covered by (n -> head_after) edge
        # if it existed before, it shouldn't exist after
        # should already be covered by above?
        # if head_after in g.outgoing(n):
        #    g.del_edge(n, head_inner)

        printy(f"2-head_after:{head_after}, head_inner:{head_inner}, merged:{merged}, g:{g}")

        # # remove old edges in separate lines
        # al_line = zip(al, al_join[1:])
        # bl_line = zip(bl, bl_join[1:])
        # al_bl_line = list(al_line) + list(bl_line)
        # printy("del", al_bl_line)
        # for (a,b) in al_bl_line:
        #     g.del_edge(a,b)
        #
        # printy(f"3-head_after:{head_after}, head_inner:{head_inner}, merged:{merged}, g:{g}")

        # add in the new line edges
        merged_line = list(zip(merged, merged[1:] + [join]))
        printy("add", merged_line)
        for (a, b) in merged_line:
            g.add_edge(a, b)

        printy(f"4-head_after:{head_after}, head_inner:{head_inner}, merged:{merged}, g:{g}")
        pass

    def handleFork(fork, nexts):
        return functools.reduce(lambda a, b: handleFork2(fork, a, b), nexts)

    def handleFork2(fork, child1, child2):
        printx(f"handleFork2(child1:{child1}, child2:{child2})")
        lca = g.findLCA(child1, child2)
        printx("handleFork2: lca is", lca)
        return mergeV(fork, child1, child2)

    def mergeV(fork, head1, head2):
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

        printx(f"mergeV(head1:{head1}, head2:{head2}, join:{join})")
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

        printx(f"mergeV({head1}, {head2}, join:{join}) -> p1:{p1} p2:{p2}")

        nep = g.get_all_nodes_and_edge_pairs()

        res = uniformly_random(nep.nodes, nep.edges)

        printx("res", res)
        printx("nodes1", g)

        g.zip(nep.edges, res)

        printy("nodes2", g)

    # the core impl

    # data Solution = Line { length :: Int, members :: List NodeId } | MeetJoin { children :: List NodeId, parents :: List NodeId }

    # TODO[fh]: check incoming edges to bail out if either line is not a line? what's the algorithm for that? solve the sub-problem where the join point is the new head, and then backtrack to merging the subproblem into the original problem? probably works.


    for transpose in [False, True]:
        if transpose:
            printy("### TRANSPOSE")
            g.transpose()
        for _ in nodes:
            for node in nodes:
                if len(g.outgoing(node)) >= 2 and False:  ############### DISABLED
                    printx("fork node", node)
                    # m = handleFork(node, set(g.outgoing(node)))

                    # todo[fh]: update outgoing

                    printx("fork merged", node, "g", g)
                if len(g.incoming(node)) >= 2:
                    printy("join node", node)
                    handleJoin(node)
                    printy("join node", node, "done")

                # make sure the modifications we did didn't break any previous constraint
                validate_partial_ordering(transpose)
                to_dot_file(transpose)
        if transpose:
            g.transpose()

    #nep = g.get_all_nodes_and_edge_pairs()
    #assert len(nep.edges) + 1 >= len(nep.nodes), (nep, g)

    printy("returning", g)
    ans = g.toposort_unambiguous_graph()
    ans.reverse()
    printy("returning2", ans)
    return ans


def is_valid_order(constraints):
    def inner(order):
        picked = set()
        available = set(order) - set(map(lambda x: x[1], constraints))
        for o in order:
            if o not in available:
                printy(f"is_valid_order failed on {o} not in {available}, picked:{picked}, order:{order}, constraints:{constraints}")
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


def uniformly_random(name, nodes, edges):
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

def random_and_sort(nodes, edges):
    sorting = list(nodes)
    random.shuffle(sorting)

    g = graph.Graph.from_nodes_and_edges(nodes, edges)
    seen = set()
    while seen != nodes:
        x = sorting[len(seen)]
        if g.incoming(x).issubset(seen):
            seen.add(x)
        else:
            sorting.append(sorting.pop(len(seen)))
    return tuple(sorting)


def check_valid_toposort(f, name, nodes, edges):
    res = f(name, nodes, edges)
    assert res, ("res is", res, nodes, edges)
    assert is_valid_order(edges)(tuple(res)), (name, "Not a valid order...", res, edges)
    return res


def check_randomness(f, name, nodes, edges):
    all_of_them = list_permutations(nodes, edges)
    num_samples = 1000 * len(all_of_them)
    samples = defaultdict(int)
    len_idx = None
    for _ in range(num_samples):
        idx = f(name, nodes, edges)
        if len_idx is not None and len(idx) != len_idx:
            print("idx check failed", len_idx, idx, nodes, edges)
            exit(3)
        len_idx = len(idx)
        samples[tuple(idx)] += 1

    if (len(all_of_them) != len(samples)): print( f"Cannot generate all orders ans:{all_of_them}, given:{list(samples.keys())}")

    expected = num_samples / len(samples)
    variances = []
    for a, b in samples.items():
        # You probably want to use a Beta-distribution here, to see the likelyhood of the distribution being uniform.
        # But this crude test is probably (pun very much intended) good enough.
        if abs(b - expected) > expected * 0.05:
            print(name, f"Outlier! {a}, with {b} but expected ~{expected}")
        variances.append((b - expected) ** 2)

    return sum(variances) ** 0.5, samples


def dooer(name, nodes, edges):
    #check_randomness(uniformly_random, name, nodes, edges)
    check_randomness(pupper, name, nodes, edges)
    #check_valid_toposort(pupper, name, nodes, edges)


print()
print("### Diamond")
print(dooer("Diamond", set(range(3 + 1))
            , set([(0, 1), (0, 2), (1, 3), (2, 3)])
            ))

print()
print("### DoubleSeqDiamond")
print(dooer("DoubleSeqDiamond", set(range(6 + 1))
            , set([(0, 1), (0, 2), (1, 3), (2, 3), (3, 4), (3, 5), (4, 6), (5, 6)])
            ))

print()
print("### DoubleParDiamond")
print(dooer("DoubleParDiamond", set(range(6 + 1))
            , set([(0, 1), (0, 2), (1, 3), (2, 3), (4, 2), (2, 6), (4, 5), (5, 6)])
            ))

print()
print("### free 4")
print(dooer("free 4", set(range(3 + 1))
            , set([])
            ))

print()
print("### line 5")
print(dooer("line 4", set(range(4 + 1))
            , set([(0, 1), (1, 2), (2, 3), (3, 4)])
            ))

print()
print("### First test!")
print(dooer("First test!", set(range(4 + 1))
            , set([(0, 1), (0, 2), (1, 3), (2, 4)])
            ))

print()
print("### Second test!")
print(dooer("Second test!", set(range(6 + 1))
            , set([(0, 1), (1, 2), (1, 3), (0, 4), (4, 5), (5, 6)])
            ))

print()
print("### Third test!")
print(dooer("Third test!", set(range(7 + 1))
            , set([(0, 1), (1, 2), (1, 3), (3, 4), (4, 5), (5, 6), (0, 7)])
            ))

print()
print("### Fourth test!")
print(dooer("Fourth test!", set(range(8 + 1))
            , set([(0, 1), (1, 2), (1, 3), (3, 4), (4, 5), (5, 6), (0, 7)])
            ))

print()
print("### Fifth test!")
print(dooer("Fifth test!", set(range(4 + 1))
                      , set([(0, 1), (0, 2), (1, 3), (2, 3), (3, 4)])
                      ))

## https://bjpcjp.github.io/pdfs/math/topological-sort-ADM.pdf
print()
print("### topo-sort adm example graph, join-only version, skipping the right child if there's two")
print(dooer("topo-sort adm example graph, join-only version, skipping the right child if there's two", set(range(10 + 1)),
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
# print()
# print("### topo-sort adm example graph")
# print(dooer("topo-sort adm example graph", set(range(10 + 1)),
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
# print()
# print("### --- 1 ---")
# for n in range(1, m):
#     print(n)
#     list_permutations( set(chain(range(0, n)))
#                      , set(chain(zip(range(0, n), range(1, n))))
#                      )
#
# print()
# print("### --- 2 ---")
# for n in range(1, m):
#     print(n)
#     list_permutations( set(chain(range(0, n), range(n, 2*n)))
#                      , set(chain(zip(range(0, n), range(1, n)), zip(range(n, 2*n), range(n+1, 2*n))))
#                      )
#
# print()
# print("### --- 3 ---")
# for n in range(1, m):
#     print(n)
#     list_permutations( set(chain(range(0, n), range(n, 2*n), range(2*n, 3*n)))
#                      , set(chain(zip(range(0, n), range(1, n)), zip(range(n, 2*n), range(n+1, 2*n)), zip(range(2*n, 3*n), range(2*n+1, 3*n))))
#                      )

"""
Q: what's the ratio between the number of toposorts if we add an edge `a -> b` vs `b -> a`? Does it relate to the number of transitive edges added in the full closure graph of the ordering? Can we compute that? Is there a similar metric which doesn't change as we go?

- Always choosing the direction of each edge in the same order is perfectly fine, i.e. always starting with adding the same edge but in different directions
- Can we precompute something that then allows us to randomly sample in linear time? Obviously calculating them all and storing them in a list/trie, but is there something else?

- Can we iterate through them all? yes, all perms and then filter
- Perhaps randomly generating an ordering and pushing it towards valid space is a decent idea? more likely to find a match, but unlikely to be uniformly random

# V merge is highly unbalanced atm, e.g. :
Third test! Outlier! (0, 7, 1, 2, 3, 4, 5, 6), with 5846 but expected ~1000.0
Third test! Outlier! (0, 1, 3, 2, 7, 4, 5, 6), with 1434 but expected ~1000.0
Third test! Outlier! (0, 1, 7, 3, 4, 5, 2, 6), with 335 but expected ~1000.0
Third test! Outlier! (0, 1, 3, 4, 5, 6, 7, 2), with 99 but expected ~1000.0
"""