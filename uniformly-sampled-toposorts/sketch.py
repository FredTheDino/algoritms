# A small sketch program used to test the algoritm.
# Quickly sketched together to try to disprove it.
# The algoritm can be implemented a lot faster if you use some pointers,
# but this is good enough to test it out. :)

from itertools import permutations, chain
import random
from collections import defaultdict

nodes = set([0, 1, 2, 3, 5])
edges = set([(0, 1), (0, 2), (1, 3), (2, 5)])

def is_valid_order(constraints):
    locked = set(map(lambda x: x[1], constraints))
    def inner(order):
        available = set(order) - locked
        for o in order:
            if o not in available:
                return False
            for (a, b) in constraints:
                if a == o:
                    available.add(b)
        return True
    return inner


def list_permutations(nodes, edges):
    return list(filter(is_valid_order(edges), permutations(nodes)))

def size(node, edges):
    # This can be speed up substatially
    return 1 + sum(size(b, edges) for (a, b) in edges if a == node)

def uniformly_random(nodes, edges):
    possible = {}

    def weighted_random(p):
        # This can be done a lot faster

        # NOTE[ed]: If you change this to `random.randint(0, sum(p.values()))` and `n <= 0`, the algoritm does not work at all.
        n = random.randint(0, sum(p.values()) - 1)
        for (a, w) in p.items():
            n -= w
            if n < 0:
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
    return order

def check_randomness(nodes, edges):
    num_samples = 100000
    samples = defaultdict(int)
    for _ in range(num_samples):
        samples[uniformly_random(nodes, edges)] += 1

    assert (len(list_permutations(nodes, edges)) == len(samples)), "Cannot generate all orders"

    expected = num_samples / len(samples)
    variances = []
    for a, b in samples.items():
        # You probably want to use a Beta-distribution here, to see the likelyhood of the distribution being uniform.
        # But this crude test is probably (pun very much intended) good enough.
        if abs(b - expected) > expected * 0.05:
            print(f"Outlier! {a}, with {b} but expected ~{expected}")
        variances.append((b - expected) ** 2)

    return sum(variances) ** 0.5, samples

print("First test!")
print(check_randomness( set(range(5+1))
                      , set([(0, 1), (0, 2), (1, 3), (2, 5)])
                      ))
print("PASS")

print("Second test!")
print(check_randomness( set(range(6+1))
                      , set([(0, 1), (1, 2), (1, 3), (0, 4), (4, 5), (5, 6)])
                      ))
print("PASS")

print("Third test!")
print(check_randomness( set(range(7+1))
                      , set([(0, 1), (1, 2), (1, 3), (3, 4), (4, 5), (5, 6), (0, 7)])
                      ))
print("PASS")

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


