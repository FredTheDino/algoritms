# I couldn't find a graph data structure that had the basic features I wanted, i.e. precomputed incoming and outgoing sets

from dataclasses import dataclass
from collections import OrderedDict


@dataclass
class NodeInfo:
    label: str
    outgoing: set
    incoming: set


@dataclass
class LcaPaths:
    path1: list
    path2: list
    edges: list
    lca: int

@dataclass
class NodesAndEdges:
    nodes: list
    edges: list


class Graph():
    def __init__(self):
        self.nodes = {}
        self.node_labels = {}
        self.edge_labels = {}

    @staticmethod
    def from_nodes_and_edges(nodes, edges):
        g = Graph()

        for n in nodes:
            g.add_node(n)

        for (a, b) in edges:
            g.add_edge(a, b)

        return g


    def __repr__(self):
        out = OrderedDict()
        inc = OrderedDict()
        for k in self.nodes:
            out[k] = self.outgoing(k)
            inc[k] = self.incoming(k)

        return f"Graph<out={out}, inc={inc}>"

    def add_node(self, a, label=None):
        if a not in self.nodes:
            self.nodes[a] = NodeInfo(
                label=label or a,
                outgoing=set(),
                incoming=set()
            )

    def del_node(self, a):
        for o in self.outgoing[a]:
            self.del_edge(a, o)
        for i in self.incoming[a]:
            self.del_edge(i, a)
        del self.nodes[a]

    def add_edge(self, a, b, label=None):
        assert a != b, (a, b, self, "no self-edges for now; they're not in the problem we're solving, so they're indications of bugs instead")
        self.add_node(a, None)
        self.add_node(b, None)
        self.nodes[a].outgoing.add(b)
        self.nodes[b].incoming.add(a)
        self.edge_labels[(a, b)] = label
        #print(f"add_edge({a} -> {b}) into {self}")

    def del_edge(self, a, b):
        self.add_node(a, None)
        self.add_node(b, None)

        self.nodes[a].outgoing.discard(b)
        self.nodes[b].incoming.discard(a)
        if (a, b) in self.edge_labels:
            del self.edge_labels[(a, b)]

    def outgoing(self, a):
        return set(self.nodes[a].outgoing)

    def incoming(self, a):
        assert a in self.nodes, ("a not in self.nodes", a, self)
        return set(self.nodes[a].incoming)

    def node_label(self, a):
        return self.nodes[a].label

    def edge_label(self, a, b):
        return self.edge_labels[(a, b)]

    ######

    def transitive_parents(self, start):
        ans = []
        q = [start]
        seen = set()
        while q != []:
            e = q.pop()
            if e in seen:
                continue
            seen.add(e)
            q += self.incoming(e)
            ans += [e]
        return ans

    def transitive_children(self, start):
        ans = []
        q = [start]
        seen = set()
        while q != []:
            e = q.pop()
            if e in seen:
                continue
            seen.add(e)
            q += self.outgoing(e)
            ans += [e]
        return ans

    def get_all_nodes_and_edge_pairs(self):
        nodes = []
        edges = []
        for a in self.nodes:
            nodes += [a]
            for o in self.outgoing(a):
                edges += [(a, o)]
        return NodesAndEdges(nodes=set(nodes), edges=set(edges))

    def findLCA(self, head1, head2):
        # TODO[fh]: find lowest common ancestor using range min query, O(h) time in O(1) space, "You can turn LCA problem to RMQ??1 and then use Farach Colton Bender algorithm, which solves RMQ??1 in O(n) preprocessing and O(1) for query."

        r1 = self.transitive_parents(head1)
        r2 = self.transitive_parents(head2)
        assert r1[-1] == r2[-1]
        #print("transitive_parents(head1)", r1)
        #print("transitive_parents(head2)", r2)

        for r1x in r1:
            if r1x in r2:
                return r1x

    def findLCA_with_paths(self, head1, head2):
        # TODO[fh]: find lowest common ancestor using range min query, O(h) time in O(1) space, "You can turn LCA problem to RMQ??1 and then use Farach Colton Bender algorithm, which solves RMQ??1 in O(n) preprocessing and O(1) for query." I'm not confident the current impl is even correct.

        r1 = self.transitive_parents(head1)
        r2 = self.transitive_parents(head2)
        assert r1[-1] == r2[-1]
        ###print("transitive_parents(head1)", r1)
        #print("transitive_parents(head2)", r2)

        lca = None
        for r1x in r1:
            if r1x in r2:
                lca = r1x
                break

        path1 = []
        for n1 in r1:
            if n1 == lca:
                break
            path1 += [n1]

        path2 = []
        for n2 in r2:
            if n2 == lca:
                break
            path2 += [n2]

        #print(f"path1:{path1}, path2:{path2}")

        edges = []
        for p1 in range(len(path1)):
            if (p1+1) < len(path1):
                edges += [(path1[p1], path1[p1+1])]
            else:
                edges += [(path1[p1], lca)]

        for p2 in range(len(path2)):
            if (p2+1) < len(path2):
                edges += [(path2[p2], path2[p2+1])]
            else:
                edges += [(path2[p2], lca)]

        return LcaPaths(path1=r1, path2=r2, lca=lca, edges=edges)

    def zip(self, old_edges, new_order):
        new_edges = []
        for ni in range(len(new_order)-1):
            new_edges += [(new_order[ni], new_order[ni+1])]
        #print(f"zip old_edges:{old_edges}, new_edges:{new_edges}, new_order:{new_order}")

        for (a,b) in old_edges:
            self.del_edge(a,b)
        for (a,b) in new_edges:
            self.add_edge(a,b)

    def toposort_unambiguous_graph(self):
        nep = self.get_all_nodes_and_edge_pairs()
        #assert len(nep.edges) + 1 >= len(nep.nodes)

        res = []
        seen = set()
        def walker(n):
            if n in seen:
                return
            for i in self.incoming(n):
                if i not in seen:
                    return
            seen.add(n)

            for o in self.outgoing(n):
                walker(o)
            res.append(n)

        for n in self.nodes:
            walker(n)
        assert len(res) == len(nep.nodes), [res, nep, self]
        return res

    def transpose(self):
        for n in self.nodes:
            inc = self.nodes[n].incoming
            out = self.nodes[n].outgoing
            # TODO[fh]: we don't transpose edge labels here; should we?
            self.nodes[n].incoming = out
            self.nodes[n].outgoing = inc
