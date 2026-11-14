#include <rstd/test/gtest.hpp>
import rstd;
import rstd.test;
import ligraph;

using namespace rstd::prelude;

auto main(int argc, char** argv) -> int {
    rstd::env::args_init(argc, argv);
    return rstd::test::run_registered().to_primitive();
}

auto diamond() -> Vec<Vec<usize>> {
    Vec<Vec<usize>> graph;
    graph.resize(usize(5), Vec<usize>::make());
    graph[usize()].push(usize(1));
    graph[usize()].push(usize(2));
    graph[usize(1)].push(usize(3));
    graph[usize(2)].push(usize(3));
    return graph;
}

TEST(Graph, OrdersAndSearchWorkspace) {
    auto                   graph = diamond();
    auto                   view  = ligraph::adjacency_view(graph.as_slice());
    ligraph::TopoWorkspace topo;
    auto                   order = ligraph::toposort_min(view, topo).unwrap();
    EXPECT_EQ(order.len(), usize(5));
    for (usize i; i < order.len(); ++i) EXPECT_EQ(order[i], i);
    ligraph::SearchWorkspace search;
    EXPECT_TRUE(ligraph::has_path(view, usize(), usize(3), search).unwrap());
    EXPECT_FALSE(ligraph::has_path(view, usize(3), usize(), search).unwrap());
    EXPECT_TRUE(ligraph::has_path(view, usize(3), usize(3), search).unwrap());
    EXPECT_TRUE(ligraph::has_path(view, usize(5), usize(), search).is_err());
    ligraph::DfsWorkspace dfs;
    Vec<usize>            roots;
    roots.push(usize());
    auto dependencies = ligraph::dependency_order(view, roots.as_slice(), dfs).unwrap();
    EXPECT_EQ(dependencies.len(), usize(4));
    EXPECT_EQ(dependencies[usize()], usize(3));
    EXPECT_EQ(dependencies[usize(1)], usize(1));
    EXPECT_EQ(dependencies[usize(2)], usize(2));
    EXPECT_EQ(dependencies[usize(3)], usize());
    EXPECT_EQ(ligraph::toposort(view, dfs).unwrap().len(), usize(5));
}

TEST(Graph, IteratorOrderAndComposition) {
    auto       graph = diamond();
    Vec<usize> roots;
    roots.push(usize());
    roots.push(usize());
    auto breadth = ligraph::bfs(ligraph::adjacency_view(graph.as_slice()), roots.as_slice())
                       .unwrap()
                       .map([](auto item) {
                           return rstd::move(item).unwrap();
                       })
                       .collect<Vec<usize>>();
    EXPECT_EQ(breadth.len(), usize(4));
    for (usize i; i < breadth.len(); ++i) EXPECT_EQ(breadth[i], i);
    auto depth = ligraph::dfs(ligraph::adjacency_view(graph.as_slice()), roots.as_slice())
                     .unwrap()
                     .map([](auto item) {
                         return rstd::move(item).unwrap();
                     })
                     .collect<Vec<usize>>();
    EXPECT_EQ(depth.len(), usize(4));
    EXPECT_EQ(depth[usize()], usize());
    EXPECT_EQ(depth[usize(1)], usize(1));
    EXPECT_EQ(depth[usize(2)], usize(3));
    EXPECT_EQ(depth[usize(3)], usize(2));
    roots.push(usize(4));
    auto multiple = ligraph::bfs(ligraph::adjacency_view(graph.as_slice()), roots.as_slice())
                        .unwrap()
                        .map([](auto item) {
                            return rstd::move(item).unwrap();
                        })
                        .collect<Vec<usize>>();
    EXPECT_EQ(multiple.len(), usize(5));
    EXPECT_EQ(multiple[usize()], usize());
    EXPECT_EQ(multiple[usize(1)], usize(4));
    EXPECT_EQ(multiple[usize(4)], usize(3));
}

TEST(Graph, CyclesInvalidEdgesAndRecovery) {
    auto graph = diamond();
    graph[usize(3)].push(usize(1));
    ligraph::TopoWorkspace topo;
    auto failed = ligraph::toposort_min(ligraph::adjacency_view(graph.as_slice()), topo);
    ASSERT_TRUE(failed.is_err());
    auto error = rstd::move(failed).unwrap_err();
    EXPECT_EQ(error.kind, ligraph::ErrorKind::Cycle);
    EXPECT_EQ(error.cycle.len(), usize(3));
    EXPECT_EQ(error.cycle[usize()], error.cycle[usize(2)]);
    graph[usize(3)].clear();
    graph[usize(4)].push(usize(10));
    auto invalid = ligraph::toposort_min(ligraph::adjacency_view(graph.as_slice()), topo);
    ASSERT_TRUE(invalid.is_err());
    EXPECT_EQ(invalid.unwrap_err().kind, ligraph::ErrorKind::InvalidNode);
    graph.clear();
    EXPECT_TRUE(
        ligraph::toposort_min(ligraph::adjacency_view(graph.as_slice()), topo).unwrap().is_empty());
    ligraph::DfsWorkspace dfs;
    ligraph::SccWorkspace scc;
    Vec<usize>            roots;
    auto                  empty = ligraph::adjacency_view(graph.as_slice());
    EXPECT_TRUE(ligraph::toposort(empty, dfs).unwrap().is_empty());
    EXPECT_TRUE(ligraph::strongly_connected_components(empty, scc).unwrap().is_empty());
    EXPECT_TRUE(ligraph::bfs(empty, roots.as_slice()).unwrap().next().is_none());
    EXPECT_TRUE(ligraph::dfs(empty, roots.as_slice()).unwrap().next().is_none());
}

TEST(Graph, StronglyConnectedComponentsAndDeepChain) {
    Vec<Vec<usize>> graph;
    graph.resize(usize(10000), Vec<usize>::make());
    for (usize i; i + usize(1) < graph.len(); ++i) graph[i].push(i + usize(1));
    ligraph::DfsWorkspace dfs;
    auto order = ligraph::toposort(ligraph::adjacency_view(graph.as_slice()), dfs).unwrap();
    EXPECT_EQ(order.len(), graph.len());
    EXPECT_EQ(order[usize()], usize());
    ligraph::SccWorkspace scc;
    auto                  groups =
        ligraph::strongly_connected_components(ligraph::adjacency_view(graph.as_slice()), scc)
            .unwrap();
    EXPECT_EQ(groups.len(), graph.len());
    graph[usize(9999)].push(usize());
    auto cycle =
        ligraph::strongly_connected_components(ligraph::adjacency_view(graph.as_slice()), scc)
            .unwrap();
    EXPECT_EQ(cycle.len(), usize(1));
    EXPECT_EQ(cycle[usize()].len(), graph.len());
}

TEST(Graph, TraversalErrorsAndEarlyStop) {
    Vec<Vec<usize>> graph;
    graph.resize(usize(2), Vec<usize>::make());
    graph[usize()].push(usize(1));
    graph[usize(1)].push(usize(9));
    Vec<usize> roots;
    roots.push(usize());
    auto view    = ligraph::adjacency_view(graph.as_slice());
    auto breadth = ligraph::bfs(view, roots.as_slice()).unwrap();
    EXPECT_TRUE(breadth.next().unwrap().is_ok());
    EXPECT_TRUE(breadth.next().unwrap().is_err());
    EXPECT_TRUE(breadth.next().is_none());
    EXPECT_TRUE(breadth.next().is_none());
    auto depth = ligraph::dfs(view, roots.as_slice()).unwrap();
    EXPECT_TRUE(depth.next().unwrap().is_ok());
    EXPECT_TRUE(depth.next().unwrap().is_ok());
    EXPECT_TRUE(depth.next().unwrap().is_err());
    EXPECT_TRUE(depth.next().is_none());
    roots[usize()] = usize(7);
    EXPECT_TRUE(ligraph::bfs(view, roots.as_slice()).is_err());
    EXPECT_TRUE(ligraph::dfs(view, roots.as_slice()).is_err());
    roots[usize()]  = usize();
    int  expansions = 0;
    auto counted    = ligraph::indexed_view(graph.len(), [&](usize node) {
        ++expansions;
        return graph[node].iter().copied();
    });
    auto first      = ligraph::dfs(counted, roots.as_slice())
                          .unwrap()
                          .take(usize(1))
                          .collect<Vec<ligraph::Result<usize>>>();
    EXPECT_EQ(first.len(), usize(1));
    EXPECT_EQ(expansions, 1);
    ligraph::DfsWorkspace ordering;
    EXPECT_TRUE(ligraph::dependency_order(view, roots.as_slice(), ordering).is_err());
    graph[usize(1)].clear();
    graph[usize()].push(usize(1));
    ligraph::TopoWorkspace topology;
    EXPECT_EQ(ligraph::toposort_min(view, topology).unwrap().len(), usize(2));
    EXPECT_EQ(ligraph::dependency_order(view, roots.as_slice(), ordering).unwrap().len(), usize(2));
}

TEST(Graph, SmallGraphsMatchReachabilityAndPartitions) {
    ligraph::SearchWorkspace search;
    ligraph::DfsWorkspace    ordering;
    ligraph::TopoWorkspace   minimum;
    ligraph::SccWorkspace    scc;
    for (unsigned mask = 0; mask < 512; ++mask) {
        Vec<Vec<usize>> graph;
        graph.resize(usize(3), Vec<usize>::make());
        bool reached[3][3] {};
        for (unsigned a = 0; a < 3; ++a)
            for (unsigned b = 0; b < 3; ++b)
                if (mask & (1u << (a * 3 + b))) {
                    graph[usize(a)].push(usize(b));
                    reached[a][b] = true;
                }
        for (unsigned k = 0; k < 3; ++k)
            for (unsigned a = 0; a < 3; ++a)
                for (unsigned b = 0; b < 3; ++b) reached[a][b] |= reached[a][k] && reached[k][b];
        bool cyclic = reached[0][0] || reached[1][1] || reached[2][2];
        auto view   = ligraph::adjacency_view(graph.as_slice());
        for (unsigned a = 0; a < 3; ++a)
            for (unsigned b = 0; b < 3; ++b)
                EXPECT_EQ(ligraph::has_path(view, usize(a), usize(b), search).unwrap(),
                          a == b || reached[a][b]);
        auto sorted   = ligraph::toposort(view, ordering);
        auto smallest = ligraph::toposort_min(view, minimum);
        EXPECT_EQ(sorted.is_err(), cyclic);
        EXPECT_EQ(smallest.is_err(), cyclic);
        if (! cyclic) {
            usize positions[3] {};
            for (usize i; i < sorted->len(); ++i) positions[(*sorted)[i].to_primitive()] = i;
            for (unsigned a = 0; a < 3; ++a)
                for (auto b : graph[usize(a)])
                    EXPECT_TRUE(positions[a] < positions[b.to_primitive()]);
            bool emitted[3] {};
            for (auto current : *smallest) {
                for (unsigned a = 0; a < current.to_primitive(); ++a) {
                    if (emitted[a]) continue;
                    bool ready = true;
                    for (unsigned b = 0; b < 3; ++b)
                        if (! emitted[b] && (mask & (1u << (b * 3 + a)))) ready = false;
                    EXPECT_FALSE(ready);
                }
                emitted[current.to_primitive()] = true;
            }
        } else {
            auto error = rstd::move(smallest).unwrap_err();
            EXPECT_EQ(error.kind, ligraph::ErrorKind::Cycle);
            ASSERT_TRUE(error.cycle.len() >= usize(2));
            EXPECT_EQ(error.cycle[usize()], *error.cycle.last().unwrap());
            for (usize i(1); i < error.cycle.len(); ++i) {
                auto a = error.cycle[i - usize(1)].to_primitive();
                auto b = error.cycle[i].to_primitive();
                EXPECT_TRUE((mask & (1u << (a * 3 + b))) != 0);
            }
        }
        auto     components = ligraph::strongly_connected_components(view, scc).unwrap();
        unsigned labels[3] {};
        bool     seen[3] {};
        for (usize label; label < components.len(); ++label)
            for (auto node : components[label]) {
                EXPECT_FALSE(seen[node.to_primitive()]);
                seen[node.to_primitive()]   = true;
                labels[node.to_primitive()] = static_cast<unsigned>(label.to_primitive());
            }
        for (unsigned a = 0; a < 3; ++a) {
            EXPECT_TRUE(seen[a]);
            for (unsigned b = 0; b < 3; ++b)
                EXPECT_EQ(labels[a] == labels[b], a == b || (reached[a][b] && reached[b][a]));
        }
    }
}

struct InlineGraph {
    usize edge { 1 };
    auto  node_count() const -> usize { return usize(2); }
    auto  neighbors(usize node) const {
        return rstd::iter::from_fn(
            [pointer = &edge, done = node != usize()]() mutable -> Option<usize> {
                if (done) return None();
                done = true;
                return Some(usize(*pointer));
            });
    }
};

TEST(Graph, DfsMoveKeepsActiveNeighborViewsAlive) {
    Vec<usize> roots;
    roots.push(usize());
    auto traversal = ligraph::dfs(InlineGraph {}, roots.as_slice()).unwrap();
    EXPECT_EQ(traversal.next().unwrap().unwrap(), usize());
    auto moved = rstd::move(traversal);
    EXPECT_EQ(moved.next().unwrap().unwrap(), usize(1));
    EXPECT_TRUE(moved.next().is_none());
}

struct BorrowedNode {
    usize       slot;
    unsigned    generation;
    friend auto operator==(BorrowedNode, BorrowedNode) -> bool = default;
};

TEST(Graph, TypedTraversalPreservesGenerationsAndCycles) {
    auto graph = ligraph::traversal_view<BorrowedNode, usize>(
        [](BorrowedNode) -> Result<empty, usize> {
            return Ok(empty {});
        },
        [](BorrowedNode node) {
            auto neighbors =
                rstd::iter::once(BorrowedNode { node.slot, node.generation == 1 ? 2u : 1u });
            return Result<decltype(neighbors), usize>(Ok(rstd::move(neighbors)));
        });
    Vec<BorrowedNode> roots;
    roots.push(BorrowedNode { usize(), 1 });
    auto visited = Vec<BorrowedNode>::make();
    auto visit   = [&visited](BorrowedNode node) {
        if (visited.iter().any([&](auto item) {
                return *item == node;
            }))
            return false;
        visited.push(BorrowedNode(node));
        return true;
    };
    auto breadth = ligraph::bfs(graph, roots.as_slice(), visit).unwrap();
    EXPECT_EQ(breadth.next().unwrap().unwrap().generation, 1u);
    EXPECT_EQ(breadth.next().unwrap().unwrap().generation, 2u);
    EXPECT_TRUE(breadth.next().is_none());
    EXPECT_EQ(visited.len(), usize(2));
    visited.clear();
    auto depth = ligraph::dfs(graph, roots.as_slice(), visit).unwrap();
    EXPECT_EQ(depth.next().unwrap().unwrap().generation, 1u);
    auto moved = rstd::move(depth);
    EXPECT_EQ(moved.next().unwrap().unwrap().generation, 2u);
    EXPECT_TRUE(moved.next().is_none());
}

struct TraversalFailure {
    Box<usize> payload;
};

TEST(Graph, FallibleTraversalTransfersOwnedErrorsAndStops) {
    for (bool breadth : { false, true }) {
        Option<TraversalFailure> failure = Some(TraversalFailure { Box<usize>::make(usize(77)) });
        auto                     graph   = ligraph::traversal_view<usize, TraversalFailure>(
            [](usize) -> Result<empty, TraversalFailure> {
                return Ok(empty {});
            },
            [&failure](
                usize node) -> Result<decltype(rstd::iter::once(usize())), TraversalFailure> {
                if (node == usize(1)) return Err(failure.take().unwrap());
                return Ok(rstd::iter::once(usize(1)));
            });
        Vec<usize> roots;
        roots.push(usize());
        auto check = [&](auto traversal) {
            EXPECT_EQ(traversal.next().unwrap().unwrap(), usize());
            auto failed = traversal.next().unwrap();
            ASSERT_TRUE(failed.is_err());
            EXPECT_EQ(*failed.unwrap_err().payload, usize(77));
            EXPECT_TRUE(failure.is_none());
            EXPECT_TRUE(traversal.next().is_none());
            EXPECT_TRUE(traversal.next().is_none());
        };
        if (breadth)
            check(ligraph::bfs(graph, roots.as_slice(), ligraph::DenseVisitMap(usize(2))).unwrap());
        else
            check(ligraph::dfs(graph, roots.as_slice(), ligraph::DenseVisitMap(usize(2))).unwrap());
    }
    auto rejected = ligraph::traversal_view<usize, usize>(
        [](usize node) -> Result<empty, usize> {
            return Err(usize(node));
        },
        [](usize) -> Result<decltype(rstd::iter::empty<usize>()), usize> {
            return Ok(rstd::iter::empty<usize>());
        });
    Vec<usize> roots;
    roots.push(usize(9));
    EXPECT_EQ(
        ligraph::bfs(rejected, roots.as_slice(), ligraph::DenseVisitMap(usize())).unwrap_err(),
        usize(9));
    EXPECT_EQ(
        ligraph::dfs(rejected, roots.as_slice(), ligraph::DenseVisitMap(usize())).unwrap_err(),
        usize(9));
}
