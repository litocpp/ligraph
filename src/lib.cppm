export module ligraph;
export import rstd.alloc;

using namespace rstd::prelude;
using ::alloc::vec::Vec;
using ::alloc::boxed::Box;

export namespace ligraph
{

enum class ErrorKind
{
    InvalidNode,
    Cycle
};

struct Error {
    ErrorKind  kind;
    usize      node;
    Vec<usize> cycle;
};

template<class T>
using Result = rstd::Result<T, Error>;

// Indices are dense. The graph and its topology must outlive borrowed views and
// traversal.
template<class G>
concept IndexedGraph = requires(const G& graph, usize node) {
    { graph.node_count() } -> rstd::mtp::same_as<usize>;
    requires rstd::iter::has_next<decltype(graph.neighbors(node))>;
    requires rstd::mtp::same_as<typename decltype(graph.neighbors(node))::Item, usize>;
};

template<class F>
class IndexedView {
    usize count_;
    F     neighbors_;

public:
    IndexedView(usize count, F neighbors): count_(count), neighbors_(rstd::move(neighbors)) {}
    auto node_count() const -> usize { return count_; }
    auto neighbors(usize node) const { return neighbors_(node); }
};

template<class F>
    requires IndexedGraph<IndexedView<F>>
auto indexed_view(usize count, F neighbors) -> IndexedView<F> {
    return { count, rstd::move(neighbors) };
}

inline auto adjacency_view(slice<Vec<usize>> adjacency) {
    return indexed_view(adjacency.len(), [adjacency](usize node) {
        return adjacency[node].iter().copied();
    });
}

class SearchWorkspace {
    Vec<bool>  seen_;
    Vec<usize> pending_;

public:
    template<IndexedGraph G>
    auto has_path(const G& graph, usize from, usize to) -> Result<bool> {
        auto count = graph.node_count();
        if (from >= count) return Err(Error { ErrorKind::InvalidNode, from, {} });
        if (to >= count) return Err(Error { ErrorKind::InvalidNode, to, {} });
        seen_.clear();
        seen_.resize(count, false);
        pending_.clear();
        pending_.push(usize(from));
        seen_[from] = true;
        while (auto current = pending_.pop()) {
            if (*current == to) return Ok(true);
            auto neighbors = graph.neighbors(*current);
            while (auto next = neighbors.next()) {
                if (*next >= count) return Err(Error { ErrorKind::InvalidNode, *next, {} });
                if (! seen_[*next]) {
                    seen_[*next] = true;
                    pending_.push(usize(*next));
                }
            }
        }
        return Ok(false);
    }
};

template<IndexedGraph G>
auto has_path(const G& graph, usize from, usize to, SearchWorkspace& workspace) -> Result<bool> {
    return workspace.has_path(graph, from, to);
}

class DfsWorkspace {
    Vec<u8>    colors_;
    Vec<usize> parents_;

    auto cycle(usize from, usize to) const -> Error {
        Vec<usize> reverse;
        reverse.push(usize(to));
        for (auto node = from; node != to; node = parents_[node]) reverse.push(usize(node));
        reverse.push(usize(to));
        return { ErrorKind::Cycle,
                 to,
                 reverse.iter().rev().copied().template collect<Vec<usize>>() };
    }

public:
    // Edges point to dependencies; result follows DFS completion order, including
    // root order.
    template<IndexedGraph G>
    auto dependency_order(const G& graph, slice<usize> roots) -> Result<Vec<usize>> {
        auto count = graph.node_count();
        colors_.clear();
        colors_.resize(count, u8());
        parents_.clear();
        parents_.resize(count, usize());
        using Neighbors = decltype(graph.neighbors(usize()));
        struct Frame {
            usize     node;
            Neighbors neighbors;
        };
        Vec<Frame> frames;
        Vec<usize> order;
        for (auto root : roots) {
            if (root >= count) return Err(Error { ErrorKind::InvalidNode, root, {} });
            if (colors_[root] == u8(2)) continue;
            colors_[root] = u8(1);
            frames.push({ root, graph.neighbors(root) });
            while (! frames.is_empty()) {
                auto node = frames.last().unwrap()->node;
                auto next = frames.last_mut().unwrap().get_mut().neighbors.next();
                if (! next) {
                    colors_[node] = u8(2);
                    order.push(usize(node));
                    frames.pop();
                    continue;
                }
                if (*next >= count) return Err(Error { ErrorKind::InvalidNode, *next, {} });
                if (colors_[*next] == u8(1)) return Err(cycle(node, *next));
                if (colors_[*next] == u8(2)) continue;
                parents_[*next] = node;
                colors_[*next]  = u8(1);
                frames.push({ *next, graph.neighbors(*next) });
            }
        }
        return Ok(rstd::move(order));
    }
};

template<IndexedGraph G>
auto dependency_order(const G& graph, slice<usize> roots, DfsWorkspace& workspace)
    -> Result<Vec<usize>> {
    return workspace.dependency_order(graph, roots);
}

// For u -> v, u appears before v. Disconnected vertices are included.
template<IndexedGraph G>
auto toposort(const G& graph, DfsWorkspace& workspace) -> Result<Vec<usize>> {
    Vec<usize> roots;
    for (usize i; i < graph.node_count(); ++i) roots.push(usize(i));
    auto result = dependency_order(graph, roots.as_slice(), workspace);
    if (result.is_err()) return Err(rstd::move(result).unwrap_err());
    return Ok(result->iter().rev().copied().template collect<Vec<usize>>());
}

class TopoWorkspace {
    Vec<usize>                            incoming_;
    ::alloc::collections::BTreeSet<usize> ready_;
    DfsWorkspace                          cycle_;

public:
    // Always emits the smallest currently ready index, not just initially sorted
    // roots.
    template<IndexedGraph G>
    auto sort_min(const G& graph) -> Result<Vec<usize>> {
        auto count = graph.node_count();
        incoming_.clear();
        incoming_.resize(count, usize());
        ready_.clear();
        for (usize node; node < count; ++node) {
            auto neighbors = graph.neighbors(node);
            while (auto next = neighbors.next()) {
                if (*next >= count) return Err(Error { ErrorKind::InvalidNode, *next, {} });
                ++incoming_[*next];
            }
        }
        for (usize node; node < count; ++node)
            if (incoming_[node] == usize()) ready_.insert(usize(node));
        Vec<usize> order;
        while (auto current = ready_.pop_first()) {
            order.push(usize(*current));
            auto neighbors = graph.neighbors(*current);
            while (auto next = neighbors.next())
                if (--incoming_[*next] == usize()) ready_.insert(*next);
        }
        if (order.len() != count) return toposort(graph, cycle_);
        return Ok(rstd::move(order));
    }
};

template<IndexedGraph G>
auto toposort_min(const G& graph, TopoWorkspace& workspace) -> Result<Vec<usize>> {
    return workspace.sort_min(graph);
}

template<class G>
concept TraversalGraph = requires(const G& graph, typename G::NodeId node) {
    typename G::Error;
    typename G::Neighbors;
    requires rstd::mtp::init<typename G::NodeId, const typename G::NodeId&>;
    requires rstd::iter::has_next<typename G::Neighbors>;
    requires rstd::mtp::same_as<typename G::Neighbors::Item, typename G::NodeId>;
    { graph.check_node(node) } -> rstd::mtp::same_as<rstd::Result<empty, typename G::Error>>;
    {
        graph.neighbors(node)
    } -> rstd::mtp::same_as<rstd::Result<typename G::Neighbors, typename G::Error>>;
};

template<class N, class E, class Check, class Next>
class TraversalView {
    Check check_;
    Next  next_;

public:
    using NodeId = N;
    using Error  = E;
    using Neighbors =
        typename decltype(rstd::mtp::declval<const Next&>()(rstd::mtp::declval<N>()))::value_type;
    TraversalView(Check check, Next next): check_(rstd::move(check)), next_(rstd::move(next)) {}
    auto check_node(N node) const -> rstd::Result<empty, E> { return check_(node); }
    auto neighbors(N node) const -> rstd::Result<Neighbors, E> { return next_(node); }
};

template<class N, class E, class Check, class Next>
    requires TraversalGraph<TraversalView<N, E, Check, Next>>
auto traversal_view(Check check, Next next) -> TraversalView<N, E, Check, Next> {
    return { rstd::move(check), rstd::move(next) };
}

// The visit callable is invoked only after check_node succeeds. True means newly visited.
template<class Visit, class G>
concept VisitMapFor = TraversalGraph<G> && requires(Visit& visit, typename G::NodeId node) {
    { visit(node) } -> rstd::mtp::same_as<bool>;
};

template<TraversalGraph G, VisitMapFor<G> Visit>
class TryBfs : public rstd::DefaultInClass<TryBfs<G, Visit>, rstd::iter::Iterator> {
    using Node  = typename G::NodeId;
    using Error = typename G::Error;
    G                                    graph_;
    Visit                                visit_;
    ::alloc::collections::VecDeque<Node> pending_;
    bool                                 done_ {};
    TryBfs(G graph, Visit visit): graph_(rstd::move(graph)), visit_(rstd::move(visit)) {}
    auto view() const -> const G& { return graph_; }

public:
    using Item                         = rstd::Result<Node, Error>;
    static constexpr bool PROVEN_FUSED = true;
    static auto make(G graph, slice<Node> roots, Visit visit) -> rstd::Result<TryBfs, Error> {
        TryBfs result(rstd::move(graph), rstd::move(visit));
        for (auto root : roots) {
            auto checked = result.view().check_node(root);
            if (checked.is_err()) return Err(rstd::move(checked).unwrap_err());
            if (result.visit_(root)) result.pending_.push_back(Node(root));
        }
        return Ok(rstd::move(result));
    }
    auto next() -> Option<Item> {
        if (done_) return None();
        auto node = pending_.pop_front();
        if (! node) {
            done_ = true;
            return None();
        }
        auto expanded = view().neighbors(*node);
        if (expanded.is_err()) {
            done_ = true;
            return Some(Item(Err(rstd::move(expanded).unwrap_err())));
        }
        auto neighbors = rstd::move(expanded).unwrap();
        while (auto next = neighbors.next()) {
            auto checked = view().check_node(*next);
            if (checked.is_err()) {
                done_ = true;
                return Some(Item(Err(rstd::move(checked).unwrap_err())));
            }
            if (visit_(*next)) pending_.push_back(Node(*next));
        }
        return Some(Item(Ok(Node(*node))));
    }
};

template<TraversalGraph G, VisitMapFor<G> Visit>
auto bfs(G graph, slice<typename G::NodeId> roots, Visit visit)
    -> rstd::Result<TryBfs<G, Visit>, typename G::Error> {
    return TryBfs<G, Visit>::make(rstd::move(graph), roots, rstd::move(visit));
}

template<TraversalGraph G, VisitMapFor<G> Visit>
class TryDfs : public rstd::DefaultInClass<TryDfs<G, Visit>, rstd::iter::Iterator> {
    using Node  = typename G::NodeId;
    using Error = typename G::Error;
    struct Frame {
        typename G::Neighbors neighbors;
    };
    // Active neighbor iterators may borrow the view itself across traversal moves.
    Box<G>     graph_;
    Visit      visit_;
    Vec<Node>  roots_;
    usize      root_ {};
    Vec<Frame> frames_;
    bool       done_ {};
    TryDfs(G graph, Visit visit)
        : graph_(Box<G>::make(rstd::move(graph))), visit_(rstd::move(visit)) {}
    auto view() const -> const G& { return *graph_; }

public:
    using Item                         = rstd::Result<Node, Error>;
    static constexpr bool PROVEN_FUSED = true;
    static auto make(G graph, slice<Node> roots, Visit visit) -> rstd::Result<TryDfs, Error> {
        TryDfs result(rstd::move(graph), rstd::move(visit));
        for (auto root : roots) {
            auto checked = result.view().check_node(root);
            if (checked.is_err()) return Err(rstd::move(checked).unwrap_err());
            result.roots_.push(Node(root));
        }
        return Ok(rstd::move(result));
    }
    auto next() -> Option<Item> {
        if (done_) return None();
        for (;;) {
            Option<Node> node;
            if (! frames_.is_empty()) {
                node = frames_.last_mut().unwrap().get_mut().neighbors.next();
                if (! node) {
                    frames_.pop();
                    continue;
                }
            } else {
                if (root_ == roots_.len()) {
                    done_ = true;
                    return None();
                }
                node = Some(Node(roots_[root_++]));
            }
            auto checked = view().check_node(*node);
            if (checked.is_err()) {
                done_ = true;
                return Some(Item(Err(rstd::move(checked).unwrap_err())));
            }
            if (! visit_(*node)) continue;
            auto expanded = view().neighbors(*node);
            if (expanded.is_err()) {
                done_ = true;
                return Some(Item(Err(rstd::move(expanded).unwrap_err())));
            }
            frames_.push({ rstd::move(expanded).unwrap() });
            return Some(Item(Ok(Node(*node))));
        }
    }
};

template<TraversalGraph G, VisitMapFor<G> Visit>
auto dfs(G graph, slice<typename G::NodeId> roots, Visit visit)
    -> rstd::Result<TryDfs<G, Visit>, typename G::Error> {
    return TryDfs<G, Visit>::make(rstd::move(graph), roots, rstd::move(visit));
}

class DenseVisitMap {
    Vec<bool> seen_;

public:
    explicit DenseVisitMap(usize count) { seen_.resize(count, false); }
    auto operator()(usize node) -> bool {
        if (seen_[node]) return false;
        seen_[node] = true;
        return true;
    }
};

template<IndexedGraph G>
class CheckedIndexedGraph {
    G graph_;

public:
    using NodeId    = usize;
    using Error     = ligraph::Error;
    using Neighbors = decltype(rstd::mtp::declval<const G&>().neighbors(usize()));
    explicit CheckedIndexedGraph(G graph): graph_(rstd::move(graph)) {}
    auto check_node(usize node) const -> Result<empty> {
        if (node >= graph_.node_count()) return Err(Error { ErrorKind::InvalidNode, node, {} });
        return Ok(empty {});
    }
    auto neighbors(usize node) const -> Result<Neighbors> { return Ok(graph_.neighbors(node)); }
};

template<IndexedGraph G>
class Bfs : public rstd::DefaultInClass<Bfs<G>, rstd::iter::Iterator> {
    using Inner = TryBfs<CheckedIndexedGraph<G>, DenseVisitMap>;
    Inner inner_;
    explicit Bfs(Inner inner): inner_(rstd::move(inner)) {}

public:
    using Item                         = Result<usize>;
    static constexpr bool PROVEN_FUSED = true;
    static auto           make(G graph, slice<usize> roots) -> Result<Bfs> {
        auto count = static_cast<const G&>(graph).node_count();
        auto traversal =
            Inner::make(CheckedIndexedGraph<G>(rstd::move(graph)), roots, DenseVisitMap(count));
        if (traversal.is_err()) return Err(rstd::move(traversal).unwrap_err());
        return Ok(Bfs(rstd::move(traversal).unwrap()));
    }
    auto next() -> Option<Item> { return inner_.next(); }
};

template<IndexedGraph G>
auto bfs(G graph, slice<usize> roots) -> Result<Bfs<G>> {
    return Bfs<G>::make(rstd::move(graph), roots);
}

template<IndexedGraph G>
class Dfs : public rstd::DefaultInClass<Dfs<G>, rstd::iter::Iterator> {
    using Inner = TryDfs<CheckedIndexedGraph<G>, DenseVisitMap>;
    Inner inner_;
    explicit Dfs(Inner inner): inner_(rstd::move(inner)) {}

public:
    using Item                         = Result<usize>;
    static constexpr bool PROVEN_FUSED = true;
    static auto           make(G graph, slice<usize> roots) -> Result<Dfs> {
        auto count = static_cast<const G&>(graph).node_count();
        auto traversal =
            Inner::make(CheckedIndexedGraph<G>(rstd::move(graph)), roots, DenseVisitMap(count));
        if (traversal.is_err()) return Err(rstd::move(traversal).unwrap_err());
        return Ok(Dfs(rstd::move(traversal).unwrap()));
    }
    auto next() -> Option<Item> { return inner_.next(); }
};

template<IndexedGraph G>
auto dfs(G graph, slice<usize> roots) -> Result<Dfs<G>> {
    return Dfs<G>::make(rstd::move(graph), roots);
}

class SccWorkspace {
    Vec<usize> indices_, low_, stack_;
    Vec<bool>  active_;

public:
    // Components are emitted in completion order; members retain DFS stack order.
    template<IndexedGraph G>
    auto components(const G& graph) -> Result<Vec<Vec<usize>>> {
        auto count = graph.node_count();
        indices_.clear();
        indices_.resize(count, count);
        low_.clear();
        low_.resize(count, usize());
        active_.clear();
        active_.resize(count, false);
        stack_.clear();
        using Neighbors = decltype(graph.neighbors(usize()));
        struct Frame {
            usize     node;
            Neighbors neighbors;
        };
        Vec<Frame>      frames;
        Vec<Vec<usize>> output;
        usize           sequence;
        const auto      enter = [&](usize node) {
            indices_[node] = sequence;
            low_[node]     = sequence++;
            active_[node]  = true;
            stack_.push(usize(node));
            frames.push({ node, graph.neighbors(node) });
        };
        for (usize root; root < count; ++root) {
            if (indices_[root] != count) continue;
            enter(root);
            while (! frames.is_empty()) {
                auto node = frames.last().unwrap()->node;
                auto next = frames.last_mut().unwrap().get_mut().neighbors.next();
                if (next) {
                    if (*next >= count) return Err(Error { ErrorKind::InvalidNode, *next, {} });
                    if (indices_[*next] == count)
                        enter(*next);
                    else if (active_[*next])
                        low_[node] = rstd::cmp::min(low_[node], indices_[*next]);
                    continue;
                }
                frames.pop();
                if (low_[node] == indices_[node]) {
                    Vec<usize> component;
                    for (;;) {
                        auto member     = stack_.pop().unwrap();
                        active_[member] = false;
                        component.push(usize(member));
                        if (member == node) break;
                    }
                    output.push(rstd::move(component));
                }
                if (auto parent = frames.last())
                    low_[parent->get().node] = rstd::cmp::min(low_[parent->get().node], low_[node]);
            }
        }
        return Ok(rstd::move(output));
    }
};

template<IndexedGraph G>
auto strongly_connected_components(const G& graph, SccWorkspace& workspace)
    -> Result<Vec<Vec<usize>>> {
    return workspace.components(graph);
}

} // namespace ligraph
