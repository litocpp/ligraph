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

template<IndexedGraph G>
class Bfs : public rstd::DefaultInClass<Bfs<G>, rstd::iter::Iterator> {
    G                                     graph_;
    Vec<bool>                             seen_;
    ::alloc::collections::VecDeque<usize> pending_;
    bool                                  done_ {};
    explicit Bfs(G graph): graph_(rstd::move(graph)) {}
    auto view() const -> const G& { return graph_; }

public:
    using Item                         = Result<usize>;
    static constexpr bool PROVEN_FUSED = true;
    static auto           make(G graph, slice<usize> roots) -> Result<Bfs> {
        Bfs  result(rstd::move(graph));
        auto count = result.view().node_count();
        result.seen_.resize(count, false);
        for (auto root : roots) {
            if (root >= count) return Err(Error { ErrorKind::InvalidNode, root, {} });
            if (! result.seen_[root]) {
                result.seen_[root] = true;
                result.pending_.push_back(usize(root));
            }
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
        auto neighbors = view().neighbors(*node);
        while (auto next = neighbors.next()) {
            if (*next >= seen_.len()) {
                done_ = true;
                return Some(Item(Err(Error { ErrorKind::InvalidNode, *next, {} })));
            }
            if (! seen_[*next]) {
                seen_[*next] = true;
                pending_.push_back(*next);
            }
        }
        return Some(Item(Ok(*node)));
    }
};

template<IndexedGraph G>
auto bfs(G graph, slice<usize> roots) -> Result<Bfs<G>> {
    return Bfs<G>::make(rstd::move(graph), roots);
}

template<IndexedGraph G>
class Dfs : public rstd::DefaultInClass<Dfs<G>, rstd::iter::Iterator> {
    using Neighbors = decltype(rstd::mtp::declval<const G&>().neighbors(usize()));
    struct Frame {
        Neighbors neighbors;
    };
    // Active neighbor iterators may borrow the view itself across traversal moves.
    Box<G>     graph_;
    Vec<bool>  seen_;
    Vec<usize> roots_;
    usize      root_ {};
    Vec<Frame> frames_;
    bool       done_ {};
    explicit Dfs(G graph): graph_(Box<G>::make(rstd::move(graph))) {}
    auto view() const -> const G& { return *graph_; }

public:
    using Item                         = Result<usize>;
    static constexpr bool PROVEN_FUSED = true;
    static auto           make(G graph, slice<usize> roots) -> Result<Dfs> {
        Dfs  result(rstd::move(graph));
        auto count = result.view().node_count();
        result.seen_.resize(count, false);
        for (auto root : roots) {
            if (root >= count) return Err(Error { ErrorKind::InvalidNode, root, {} });
            result.roots_.push(usize(root));
        }
        return Ok(rstd::move(result));
    }
    auto next() -> Option<Item> {
        if (done_) return None();
        for (;;) {
            Option<usize> node;
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
                node = Some(usize(roots_[root_++]));
            }
            if (*node >= seen_.len()) {
                done_ = true;
                return Some(Item(Err(Error { ErrorKind::InvalidNode, *node, {} })));
            }
            if (seen_[*node]) continue;
            seen_[*node] = true;
            frames_.push({ view().neighbors(*node) });
            return Some(Item(Ok(*node)));
        }
    }
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
