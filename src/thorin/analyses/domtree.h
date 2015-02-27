#ifndef THORIN_ANALYSES_DOMTREE_H
#define THORIN_ANALYSES_DOMTREE_H

#include "thorin/lambda.h"
#include "thorin/analyses/cfg.h"
#include "thorin/util/array.h"

namespace thorin {

class CFNode;
template<bool> class CFG;

/**
 * @brief A Dominance Tree.
 *
 * The template parameter @p forward determines 
 * whether a regular dominance tree (@c true) or a post-dominance tree (@c false) should be constructed.
 * This template parameter is associated with @p CFG's @c forward parameter.
 */
template<bool forward>
class DomTreeBase {
public:
    class Node {
    public:
        explicit Node(const CFNode* cf_node)
            : cf_node_(cf_node)
        {}

        const CFNode* cf_node() const { return cf_node_; }
        Lambda* lambda() const;
        const Node* idom() const { return idom_; }
        const std::vector<const Node*>& children() const { return children_; }
        size_t num_children() const { return children_.size(); }
        bool entry() const { return idom_ == this; }
        int depth() const { return depth_; }
        size_t max_index() const;
        void dump() const;

    private:
        const CFNode* cf_node_;
        mutable const Node* idom_ = nullptr;
        mutable AutoVector<const Node*> children_;
        mutable int depth_;
        mutable size_t max_index_;

        template<bool> friend class DomTreeBase;
    };

    DomTreeBase(const DomTreeBase&) = delete;
    DomTreeBase& operator= (DomTreeBase) = delete;

    explicit DomTreeBase(const CFG<forward>& cfg)
        : cfg_(cfg)
        , nodes_(cfg)
    {
        create();
    }

    const CFG<forward>& cfg() const { return cfg_; }
    size_t index(const Node* n) const { return cfg().index(n->cf_node()); }
    const Node* root() const { return root_; }
    /// Returns the least common ancestor of @p i and @p j.
    const Node* lca(const Node* i, const Node* j) const;
    const Node* lookup(const CFNode* n) const { return nodes_[n]; }
    void dump() const { root()->dump(); }

private:
    void create();
    size_t postprocess(const Node* n, int depth);

    const CFG<forward>& cfg_;
    AutoPtr<const Node> root_;
    typename CFG<forward>::template Map<const Node*> nodes_;
};

typedef DomTreeBase<true>  DomTree;
typedef DomTreeBase<false> PostDomTree;
typedef DomTree::Node      DomNode;
typedef PostDomTree::Node  PostDomNode;

}

#endif
