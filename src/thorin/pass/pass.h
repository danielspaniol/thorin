#ifndef THORIN_PASS_PASS_H
#define THORIN_PASS_PASS_H

#include <map>

#include "thorin/world.h"

namespace thorin {

class PassMan;
static constexpr uint32_t No_Undo = -1;

/**
 * All Pass%es that want to be registered in the @p PassMan must implement this interface.
 * * Directly inherit from this class if your pass doesn't need state.
 * * Inherit from @p Pass using CRTP if you do need state.
 */
class PassBase {
public:
    PassBase(PassMan& man, size_t index, const std::string& name)
        : man_(man)
        , index_(index)
        , name_(name)
    {}
    virtual ~PassBase() {}

    /// @name getters
    //@{
    PassMan& man() { return man_; }
    size_t index() const { return index_; }
    const std::string& name() const { return name_; }
    World& world();
    ///@}
    /// @name hooks for the PassMan
    //@{
    /// Invoked just before @em nom%inal is rewritten.
    virtual void enter([[maybe_unused]] Def* nom) {}

    /**
     * Inspects a @p nom%inal when first encountering it during @p rewrite%ing @p cur_nom.
     * Returns a potentially new @em nominal.
     */
    virtual Def* inspect([[maybe_unused]] Def* cur_nom, Def* nom) { return nom; }

    /**
     * Rewrites a @em structural @p def within @p cur_nom.
     * Returns the replacement.
     */
    virtual const Def* rewrite(Def* cur_nom, const Def* def) = 0;

    /**
     * Invoked after the @p PassMan has finished @p rewrite%ing @p cur_nom to analyze @p def.
     * Return @p No_Undo or the state to roll back to.
     */
    virtual uint32_t analyze([[maybe_unused]] Def* cur_nom, [[maybe_unused]] const Def* def) { return No_Undo; }
    ///@}
    /// @name mangage state - dummy implementations here
    //@{
    virtual void* alloc() { return nullptr; }
    virtual void dealloc(void*) {}
    //@}

private:
    PassMan& man_;
    size_t index_;
    std::string name_;
};

/**
 * An optimizer that combines several optimizations in an optimal way.
 * This is loosely based upon:
 * "Composing dataflow analyses and transformations" by Lerner, Grove, Chambers.
 */
class PassMan {
public:
    typedef std::unique_ptr<PassBase> PassPtr;

    PassMan(World& world)
        : world_(world)
    {}

    /// @name create and run
    //@{
    /// Add @p Pass to this @p PassMan.
    template<class P, class... Args>
    PassMan& create(Args... args) {
        passes_.emplace_back(std::make_unique<P>(*this, passes_.size()), std::forward<Args>(args)...);
        return *this;
    }
    void run(); ///< Run all registered @p Pass%es on the whole @p world.
    //@}
    /// @name getters
    //@{
    World& world() const { return world_; }
    size_t num_passes() const { return passes_.size(); }
    template<class T = Def> T* cur_nom() const { return cur_nom()->template as<T>(); }
    //@}

private:
    struct State {
        State() = default;
        State(const State&) = delete;
        State(State&&) = delete;
        State& operator=(State) = delete;

        State(const std::vector<PassPtr>& passes)
            : passes(passes.data())
            , data(passes.size(), [&](auto i) { return passes[i]->alloc(); })
        {}
        State(const State& prev, const std::vector<PassPtr>& passes)
            : map(prev.map)
            , analyzed(prev.analyzed)
            , passes(passes.data())
            , data(passes.size(), [&](auto i) { return passes[i]->alloc(); })
        {}
        ~State() {
            for (size_t i = 0, e = data.size(); i != e; ++i)
                passes[i]->dealloc(data[i]);
        }

        std::map<ReplArray, Def2Def> map;
        DefSet analyzed;
        NomSet noms;
        const PassPtr* passes;
        Array<void*> data;
    };

    void new_state() { states_.emplace_back(cur_state(), passes_); }
    State& cur_state() { assert(!states_.empty()); return states_.back(); }
    void enter(Def*);
    uint32_t rewrite(Def*);
    const Def* rewrite(Def*, const Def*, std::pair<const ReplArray, Def2Def>&);
    uint32_t analyze(Def*, const Def*);

    World& world_;
    std::vector<PassPtr> passes_;
    std::deque<State> states_;
};

inline World& PassBase::world() { return man().world(); }

/// Inherit from this class using CRTP if you do need a Pass with a state.
template<class P>
class Pass : public PassBase {
public:
    Pass(PassMan& man, size_t index, const std::string& name)
        : PassBase(man, index, name)
    {}

    /// @name state-related getters
    //@{
    auto& states() { return man().states_; }
    auto& state(size_t i) { return *static_cast<typename P::State*>(states()[i].data[index()]); }
    auto& cur_state() { assert(!states().empty()); return *static_cast<typename P::State*>(states().back().data[index()]); }
    //@}
    /// @name recursive search in the state stack
    //@{
    /// Searches states from back to front in the map @p M for @p key using @p init if nothing is found.
    template<class M>
    auto& get(const typename M::key_type& key, typename M::mapped_type&& init) {
        auto& map = std::get<M>(cur_state());
        if (auto i = map.find(key); i != map.end())
            return i->second;

        return std::get<M>(cur_state()).emplace(key, std::move(init)).first->second;
    }
    /// Same as above but uses the default constructor as init.
    template<class M>
    auto& get(const typename M::key_type& key) { return get<M>(key, typename M::mapped_type()); }
    //@}
    /// @name alloc/dealloc state
    //@{
    void* alloc() override { return states().empty() ? new typename P::State() : new typename P::State(cur_state()); }
    void dealloc(void* state) override { delete static_cast<typename P::State*>(state); }
    //@}
};

}

#endif
