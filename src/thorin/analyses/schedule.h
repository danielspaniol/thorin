#ifndef THORIN_ANALYSES_SCHEDULE_H
#define THORIN_ANALYSES_SCHEDULE_H

#include "thorin/analyses/cfg.h"

namespace thorin {

class PrimOp;

class Schedule {
public:
    enum Kind { Early, Late, Smart };

    class Block {
    public:
        Block(const Block&) = delete;
        Block& operator= (Block) = delete;

        Block() {}

        const CFNode* node() const { return node_; }
        Lambda* lambda() const { return node()->lambda(); }
        ArrayRef<const PrimOp*> primops() const { return primops_; }
        size_t index() const { return index_; }

        typedef ArrayRef<const PrimOp*>::const_iterator const_iterator;
        const_iterator begin() const { return primops().begin(); }
        const_iterator end() const { return primops().end(); }

    private:
        const CFNode* node_;
        std::vector<const PrimOp*> primops_;
        size_t index_;

        friend class Schedule;
        friend class Scheduler;
    };

    template<class Value>
    using Map = IndexMap<Schedule, const Block&, Value>;
    using Set = IndexSet<Schedule, const Block&>;

    Schedule(const Schedule&) = delete;
    Schedule& operator= (Schedule) = delete;

    Schedule(Schedule&& other)
        : scope_(std::move(other.scope_))
        , indices_(std::move(other.indices_))
        , blocks_(std::move(other.blocks_))
        , kind_(std::move(other.kind_))
    {}
    Schedule(const Scope&, Kind = Smart);

    Kind kind() const { return kind_; }
    const Scope& scope() const { return scope_; }
    const CFA& cfa() const { return scope().cfa(); }
    const F_CFG& cfg() const { return scope().f_cfg(); }
    ArrayRef<Block> blocks() const { return blocks_; }
    size_t size() const { return blocks_.size(); }
    const Block& operator [] (const CFNode* n) const { return blocks_[indices_[n]]; }
    static size_t index(const Block& block) { return block.index(); }
    void verify();

    typedef ArrayRef<const Block>::const_iterator const_iterator;
    const_iterator begin() const { return blocks().begin(); }
    const_iterator end() const { return blocks().end(); }

private:
    Block& operator [] (const CFNode* n) { return blocks_[indices_[n]]; }
    void block_schedule();

    const Scope& scope_;
    F_CFG::Map<size_t> indices_;
    Array<Block> blocks_;
    Kind kind_;

    friend class Scheduler;
};

inline Schedule schedule(const Scope& scope, Schedule::Kind kind = Schedule::Smart) {
    return Schedule(scope, kind);
}

}

#endif
