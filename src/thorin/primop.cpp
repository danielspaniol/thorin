#include "thorin/primop.h"

#include "thorin/config.h"
#include "thorin/world.h"
#include "thorin/util/array.h"

namespace thorin {

//------------------------------------------------------------------------------

/*
 * constructors
 */

Cmp::Cmp(CmpTag tag, const Def* lhs, const Def* rhs, Debug dbg)
    : BinOp((NodeTag) tag, lhs->world().type_bool(), lhs, rhs, dbg)
{}

Known::Known(const Def* def, Debug dbg)
    : PrimOp(Node_Known, def->world().type_bool(), {def}, dbg)
{}

SizeOf::SizeOf(const Def* def, Debug dbg)
    : PrimOp(Node_SizeOf, def->world().type_qs32(), {def}, dbg)
{}

Assembly::Assembly(const Def* type, Defs inputs, std::string asm_template, ArrayRef<std::string> output_constraints, ArrayRef<std::string> input_constraints, ArrayRef<std::string> clobbers, Flags flags, Debug dbg)
    : MemOp(Node_Assembly, type, inputs, dbg)
{

    new (&extra<Extra>()) Extra();
    extra<Extra>().asm_template_ = asm_template;
    extra<Extra>().output_constraints_ = output_constraints;
    extra<Extra>().input_constraints_ = input_constraints;
    extra<Extra>().clobbers_ = clobbers;
    extra<Extra>().flags_ = flags;
}

Assembly::~Assembly() {
    (&extra<Extra>())->~Extra();
}

//------------------------------------------------------------------------------

/*
 * equal
 */

bool Slot::equal(const Def* other) const { return this == other; }

//------------------------------------------------------------------------------

/*
 * rebuild
 */

// do not use any of PrimOp's type getters - during import we need to derive types from 't' in the new world 'to'

const Def* ArithOp::rebuild(World& to, const Def*  , Defs ops) const { return to.arithop(arithop_tag(), ops[0], ops[1], debug()); }
const Def* Bitcast::rebuild(World& to, const Def* t, Defs ops) const { return to.bitcast(t, ops[0], debug()); }
const Def* Cast   ::rebuild(World& to, const Def* t, Defs ops) const { return to.cast(t, ops[0], debug()); }
const Def* Cmp    ::rebuild(World& to, const Def*  , Defs ops) const { return to.cmp(cmp_tag(), ops[0], ops[1], debug()); }
const Def* Enter  ::rebuild(World& to, const Def*  , Defs ops) const { return to.enter(ops[0], debug()); }
const Def* Global ::rebuild(World& to, const Def*  , Defs ops) const { return to.global(ops[0], is_mutable(), debug()); }
const Def* Hlt    ::rebuild(World& to, const Def*  , Defs ops) const { return to.hlt(ops[0], debug()); }
const Def* Known  ::rebuild(World& to, const Def*  , Defs ops) const { return to.known(ops[0], debug()); }
const Def* Run    ::rebuild(World& to, const Def*  , Defs ops) const { return to.run(ops[0], debug()); }
const Def* LEA    ::rebuild(World& to, const Def*  , Defs ops) const { return to.lea(ops[0], ops[1], debug()); }
const Def* Load   ::rebuild(World& to, const Def*  , Defs ops) const { return to.load(ops[0], ops[1], debug()); }
const Def* Lit    ::rebuild(World& to, const Def* t, Defs    ) const { return to.lit(t, box(), debug()); }
const Def* Select ::rebuild(World& to, const Def*  , Defs ops) const { return to.select(ops[0], ops[1], ops[2], debug()); }
const Def* SizeOf ::rebuild(World& to, const Def*  , Defs ops) const { return to.size_of(ops[0]->type(), debug()); }
const Def* Slot   ::rebuild(World& to, const Def* t, Defs ops) const { return to.slot(t->as<PtrType>()->pointee(), ops[0], debug()); }
const Def* Store  ::rebuild(World& to, const Def*  , Defs ops) const { return to.store(ops[0], ops[1], ops[2], debug()); }
const Def* Variant::rebuild(World& to, const Def* t, Defs ops) const { return to.variant(t->as<VariantType>(), ops[0], debug()); }

const Def* Alloc::rebuild(World& to, const Def* t, Defs ops) const {
    return to.alloc(t->as<Sigma>()->op(1)->as<PtrType>()->pointee(), ops[0], ops[1], debug());
}

const Def* Assembly::rebuild(World& to, const Def* t, Defs ops) const {
    return to.assembly(t, ops, asm_template(), output_constraints(), input_constraints(), clobbers(), flags(), debug());
}

const Def* DefiniteArray::rebuild(World& to, const Def* t, Defs ops) const {
    return to.definite_array(t->as<DefiniteArrayType>()->elem_type(), ops, debug());
}

const Def* IndefiniteArray::rebuild(World& to, const Def* t, Defs ops) const {
    return to.indefinite_array(t->as<IndefiniteArrayType>()->elem_type(), ops[0], debug());
}

//------------------------------------------------------------------------------

/*
 * op_name
 */

const char* Def::op_name() const {
    switch (tag()) {
#define THORIN_NODE(op, abbr) case Node_##op: return #abbr;
#include "thorin/tables/nodetable.h"
        default: THORIN_UNREACHABLE;
    }
}

const char* ArithOp::op_name() const {
    switch (tag()) {
#define THORIN_ARITHOP(op) case ArithOp_##op: return #op;
#include "thorin/tables/arithoptable.h"
        default: THORIN_UNREACHABLE;
    }
}

const char* Cmp::op_name() const {
    switch (tag()) {
#define THORIN_CMP(op) case Cmp_##op: return #op;
#include "thorin/tables/cmptable.h"
        default: THORIN_UNREACHABLE;
    }
}

const char* Global::op_name() const { return is_mutable() ? "global_mutable" : "global_immutable"; }

//------------------------------------------------------------------------------

/*
 * stream
 */

std::ostream& PrimOp::stream(std::ostream& os) const {
    if (is_const(this)) {
        if (num_ops() == 0)
            return streamf(os, "{} {}", op_name(), type());
        else
            return streamf(os, "({} {} {})", type(), op_name(), stream_list(ops(), [&](const Def* def) { os << def; }));
    } else
        return os << unique_name();
}

std::ostream& Lit::stream(std::ostream& os) const {
    os << type() << ' ';
    if (auto prim_type = type()->isa<PrimType>()) {
        auto tag = prim_type->primtype_tag();

        // print i8 as ints
        switch (tag) {
            case PrimType_qs8: return os << (int) box().get_qs8();
            case PrimType_ps8: return os << (int) box().get_ps8();
            case PrimType_qu8: return os << (unsigned) box().get_qu8();
            case PrimType_pu8: return os << (unsigned) box().get_pu8();
            default:
                switch (tag) {
#define THORIN_ALL_TYPE(T, M) case PrimType_##T: return os << box().get_##M();
#include "thorin/tables/primtypetable.h"
                    default: THORIN_UNREACHABLE;
                }
        }
    } else {
        return os << box().get_u64();
    }
}

std::ostream& Global::stream(std::ostream& os) const { return os << unique_name(); }

std::ostream& Assembly::stream_assignment(std::ostream& os) const {
    streamf(os, "{} {} = asm \"{}\"", type(), unique_name(), asm_template());
    stream_list(os, output_constraints(), [&](const auto& output_constraint) { os << output_constraint; }, " : (", ")");
    stream_list(os,  input_constraints(), [&](const auto&  input_constraint) { os <<  input_constraint; }, " : (", ")");
    stream_list(os,           clobbers(), [&](const auto&           clobber) { os <<           clobber; }, " : (", ") ");
    return stream_list(os,         ops(), [&](const Def*                def) { os <<               def; },    "(", ")") << endl;
}

//------------------------------------------------------------------------------

/*
 * misc
 */

std::string DefiniteArray::as_string() const {
    std::string res;
    for (auto op : ops()) {
        auto c = op->as<Lit>()->box().get_pu8();
        if (!c) break;
        res += c;
    }
    return res;
}

const Def* PrimOp::out(size_t i) const {
    assert(i == 0 || i < type()->as<Sigma>()->num_ops());
    return world().extract(this, i, debug());
}

//------------------------------------------------------------------------------

}
