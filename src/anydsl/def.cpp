#include "anydsl/def.h"

#include <typeinfo>

#include "anydsl/lambda.h"
#include "anydsl/primop.h"
#include "anydsl/type.h"
#include "anydsl/util/for_all.h"

namespace anydsl {


//------------------------------------------------------------------------------

Def::~Def() { 
    for (size_t i = 0, e = numOps(); i != e; ++i)
        if (ops_[i])
            ops_[i]->unregisterUse(i, this);

    for_all (use, uses_) {
        size_t i = use.index();
        anydsl_assert(use.def()->ops()[i] == this, "use points to incorrect def");
        use.def()->delOp(i);
    }

    delete[] ops_;
}

void Def::registerUse(size_t i, const Def* def) const {
    Use use(i, def);
    anydsl_assert(uses_.find(use) == uses_.end(), "already in use set");
    uses_.insert(use);
}

void Def::unregisterUse(size_t i, const Def* def) const {
    Use use(i, def);
    anydsl_assert(uses_.find(use) != uses_.end(), "must be inside the use set");
    uses_.erase(use);
}

World& Def::world() const { 
    if (type_)
        return type_->world(); 
    else 
        return as<Type>()->world();
}

bool Value::equal(const Value* other) const {
    if (this->indexKind() != other->indexKind())
        return false;

    if (this->numOps() != other->numOps())
        return false;

    bool result = true;
    for (size_t i = 0, e = numOps(); i != e && result; ++i)
        result &= this->ops_[i] == other->ops_[i];

    return result;
}

size_t Value::hash() const {
    size_t seed = 0;

    boost::hash_combine(seed, indexKind());
    boost::hash_combine(seed, numOps());

    for (size_t i = 0, e = numOps(); i != e; ++i)
        boost::hash_combine(seed, ops_[i]);

    return seed;
}

//------------------------------------------------------------------------------

Param::Param(const Type* type, const Lambda* lambda, size_t index)
    : Value(Index_Param, type, 1)
    , index_(index)
{
    setOp(0, lambda);
}

const Lambda* Param::lambda() const {
    return ops_[0]->as<Lambda>();
}

//------------------------------------------------------------------------------

} // namespace anydsl
