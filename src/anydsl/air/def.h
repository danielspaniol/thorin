#ifndef ANYDSL_DEF_H
#define ANYDSL_DEF_H

#include <string>
#include <vector>

#include <boost/cstdint.hpp>
#include <boost/unordered_set.hpp>

#include "anydsl/air/airnode.h"

namespace anydsl {

//------------------------------------------------------------------------------

class Lambda;
class Type;
class World;
class Use;
typedef boost::unordered_set<Use*> Uses;

//------------------------------------------------------------------------------

class Def : public AIRNode {
protected:

    Def(IndexKind index, Type* type, const std::string& debug)
        : AIRNode(index, debug) 
        , type_(type)
    {}

public:

    virtual ~Def() { anydsl_assert(uses_.empty(), "there are still uses pointing to this def"); }

    /**
     * Manually adds given \p Use object to the list of uses of this \p Def.
     * use->def() must already point to \p this .
     */
    void registerUse(Use* use);

    /**
     * Manually removes given \p Use object from the list of uses of this \p Def.
     * use->def() must point to \p this , but should be unset right after the call to this function
     */
    void unregisterUse(Use* use);

    const Uses& uses() const { return uses_; }

    Type* type() { return type_; }
    const Type* type() const { return type_; }

    World& world() const;

    virtual uint64_t hash() const = 0;

private:

    Type* type_;
    Uses uses_;
};

//------------------------------------------------------------------------------

class Value : public Def {
protected:

    Value(IndexKind index, Type* type, const std::string& debug = "")
        : Def(index, type, debug)
    {}
};

typedef std::vector<Value*> ValueList;

//------------------------------------------------------------------------------

class Param : public Value {
public:

    Param(Lambda* parent, Type* type, const std::string& debug = "")
        : Value(Index_Param, type, debug)
        , parent_(parent)
    {}

    const Lambda* parent() const { return parent_; }

private:

    Lambda* parent_;
};

//------------------------------------------------------------------------------

class PrimOp : public Value {
public:

    PrimOpKind primOpKind() const { return (PrimOpKind) index(); }

    bool compare(PrimOp* other) const;

protected:

    PrimOp(IndexKind index, Type* type, const std::string& debug)
        : Value(index, type, debug)
    {}
};

//------------------------------------------------------------------------------

} // namespace anydsl

#endif // ANYDSL_DEF_H
