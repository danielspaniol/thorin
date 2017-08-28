#include "thorin/continuation.h"
#include "thorin/world.h"
#include "thorin/transform/mangle.h"
#include "thorin/util/log.h"

#include <limits>

namespace thorin {

static Continuation*   wrap_def(Def2Def&, Def2Def&, const Def*, const FnType*, size_t);
static Continuation* unwrap_def(Def2Def&, Def2Def&, const Def*, const FnType*, size_t);

// Computes the type of the wrapped function
static const Type* wrapped_type(const FnType* fn_type, size_t max_tuple_size) {
    std::vector<const Type*> nops;
    for (auto op : fn_type->ops()) {
        if (auto tuple_type = op->isa<TupleType>()) {
            if (tuple_type->num_ops() <= max_tuple_size) {
                for (auto arg : tuple_type->ops())
                    nops.push_back(arg);
            } else
                nops.push_back(op);
        } else if (auto op_fn_type = op->isa<FnType>()) {
            nops.push_back(wrapped_type(op_fn_type, max_tuple_size));
        } else {
            nops.push_back(op);
        }
    }
    return fn_type->world().fn_type(nops);
}

static Continuation* jump(Continuation* cont, Array<const Def*>& args) {
    cont->jump(args[0], args.skip_front(), args[0]->debug());
    return cont;
}

static Continuation* try_inline(Continuation* cont, Array<const Def*>& args) {
    if (args[0]->isa_continuation()) {
        auto dropped = drop(Call(args));
        cont->jump(dropped->callee(), dropped->args(), args[0]->debug());
    } else {
        jump(cont, args);
    }
    return cont;
}

// Wraps around a def, flattening tuples passed as parameters (dual of unwrap)
static Continuation* wrap_def(Def2Def& wrapped, Def2Def& unwrapped, const Def* old_def, const FnType* new_type, size_t max_tuple_size) {
    // Transform:
    //
    // old_def(a: T, b: (U, V), c: fn (W, (X, Y))):
    //     ...
    //
    // into:
    //
    // new_cont(a: T, b: U, c: V, d: fn (W, X, Y)):
    //     old_def(a, (b, c), unwrap_d)
    //
    //     unwrap_d(a: W, b: (X, Y)):
    //         e = extract(b, 0)
    //         f = extract(b, 1)
    //         d(a, (e, f))

    if (wrapped.contains(old_def)) return wrapped[old_def]->as_continuation();

    auto& world = old_def->world();
    auto old_type = old_def->type()->as<FnType>();
    auto new_cont = world.continuation(new_type, old_def->debug());
    Array<const Def*> call_args(old_type->num_ops() + 1);

    wrapped.emplace(old_def, new_cont);

    for (size_t i = 0, j = 0, e = old_type->num_ops(); i != e; ++i) {
        auto op = old_type->op(i);
        if (auto tuple_type = op->isa<TupleType>()) {
            if (tuple_type->num_ops() <= max_tuple_size) {
                Array<const Def*> tuple_args(tuple_type->num_ops());
                for (size_t k = 0, e = tuple_type->num_ops(); k != e; ++k)
                    tuple_args[k] = new_cont->param(j++);
                call_args[i + 1] = world.tuple(tuple_args);
            } else
                call_args[i + 1] = new_cont->param(j++);
        } else if (auto fn_type = op->isa<FnType>()) {
            auto fn_param = new_cont->param(j++);
            // no need to unwrap if the types are identical
            if (fn_param->type() != op)
                call_args[i + 1] = unwrap_def(wrapped, unwrapped, fn_param, fn_type, max_tuple_size);
            else
                call_args[i + 1] = fn_param;
        } else {
            call_args[i + 1] = new_cont->param(j++);
        }
    }

    call_args[0] = old_def;
    // inline the call, so that the old continuation is eliminated
    return try_inline(new_cont, call_args);
}

// Unwrap a def, flattening tuples passed as arguments (dual of wrap)
static Continuation* unwrap_def(Def2Def& wrapped, Def2Def& unwrapped, const Def* new_def, const FnType* old_type, size_t max_tuple_size) {
    // Transform:
    //
    // new_def(a: T, b: U, c: V, d: fn (W, X, Y)):
    //     ...
    //
    // into:
    //
    // old_cont(a: T, b: (U, V), d: fn (W, (X, Y))):
    //     e = extract(b, 0)
    //     f = extract(b, 1)
    //     new_def(a, e, f, wrap_d)
    //
    //     wrap_d(a: W, b: X, c: Y):
    //         d(a, (b, c))

    if (unwrapped.contains(new_def)) return unwrapped[new_def]->as_continuation();

    auto& world = new_def->world();
    auto new_type = new_def->type()->as<FnType>();
    auto old_cont = world.continuation(old_type, new_def->debug());
    Array<const Def*> call_args(new_type->num_ops() + 1);

    unwrapped.emplace(new_def, old_cont);

    for (size_t i = 0, j = 1, e = old_cont->num_params(); i != e; ++i) {
        auto param = old_cont->param(i);
        if (auto tuple_type = param->type()->isa<TupleType>()) {
            if (tuple_type->num_ops() <= max_tuple_size) {
                for (size_t k = 0, e = tuple_type->num_ops(); k != e; ++k)
                    call_args[j++] = world.extract(param, k);
            } else
                call_args[j++] = param;
        } else if (auto fn_type = param->type()->isa<FnType>()) {
            auto new_fn_type = new_type->op(j - 1)->as<FnType>();
            // no need to wrap if the types are identical
            if (fn_type != new_fn_type)
                call_args[j++] = wrap_def(wrapped, unwrapped, param, new_fn_type, max_tuple_size);
            else
                call_args[j++] = param;
        } else {
            call_args[j++] = param;
        }
    }

    call_args[0] = new_def;
    // we do not inline the call, so that we keep the flattened version around
    return jump(old_cont, call_args);
}

static void flatten_tuples(World& world, size_t max_tuple_size) {
    // flatten tuples passed as arguments to functions
    bool todo = true;

    while (todo) {
        todo = false;

        Def2Def wrapped, unwrapped;
        for (auto cont : world.copy_continuations()) {
            // do not change the signature of intrinsic/external functions
            if (cont->is_intrinsic() || cont->is_external() || is_passed_to_accelerator(cont)) continue;

            auto new_type = wrapped_type(cont->type(), max_tuple_size)->as<FnType>();
            if (new_type == cont->type()) continue;

            // generate a version of that continuation that operates without tuples
            auto new_cont = cont->empty()
                ? world.continuation(new_type, cont->debug())
                : wrap_def(wrapped, unwrapped, cont, new_type, max_tuple_size);
            auto old_cont = unwrap_def(wrapped, unwrapped, new_cont, cont->type(), max_tuple_size);

            // inline call sites of the old continuation
            for (auto use : cont->copy_uses()) {
                auto ucont = use->isa_continuation();
                if (!ucont || use.index() != 0) continue;

                Array<const Def*> args(ucont->num_args() + 1);
                for (size_t i = 0, e = ucont->num_args(); i != e; ++i) args[i + 1] = ucont->arg(i);
                args[0] = old_cont;
                // inline the unwrapped continuation
                try_inline(ucont, args);

                todo = true;
            }

            // replaces other uses so that the old version can be eliminated
            cont->replace(old_cont);

            if (cont->empty()) {
                // empty continuations are either intrinsics or extern functions
                new_cont->intrinsic() = cont->intrinsic();
                new_cont->cc() = cont->cc();
                if (cont->is_external()) new_cont->make_external();
            }

            DLOG("flattened: {}", cont);
        }

        world.cleanup();
    }
}

void flatten_tuples(World& world) {
    flatten_tuples(world, std::numeric_limits<size_t>::max());
}

}