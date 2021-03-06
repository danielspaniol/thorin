set(THORIN_SOURCES
    alpha_equiv.cpp
    alpha_equiv.h
    def.cpp
    def.h
    error.cpp
    error.h
    normalize.cpp
    normalize.h
    rewrite.cpp
    rewrite.h
    flatten.cpp
    flatten.h
    stream.cpp
    tables.h
    util.cpp
    util.h
    world.cpp
    world.h
    analyses/cfg.cpp
    analyses/cfg.h
    analyses/domfrontier.cpp
    analyses/domfrontier.h
    analyses/domtree.cpp
    analyses/domtree.h
    analyses/free_defs.cpp
    analyses/free_defs.h
    analyses/looptree.cpp
    analyses/looptree.h
    analyses/schedule.cpp
    analyses/schedule.h
    analyses/scope.cpp
    analyses/scope.h
    analyses/verify.cpp
    analyses/verify.h
    be/c.cpp
    be/c.h
    pass/auto_diff.cpp
    pass/auto_diff.h
    pass/copy_prop.cpp
    pass/copy_prop.h
    pass/inliner.cpp
    pass/inliner.h
    pass/mem2reg.cpp
    pass/mem2reg.h
    pass/optimize.cpp
    pass/optimize.h
    pass/partial_eval.cpp
    pass/partial_eval.h
    pass/pass.cpp
    pass/pass.h
    transform/cleanup_world.cpp
    transform/cleanup_world.h
    transform/codegen_prepare.h
    transform/codegen_prepare.cpp
    transform/compile_ptrns.h
    transform/compile_ptrns.cpp
    transform/flatten_tuples.cpp
    transform/flatten_tuples.h
    transform/mangle.cpp
    transform/mangle.h
    transform/resolve_loads.cpp
    transform/resolve_loads.h
    transform/partial_evaluation.cpp
    transform/partial_evaluation.h
    util/args.h
    util/array.h
    util/bitset.cpp
    util/bitset.h
    util/cast.h
    util/hash.h
    util/hash.cpp
    util/indexmap.h
    util/indexset.h
    util/iterator.h
    util/stream.cpp
    util/stream.h
    util/types.h
    util/utility.h
)

if(LLVM_FOUND)
    list(APPEND THORIN_SOURCES
        be/llvm/cpu.cpp
        be/llvm/cpu.h
        be/llvm/cuda.cpp
        be/llvm/cuda.h
        be/llvm/hls.cpp
        be/llvm/hls.h
        be/llvm/llvm.cpp
        be/llvm/llvm.h
        be/llvm/amdgpu.cpp
        be/llvm/amdgpu.h
        be/llvm/nvvm.cpp
        be/llvm/nvvm.h
        be/llvm/opencl.cpp
        be/llvm/opencl.h
        be/llvm/parallel.cpp
        be/llvm/runtime.inc
        be/llvm/runtime.cpp
        be/llvm/runtime.h
        be/llvm/vectorize.cpp
    )
endif()

add_library(thorin ${THORIN_SOURCES})

if(LLVM_FOUND)
    llvm_map_components_to_libnames(LLVM_LIBRARIES all)
    target_link_libraries(thorin ${LLVM_LIBRARIES})
endif()
if(RV_FOUND)
    target_link_libraries(thorin ${RV_LIBRARIES})
endif()
