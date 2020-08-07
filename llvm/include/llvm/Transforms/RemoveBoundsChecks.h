#ifndef LLVM_TRANSFORMS_REMOVE_BOUNDS_CHECKS_H
#define LLVM_TRANSFORMS_REMOVE_BOUNDS_CHECKS_H

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/PassManager.h"


namespace llvm {

class Pass;
class PassManagerBuilder;

struct RemoveBoundsChecksPass : public PassInfoMixin<RemoveBoundsChecksPass> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

Pass *createRemoveBoundsChecksPass();
  
}

#endif
