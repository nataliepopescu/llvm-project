#include "llvm/Transforms/RemoveBoundsChecks.h"
#include "llvm/PassSupport.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/CFG.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"

#include <set>

using namespace llvm;

namespace {

  struct RemoveBoundsChecks : public FunctionPass {
    static char ID; 
    
    static StringRef getFunctionName(CallBase *call) {
        Function *fun = call->getCalledFunction();
        if (fun) // thanks @Anton Korobeynikov
            return fun->getName(); // inherited from llvm::Value
        else
            return StringRef("indirect call");
    }

    RemoveBoundsChecks() : FunctionPass(ID) {
      initializeRemoveBoundsChecksPass(*PassRegistry::getPassRegistry());
    }

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
      return false;
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction (Function &F) override {
      typedef std::pair<Instruction*, BasicBlock*> edge;
      std::vector<edge> toRemove;
      for (BasicBlock &bb: F) {
        BasicBlock* succ;
        for (Instruction &I: bb) {
          if (CallBase* cs = dyn_cast<CallBase>(&I)) {
            if (getFunctionName(cs).startswith("_ZN4core9panicking18panic_bounds_check")) {
              // bad b/c we may be changing the semantics of the program
              if (InvokeInst* ii = dyn_cast<InvokeInst>(&I)) {
                errs() << "panic_bounds_check INVOKED\n";
              } else {
                errs() << "panic_bounds_check CALLED\n";
              }
              // get predecessor of the basic block
              // get the last branch inst of the predecessor
              // create a branch to the othe
              for (BasicBlock* pred: predecessors(&bb)) { // maybe our unlinking invalidates some of these preds?
                // found bounds check
                Instruction *term = pred->getTerminator();
                int numSucc = term->getNumSuccessors();
                if (numSucc == 2) { // one is bb, one is the original next block
                  if (term->getSuccessor(0) == &bb) {
                    succ = term->getSuccessor(1);
                  } else {
                    succ = term->getSuccessor(0);
                  }
                  toRemove.push_back(edge(term, succ)); // log it in the vector
                  // BranchInst::Create(succ, term);
                  // term->eraseFromParent();
                } else if (numSucc == 1) { // may be leading to a landing pad, so iteratively go up until conditional branch to panic_bounds_check
                  errs() << "only one successor in the previous block\n";
                } else {
                  errs() << "more than two successors in the previous block\n";
                }
              }
            }
          }
        }
      }

      for (auto &i : toRemove){
        auto term = i.first;
        auto succ = i.second;
        BranchInst::Create(succ, term);
        term->eraseFromParent();
      }
      return true;
    }

    void getAnalysisUsage(AnalysisUsage &AU) const override {}
  };
}

PreservedAnalyses RemoveBoundsChecksPass::run(Function &F, FunctionAnalysisManager &AM) {
  PreservedAnalyses PA;
  PA.preserve<BasicAA>();
  return PA;
}

// Next there is code to register your pass to "opt"
char RemoveBoundsChecks::ID = 0;
INITIALIZE_PASS(RemoveBoundsChecks, "remove-bc", "Remove Bounds Checks", false, false)
//static RegisterPass<RemoveBoundsChecks> X("remove-bc", "Remove Bounds Checks"); // only registers for opt tool

Pass *llvm::createRemoveBoundsChecksPass() { 
        return new RemoveBoundsChecks();
}

// Next there is code to register your pass to "clang"
/*static RemoveBoundsChecks * _PassMaker = NULL;
static RegisterStandardPasses _RegPass1(PassManagerBuilder::EP_OptimizerLast,
    [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new RemoveBoundsChecks()); }}); // ** for -Ox
static RegisterStandardPasses _RegPass2(PassManagerBuilder::EP_EnabledOnOptLevel0,
    [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new RemoveBoundsChecks()); }}); // ** for -O0
*/
