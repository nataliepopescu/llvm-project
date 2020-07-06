#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace {

    struct Simple : public FunctionPass {
        static char ID;
        Simple() : FunctionPass(ID) {}
        bool runOnFunction(Function &F) override {
            errs() << "Simple hello: ";
            errs.write_escaped(F.getName()) << '\n';
            return false;
        }
    }; // end of struct
} // end of anonymous namespace

char Simple::ID = 0;

static RegisterPass<Simple> X("simple", "Simple Hello World Pass",
        false, // FIXME set true to walk CFG?
        false); // Transformation pass

static llvm::RegisterStandardPasses Y(
    llvm::PassManagerBuilder::EP_EarlyAsPossible,
    [](const llvm::PassManagerBuilder &Builder,
       llvm::legacy::PassManagerBase &PM) { PM.add(new Simple()); });
