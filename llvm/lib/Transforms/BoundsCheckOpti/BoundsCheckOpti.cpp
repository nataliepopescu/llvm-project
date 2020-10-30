#include "llvm/Pass.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/LoopVersioning.h"

#include <unordered_map>
#include <unordered_set>

using namespace llvm;

namespace {
struct BoundsCheckOpti : public LoopPass {
  static char ID;
  BoundsCheckOpti() : LoopPass(ID) {}

  bool runOnLoop(Loop *L, LPPassManager &LPM) override;

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<ScalarEvolutionWrapperPass>();
  }

}; // end of struct BoundsCheckOpti
} // end of anonymous namespace

bool BoundsCheckOpti::runOnLoop(Loop *L, LPPassManager &LPM) {
  if (!L)
    return false;
  BasicBlock *header = L->getHeader();
  errs() << "BoundsCheckOpti for Loop: " << header->getName() << '\n';
  Function *func = header->getParent();

  // run -loop-simplify before

  // check that loop is formatted as expected
  if (!L->isLoopExiting(header))
    // avoid handling this case for now
    return false;
  BranchInst *headerTerm = dyn_cast<BranchInst>(header->getTerminator());
  if (!headerTerm)
    return false;
  BasicBlock *preheader = L->getLoopPreheader();
  if (!preheader)
    return false;

  Instruction *indvar = L->getCanonicalInductionVariable();
  if (!indvar)
    return false;
  PHINode *indvarPHI = dyn_cast<PHINode>(indvar);
  errs() << "Canonical Ind Var: " << *indvar << '\n';

  BasicBlock *incomingBB = nullptr, *backedgeBB = nullptr;
  if (!L->getIncomingAndBackEdge(incomingBB, backedgeBB))
    return false;

  Instruction *incV =
      dyn_cast<Instruction>(indvarPHI->getIncomingValueForBlock(backedgeBB));
  if (!incV)
    return false;

  SmallVector<BasicBlock *, 8> exitingBlocks;
  L->getExitingBlocks(exitingBlocks);
  // no need to do anything for loops with only one loop exit
  if (exitingBlocks.size() == 1)
    return false;

  std::unordered_map<Value *, BasicBlock *> limitToExitBlock;
  std::unordered_set<BranchInst *> termsToBeModified;

  errs() << "Initial applicability checks passed. Checking mergeability of "
            "exiting blocks\n";

  // This loop has more than one exit.
  // For the transformation to be applicable (in its current impl),
  // all loop exits need to compare the ind var with a loop invariant limit.
  // collect all limits and exit blocks
  // check if all the loop exits can be replaced by a single exit in the header
  //
  for (BasicBlock *exitingBlock : exitingBlocks) {
    BranchInst *bI = dyn_cast<BranchInst>(exitingBlock->getTerminator());
    errs() << "Checking BranchInst with term: " << *bI << '\n';
    if (!bI)
      return false;
    if (!bI->isConditional())
      return false;
    CmpInst *cI = dyn_cast<CmpInst>(bI->getCondition());
    if (!cI)
      return false;
    // only handle equality for now for now
    if (!cI->isEquality())
      return false;

    // ind var needs to be compared with a loop-invariant limit
    Value *limit = nullptr;
    if (cI->getOperand(0) == indvar || cI->getOperand(0) == incV) {
      limit = cI->getOperand(1);
    } else if (cI->getOperand(1) == indvar || cI->getOperand(1) == incV) {
      limit = cI->getOperand(0);
    }
    if (!limit)
      return false;
    if (!L->isLoopInvariant(limit))
      return false;

    // if not the header, check whether it is safe to move the check in
    // the header
    if (exitingBlock != header) {
      // be conservative and only handle the origin of the backedge
      if (exitingBlock != backedgeBB)
        return false;

      // ensure that moving the check of the current exitingBlock to the header
      // will not change the live-out state of the loop.

      // Check that all instructions in the header (i.e., instructions
      // between the terminator of the backedgeBB and the terminator of
      // the header) have no side-effects and are not live-out.

      for (Instruction &hI : *header) {
        // check that the instruction does not have any side effects
        if (hI.mayHaveSideEffects())
          return false;

        // ensure that non-side-effect insts are not live-out
        for (User *u : hI.users()) {
          if (Instruction *uI = dyn_cast<Instruction>(u)) {
            if (!L->contains(uI))
              return false;
          }
        }
      }

      // safe to move check
      termsToBeModified.insert(bI);
    }

    BasicBlock *exitBlock = (!L->contains(bI->getSuccessor(0)))
                                ? bI->getSuccessor(0)
                                : bI->getSuccessor(1);
    limitToExitBlock[limit] = exitBlock;
  }

  // merge of all exit conditions is possible.
  // The transformation is applicable

  // deal with only two exit blocks for now
  if (limitToExitBlock.size() != 2)
    return false;
  auto mapIt = limitToExitBlock.begin();
  Value *limit1 = mapIt->first;
  BasicBlock *exitBlock1 = mapIt->second;
  mapIt++;
  Value *limit2 = mapIt->first;
  BasicBlock *exitBlock2 = mapIt->second;

  errs() << "Bounds Check Optimization is applicable. Transforming the code\n";

  //  change exiting blocks (except for the header) to a unconditional branch
  //  (removes the exit block successor)
  for (BranchInst *bI : termsToBeModified) {
    BasicBlock *inLoopSucc = (L->contains(bI->getSuccessor(0)))
                                 ? bI->getSuccessor(0)
                                 : bI->getSuccessor(1);
    BasicBlock::iterator bii(bI);
    ReplaceInstWithInst(bI->getParent()->getInstList(), bii,
                        BranchInst::Create(inLoopSucc));
  }

  // compare the limits in the preheader and compute the smallest
  Instruction *preheaderTerm = preheader->getTerminator();
  // TODO: if limits are equal make sure the correct path is taken.
  CmpInst *compareSizeCond = CmpInst::Create(
      Instruction::ICmp, CmpInst::ICMP_SLE, limit1, limit2, "comparesize");
  compareSizeCond->insertBefore(preheaderTerm);
  SelectInst *smallerSize =
      SelectInst::Create(compareSizeCond, limit1, limit2, "smallersize");
  smallerSize->insertBefore(preheaderTerm);

  // create a new exiting block
  LLVMContext &ctx = func->getParent()->getContext();
  BasicBlock *newExitingBB =
      BasicBlock::Create(ctx, "unifiedexit", func, exitBlock1);
  BranchInst::Create(exitBlock1, exitBlock2, compareSizeCond, newExitingBB);

  // terminator of the header needs to jump to the new exiting BB
  CmpInst::Predicate pred;
  if (!L->contains(headerTerm->getSuccessor(0))) {
    headerTerm->setSuccessor(0, newExitingBB);
    pred = CmpInst::ICMP_EQ;
  } else {
    headerTerm->setSuccessor(1, newExitingBB);
    pred = CmpInst::ICMP_NE;
  }

  // the loop exit condition in the header needs to compare the ind var with the
  // "smallersize" limit
  CmpInst *newLoopExitCond = CmpInst::Create(Instruction::ICmp, pred, indvar,
                                             smallerSize, "newloopexitcond");
  newLoopExitCond->insertBefore(headerTerm);
  headerTerm->setCondition(newLoopExitCond);

  errs() << "Modified the loop\n";

  return true;
}

char BoundsCheckOpti::ID = 0;
static RegisterPass<BoundsCheckOpti>
    X("bounds-check-opti", "Bounds check optimization pass", false, false);
