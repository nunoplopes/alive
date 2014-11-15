

#define DEBUG_TYPE "alive_instcombine"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Support/PatternMatch.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Pass.h"
#include "llvm/Support/CFG.h"
#include "llvm/Transforms/Utils/Local.h"
#include <list>
using namespace llvm;
using namespace llvm::PatternMatch;

STATISTIC(NumXforms, "total rules fired");

namespace{
  struct ALIVE: public FunctionPass {
    static char ID;
    ALIVE(): FunctionPass(ID) {
      //      initializeALIVEPass(*PassRegistry::getPassRegistry());
    }

    virtual bool runOnFunction(Function &F);
  };

}

char ALIVE::ID = 0;

#if 0
INITIALIZE_PASS_BEGIN(ALIVE, "alive", "ALIVE C++ code gen pass for InstCombine",
                false, false)
INITIALIZE_PASS_END(ALIVE, "alive", "ALIVE C++ code gen pass for InstCombine",
                false, false)
#endif

bool hasNoSignedWrap(Value *I) {
  if (OverflowingBinaryOperator *op = dyn_cast<OverflowingBinaryOperator>(I)) {
    return op->hasNoSignedWrap();
  }
  return false;
}

bool hasNoUnsignedWrap(Value *I) {
  if (OverflowingBinaryOperator *op = dyn_cast<OverflowingBinaryOperator>(I)) {
    return op->hasNoUnsignedWrap();
  }
  return false;
}

bool isExact(Value *I) {
  if (PossiblyExactOperator *op = dyn_cast<PossiblyExactOperator>(I)) {
    return op->isExact();
  }
  return false;
}

// unsigned ComputeNumSignBits(Value *Op, unsigned Depth = 0) {
//   //return llvm::ComputeNumSignBits(Op, TD, Depth);
//   return 1;
// }

APInt computeKnownZeroBits(Value *V) {
  unsigned BitWidth = V->getType()->getScalarSizeInBits();
  APInt KnownZero(BitWidth, 0), KnownOne(BitWidth, 0);
  ComputeMaskedBits(V, KnownZero, KnownOne);
  return KnownZero;
}

APInt computeKnownOneBits(Value *V) {
  unsigned BitWidth = V->getType()->getScalarSizeInBits();
  APInt KnownZero(BitWidth, 0), KnownOne(BitWidth, 0);
  ComputeMaskedBits(V, KnownZero, KnownOne);
  return KnownOne;
}

// bool MaskedValueIsZero(Value *V, const APInt &Mask) {
//   return false;
// }

bool WillNotOverflowSignedAdd(Value *op1, Value *op2) {
  return false;
}

#include "alive.inc"

bool ALIVE:: runOnFunction(Function &F){
  
  if(F.isDeclaration())
    return false;

  for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
    SmallPtrSet<Instruction*,10> seen;
    bool more = true;
    while (more) {
      more = false;

      for (BasicBlock::iterator BBI = BB->begin(), BBE = BB->end(); BBI != BBE; ) {
        Instruction *I = BBI++;
        bool newI = seen.insert((Instruction*) I);
        if (newI && runOnInstruction(I)) {
          ++NumXforms;
          more = true;
          break;
        }
      }
    }
  }
  
  return true;
}

//char & llvm::ALIVEPassID = ALIVE::ID;
FunctionPass * createALIVEPass(){
  return new ALIVE();
}


