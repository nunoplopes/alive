

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
#include "llvm/Pass.h"
#include "llvm/Support/CFG.h"
#include "llvm/Transforms/Utils/Local.h"
#include <list>
using namespace llvm;
using namespace llvm::PatternMatch;


namespace{
  struct ALIVE: public FunctionPass {
    static char ID;
    ALIVE(): FunctionPass(ID) {
      initializeALIVEPass(*PassRegistry::getPassRegistry());
    }

    virtual bool runOnFunction(Function &F);
  };

}

char ALIVE::ID = 0;


INITIALIZE_PASS_BEGIN(ALIVE, "alive", "ALIVE C++ code gen pass for InstCombine",
                false, false)
INITIALIZE_PASS_END(ALIVE, "alive", "ALIVE C++ code gen pass for InstCombine",
                false, false)

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
          more = true;
          break;
        }
      }
    }
  }
  
  return true;
}

char & llvm::ALIVEPassID = ALIVE::ID;
FunctionPass *llvm:: createALIVEPass(){
  return new ALIVE();
}


