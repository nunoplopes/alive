// Copyright 2014 The Souper Authors. All rights reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

using namespace llvm;

namespace {
unsigned ReplaceCount;

static cl::opt<unsigned> FirstReplace("first-opt", cl::Hidden,
    cl::init(0),
    cl::desc("First optimization to perform (default=0)"));

static cl::opt<unsigned> LastReplace("last-opt", cl::Hidden,
    cl::init(std::numeric_limits<unsigned>::max()),
    cl::desc("Last optimization to perform (default=infinite)"));

struct AlivePass : public FunctionPass {
  static char ID;

public:
  AlivePass() : FunctionPass(ID) {
  }

  void getAnalysisUsage(AnalysisUsage &Info) const {
    Info.addRequired<LoopInfo>();
  }

  bool runOnFunction(Function &F) {
    bool changed = false;
    InstContext IC;
    ExprBuilderContext EBC;
    CandidateMap CandMap;

    LoopInfo *LI = &getAnalysis<LoopInfo>();

    std::string FunctionName;
    if (F.hasLocalLinkage()) {
      FunctionName =
        (F.getParent()->getModuleIdentifier() + ":" + F.getName()).str();
    } else {
      FunctionName = F.getName();
    }

    ExprBuilder EB(Opts, F.getParent(), LI, IC, EBC);

    for (auto &BB : F) {
      std::unique_ptr<BlockCandidateSet> BCS(new BlockCandidateSet);
      for (auto &I : BB) {
        if (ReplaceCount >= FirstReplace && ReplaceCount <= LastReplace) {
          BasicBlock::iterator BI = I;


          // RUN ALIVE OPTIMIZATIONS FROM HERE


          ReplaceInstWithValue(I->getParent()->getInstList(), BI, CI);
          changed = true;
        }
        if (ReplaceCount < std::numeric_limits<unsigned>::max())
          ++ReplaceCount;
      }
    }

    return changed;
  }
};

char AlivePass::ID = 0;
}

namespace llvm {
void initializeAlivePassPass(llvm::PassRegistry &);
}

INITIALIZE_PASS_BEGIN(AlivePass, "Alive", "Alive pass", false, false)
INITIALIZE_PASS_DEPENDENCY(LoopInfo)
INITIALIZE_PASS_END(AlivePass, "Alive", "Alive pass", false, false)

static struct Register {
  Register() {
    initializeAlivePassPass(*llvm::PassRegistry::getPassRegistry());
  }
} X;

static void registerAlivePass(
    const llvm::PassManagerBuilder &Builder, llvm::PassManagerBase &PM) {
  PM.add(new AlivePass);
}

static llvm::RegisterStandardPasses
RegisterAlive(llvm::PassManagerBuilder::EP_Peephole, registerAlivePass);
