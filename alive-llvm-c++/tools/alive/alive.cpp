#include "llvm/IR/LLVMContext.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/Triple.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/RegionPass.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Assembly/PrintModulePass.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/CodeGen/CommandFlags.h"
#include "llvm/DebugInfo.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/LinkAllIR.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/MC/SubtargetFeature.h"
#include "llvm/PassManager.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PassNameParser.h"
#include "llvm/Support/PluginLoader.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include <algorithm>
#include <memory>
using namespace llvm;

static cl::opt<std::string>
InputFilename(cl::Positional, cl::desc("<input bitcode file>"),
    cl::init("-"), cl::value_desc("filename"));


int
main (int argc, char ** argv)
{
  llvm_shutdown_obj Y;
  LLVMContext &Context = getGlobalContext();

  std::string OutputFilename;

  cl::ParseCommandLineOptions(argc, argv, "Alive Pass for instcombine \n");
  sys::PrintStackTraceOnErrorSignal();
  
  PassRegistry &Registry = *PassRegistry::getPassRegistry();
  
  initializeCore(Registry);
  initializeScalarOpts(Registry);
  initializeIPO(Registry);
  initializeAnalysis(Registry);
  initializeIPA(Registry);
  initializeTransformUtils(Registry);
  initializeInstCombine(Registry);
  initializeInstrumentation(Registry);
  initializeTarget(Registry);


  PassManager Passes;

  SMDiagnostic Err;    
  OwningPtr<Module> M1;

  M1.reset(ParseIRFile(InputFilename, Err, Context));
  if(M1.get() == 0){
    Err.print(argv[0], errs());
    return 1;
  }

  OwningPtr<tool_output_file> Out;
  std::string ErrorInfo;

  OutputFilename = InputFilename + ".alive.bc";

  Out.reset(new tool_output_file(OutputFilename.c_str(), ErrorInfo, sys::fs::F_None));

  if(!ErrorInfo.empty()){
    errs()<< ErrorInfo<<'\n';
    return 1;
  }
  
  Passes.add(createALIVEPass());
  Passes.add(createBitcodeWriterPass(Out->os()));
  Passes.run(*M1.get());

  Out->keep();

  return 0;
}
