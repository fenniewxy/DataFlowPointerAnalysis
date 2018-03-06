//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include <llvm/Support/CommandLine.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Support/ToolOutputFile.h>

#if LLVM_VERSION_MAJOR >= 4
#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>

#else
#include <llvm/Bitcode/ReaderWriter.h>
#endif

#include <llvm/Transforms/Scalar.h>
#include <iostream>
#include "Liveness.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
using namespace llvm;
using namespace std;
//multimap <int,StringRef> mapp;
#define NDEBUG
#if LLVM_VERSION_MAJOR >= 4
static ManagedStatic<LLVMContext> GlobalContext;
static LLVMContext &getGlobalContext() { return *GlobalContext; }
#endif

/* In LLVM 5.0, when  -O0 passed to clang , the functions generated with clang will
* have optnone attribute which would lead to some transform passes disabled, like mem2reg.
*/
#if LLVM_VERSION_MAJOR == 5
struct EnableFunctionOptPass : public FunctionPass {
    static char ID;
    EnableFunctionOptPass() :FunctionPass(ID) {}
    bool runOnFunction(Function & F) override {
        if (F.hasFnAttribute(Attribute::OptimizeNone))
        {
            F.removeFnAttr(Attribute::OptimizeNone);
        }
        return true;
    }
};

char EnableFunctionOptPass::ID = 0;
#endif

///!TODO TO BE COMPLETED BY YOU FOR ASSIGNMENT 3
struct FuncPtrPass : public ModulePass {
    static char ID; // Pass identification, replacement for typeid
    FuncPtrPass() : ModulePass(ID) {}
    set < StringRef > call_list;
  bool runOnModule(Module &M) override {
    Module::iterator mit = M.begin (), mit_end = M.end ();
    for(;mit!=mit_end;++mit){
      Function::iterator fit = mit->begin(),fit_end = mit->end();
      //errs() << "Hello: ";
      //errs().write_escaped((*mit).getName()) << '\n';
      //(*mit).dump();
      //errs() << "------------------------------\n";
      for (; fit != fit_end; ++fit){
        BasicBlock::iterator bit = fit->begin (), bit_end = fit->end ();
        for(;bit!=bit_end;++bit){
          Instruction *inst = dyn_cast < Instruction > (bit);
          if (isa < CallInst > (bit)){
            CallInst *call = dyn_cast < CallInst > (inst);
            Function *func = call->getCalledFunction();
            if(func==NULL){
              //getFunc(call);
             //auto it = call_list.begin ();
             //auto ie = call_list.end();
             //for(;it!=ie;++it)
              //mapp.insert(pair<int, StringRef>(call->getDebugLoc ().getLine (),*it)); 
              //errs()<<"func is NULL"<<'\n';
            }
            else if(func->isIntrinsic()){
              continue;
            }
            //call_list.insert (func->getName ());
            else{
              //errs()<<"call: "<<call->getCalledFunction()->getName()<<'\n';
              //mapp.insert(pair<int, StringRef>(call->getDebugLoc ().getLine (),func->getName())); 
            }
           }
        }
      }
    }
    return false;
    }
};


char FuncPtrPass::ID = 0;
static RegisterPass<FuncPtrPass> X("funcptrpass", "Print function call instruction");

char Liveness::ID = 0;
static RegisterPass<Liveness> Y("liveness", "Liveness Dataflow Analysis");


static cl::opt<std::string>
InputFilename(cl::Positional,
              cl::desc("<filename>.bc"),
              cl::init(""));


int main(int argc, char **argv) {
   LLVMContext &Context = getGlobalContext();
   SMDiagnostic Err;
   // Parse the command line to read the Inputfilename
   cl::ParseCommandLineOptions(argc, argv,
                              "FuncPtrPass \n My first LLVM too which does not do much.\n");


   // Load the input module
   std::unique_ptr<Module> M = parseIRFile(InputFilename, Err, Context);
   if (!M) {
      Err.print(argv[0], errs());
      return 1;
   }

   llvm::legacy::PassManager Passes;
#if LLVM_VERSION_MAJOR == 5
   Passes.add(new EnableFunctionOptPass());
#endif
   ///Transform it to SSA
   Passes.add(llvm::createPromoteMemoryToRegisterPass());

   /// Your pass to print Function and Call Instructions
   Passes.add(new Liveness());
   Passes.add(new FuncPtrPass());
   Passes.run(*M.get());
/*
   multimap<int, StringRef>::iterator iter, beg, end,itt; 
   pair<multimap<int,StringRef>::iterator, multimap<int,StringRef>::iterator> ret;
   for(iter = mapp.begin() ;iter != mapp.end();){
     errs() << iter->first << ":";// << iter->second <<"\n"; 
     ret = mapp.equal_range(iter->first);  
     if(iter!=mapp.end()){
       errs()<<(*iter).second;
       ++iter;
     }
     for(; iter != ret.second;++iter)
     {
        errs()<<","<< (*iter).second;
     }
      errs()<<"\n";
   }
*/
#ifndef NDEBUG
   system("pause");
#endif
}

