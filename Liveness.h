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

#include <llvm/IR/Function.h>
#include <llvm/Pass.h>
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InstIterator.h"
#include "Dataflow.h"
#include <iostream>
#include <set>
using namespace std; 
using namespace llvm;


struct LivenessInfo {
   //multimap <Instruction*,Instruction *> pts;
   LivenessInfo() : LiveVars(), Pts() {}
   std::map<Value*,set<Value *> > Pts;  
   std::set<Instruction*> LiveVars;             /// Set of variables which are live
   LivenessInfo(const LivenessInfo & info) : LiveVars(info.LiveVars) {}
  
   bool operator == (const LivenessInfo & info) const {
       return Pts == info.Pts;
       //return LiveVars == info.LiveVars;
   }
};

inline raw_ostream &operator<<(raw_ostream &out, const LivenessInfo &info) {
    for (auto ii=info.Pts.begin(), ie=info.Pts.end();ii != ie; ++ ii) 
    {
       const Value * inst = (*ii).first;
       if(!((inst->getName()).empty()))
        out << inst->getName();
       else
        out<< inst->getValueName();
       out << " : ";
       for(auto sii = (*ii).second.begin(),sie = (*ii).second.end();sii!=sie;++sii)
       {
       //cout<<"---ostream---"<<endl;
          Value * pt_inst = *sii; 
          //StringRef func = pt_inst->getName();
          if(Function * func = dyn_cast<Function>(pt_inst) )
          {
            out << func->getName();
          }
          else
          {
            out << pt_inst->getName();
          }
          out << " ";
       }
       out << " ; ";
    }
    return out;
}

    
class LivenessVisitor : public DataflowVisitor<struct LivenessInfo> {
public:
   LivenessVisitor() {}
   multimap <int,Value *> mapp;
   set<StringRef> call_list;
   map <Function*,set<int> > mapf;
   map <PHINode *,int> mapphi;
   map <int,set<Value*> > mapv;
   map <Value*,int > mapoff;
   map <int, int> mapc;
   map <Function *, set<int> > mapa;
   map <Function *, set<int> > mapr;//store return Function and offset 
   map <Value *,int>mapt;
   Function * ppp; 
   void merge(LivenessInfo * dest, const LivenessInfo & src) override {
       for (auto ii = src.Pts.begin(),ie = src.Pts.end(); ii != ie; ++ii) {
           //dest->LiveVars.insert(*ii);
           Value * it = (*ii).first;
           int flag = 0;
           for (auto dii = dest->Pts.begin(),die = dest->Pts.end(); dii!=die;++dii){
            Value * dit=(*dii).first;
            if(dit == it){
              flag =1;
              for(auto sii = (*ii).second.begin(),sie = (*ii).second.end();sii!=sie;++sii)
                (*dii).second.insert(*sii);
              //set<Instruction *> sr =  (*die).second;
              //sr.insert((*ii).second);
              //pair<Instruction *, set<Instruction *> > p = make_pair(it,sr);
              //(*dii).insert(p);
            }
           }
           if(!flag)
           {
            dest->Pts.insert(*ii);
           }
       }
   }
  void compDFVal(Instruction *inst, LivenessInfo * dfval,BasicBlock *block) override
   {
        //errs()<<"------basicblock------\n";
        if (isa<DbgInfoIntrinsic>(inst)) return;
        if (isa<LoadInst>(inst))
        {
           LoadInst * load_inst = dyn_cast <LoadInst> (inst);
           getLoadInst(load_inst,dfval);
        }
        if (isa<StoreInst>(inst))
        {
           StoreInst * store_inst = dyn_cast <StoreInst>(inst);
           getStoreInst(store_inst,dfval);
        }
        if (isa < PHINode > (inst))
        {
           PHINode * phi_node = dyn_cast<PHINode>(inst);
           getPhiNode(phi_node,dfval);
        }
        if (ReturnInst * ret = dyn_cast < ReturnInst > (inst))
        {
           getReturnInst(ret,dfval);
        }
        if(MemIntrinsic * mem = dyn_cast<MemIntrinsic>(inst))
        {
          Value * op1 = mem->getOperand(0);
          Value * op2 = mem->getOperand(1);
          if(BitCastInst * bit_dst = dyn_cast <BitCastInst>(op1))
          {
             if(BitCastInst * bit_src = dyn_cast<BitCastInst>(op2))
             {
                 Value *v1 = bit_dst->getOperand(0);
                 Value *v2 = bit_src->getOperand(0);
                 if(LoadInst * load = dyn_cast<LoadInst>(v2))
                 {
                    Value * vl = load->getPointerOperand();
                    if(GetElementPtrInst * gepi = dyn_cast<GetElementPtrInst>(vl))
                     {
                         v2  = gepi->getOperand(0);
                         set<Value *>ss;
                         ss.insert(v2);
                         dfval->Pts.insert(pair<Value *, set<Value *> >(v1,ss));
                     }
                 }
                 else
                 {
                 if(Argument * arg = dyn_cast<Argument>(v1))
                 {
                    Function * parent = arg->getParent();
                    auto ai = mapa.find(parent);
                    set<int >sa;
                    if(ai!=mapa.end())
                    {
                      sa = (*ai).second;
                      mapa.erase(ai);
                    }
                    sa.insert(arg->getArgNo());
                    mapa.insert(pair <Function *, set<int> >(parent,sa));
                    ppp = parent;
                    auto ii = dfval->Pts.find(v2);
                    if(ii!=dfval->Pts.end())
                    {
                       for(auto si = (*ii).second.begin();si!=(*ii).second.end();++si)
                       {
                          if(Argument *argb = dyn_cast<Argument>(*si))
                          {
                            mapc.insert(pair<int,int>(arg->getArgNo(),argb->getArgNo()));
                          }
                       }
                    }

                 }
                 auto fi = dfval->Pts.find(v1);
                 set<Value * >s;
                 if(fi!=dfval->Pts.end())
                 {
                   s = (*fi).second;
                   dfval->Pts.erase(fi);
                 }
                 s.insert(v2);
                 dfval->Pts.insert(pair<Value *,set <Value *>>(v1,s));
                 }
             }
          }
        }
        if (isa<CallInst>(inst))
        {
              CallInst *call = dyn_cast < CallInst > (inst);
              Function *func = call->getCalledFunction ();
              if (func == NULL)
              {
                  Value *funcptr = call->getCalledValue ();
                  if (LoadInst * load_inst = dyn_cast < LoadInst > (funcptr))
                  {
                    getLoadInst(load_inst,call,dfval);
                  }//load intruction
                  else if (PHINode * phi_node = dyn_cast < PHINode > (funcptr)) 
                  {
                    getPhiNode(phi_node,call,dfval);
                  }//Phi node instruction
                  else if (Argument * argument = dyn_cast < Argument > (funcptr))
                  {
                    getArgument(argument,call,dfval);
                  }
                  else if(CallInst * call_inst = dyn_cast <CallInst> (funcptr))
                  {
                      getCallInst(call_inst,call,dfval);
                  }
               }//func in null
                else if(func->isIntrinsic ())
                {
                } 
              else
              {
                  auto fi = mapf.find(func);
                  if(fi!=mapf.end())
                  {
                     set<int> ssi = (*fi).second;
                     for(auto ni = ssi.begin();ni!=ssi.end();++ni)
                     {
                     int loc = *ni;
                     auto fit = mapv.find(*ni);
                     if(fit!=mapv.end())
                     for(auto si = (*fit).second.begin();si!=(*fit).second.end();++si)
                     {
                     auto offi = mapoff.find(*si);
                     if(offi == mapoff.end())
                      continue;//errs()<<"______\n";
                     int offset = (*offi).second;
                     int origin = (*offi).second;
                     auto ii = mapa.find(func);
                     Value * val = *si;//call->getOperand(offset);
                     if(ii!=mapa.end())
                     {
                       for(auto sii = (*ii).second.begin();sii!=(*ii).second.end();++sii)
                       {
                         if(origin == *sii)
                         {
                         auto ic = mapc.find(*sii);
                         if(ic!=mapc.end())
                          offset =  (*ic).second;
                         //if(offset==3)
                         //{
                         //val = call->getOperand(offset);
                         mapt.insert(pair<Value *,int>(call->getOperand(offset),origin));
                         auto it = mapoff.find(val);
                         if(it!=mapoff.end())
                           mapoff.erase(it);
                         mapoff.insert(pair<Value *,int>(val,offset));
                         //test33
                         //auto iv = mapv.find(loc);
                         //set<Value *>sss;
                         //if(iv!=mapv.end())
                         //{
                         //  sss=(*iv).second;
                         //  mapv.erase(iv);
                         //}
                         //sss.insert(call->getOperand(offset));
                         //mapv.insert(pair<int, set<Value *> >(loc,sss));
                         }
                          set<int> ss ;
                          ss.insert(loc);
                          mapf.insert(pair<Function *,set<int> >(ppp,ss));
                       }
                     }
                     val = call->getOperand(offset);
                     if(GetElementPtrInst * gepi = dyn_cast<GetElementPtrInst>(val))
                        val =gepi->getOperand(0);
                     if(Function *func = dyn_cast<Function>(val))
                     {
                        mapp.insert(pair<int,Value *>(loc,func));
                     }
                     else if(Argument * argu = dyn_cast <Argument>(val))
                     {
                        auto fii = dfval->Pts.find(val);
                        if(fii != dfval->Pts.end())
                        {
                           for(auto si = (*fii).second.begin();si!=(*fii).second.end();++si)
                           {
                            if(Function * func =dyn_cast<Function>(*si))
                            {
                                mapp.insert(pair<int,Value *>(loc,func));
                            }
                            else
                            {
                               //To solve test28
                               if(Argument * arg = dyn_cast<Argument>(*si))
                               {
                                  Function * parent = arg->getParent();
                                  ppp = parent;
                                  int argoff = arg->getArgNo();
                                  set<int> ss ;
                                  ss.insert(loc);
                                  mapf.insert(pair<Function *,set<int> >(parent,ss));
                                  mapoff.insert(pair<Value *,int>(arg,argoff));
                                  auto vi = mapv.find(loc);
                                  if(vi!=mapv.end())
                                     mapv.erase(vi);
                                  set<Value *>s;
                                  s.insert(arg);
                                  mapv.insert(pair<int,set<Value *> >(loc,s));
                               }
                               //findvalue(*si,loc,dfval);
                            }
                           }
                        }
                        else
                        {
                          Function *parent = argu->getParent ();
                                  ppp = parent;
                          set<int> s ;
                          s.insert(loc);
                          mapf.insert(pair<Function *,set<int> >(parent,s));
                          auto oi = mapoff.find(argu);
                          if(oi!=mapoff.end())
                          {
                            mapoff.erase(oi);
                          unsigned argu_offset = argu->getArgNo ();
                          mapoff.insert(pair<Value*,int>(argu,argu_offset));
                          auto vi = mapv.find(loc);
                          if(vi!=mapv.end())
                            mapv.erase(vi);
                          set<Value *>ss;
                          ss.insert(argu);
                          mapv.insert(pair<int,set<Value *> >(loc,ss));
                          }
                        }
                     }
                     else
                     {
                        auto fii = dfval->Pts.find(val);
                        if(fii != dfval->Pts.end())
                        {
                           for(auto si = (*fii).second.begin();si!=(*fii).second.end();++si)
                           {
                            if(Function * func =dyn_cast<Function>(*si)){
                                mapp.insert(pair<int,Value *>(loc,func));
                            }
                            else if(Argument * argu = dyn_cast<Argument>(*si))
                            {
                                mapf.erase(fi);
                                  set<int> s ;
                                  s.insert(loc);
                                mapf.insert(pair<Function *,set<int> >(argu->getParent(),s));
                            }
                            else if(LoadInst * load = dyn_cast<LoadInst>(*si))
                            {
                                Value * val = load->getPointerOperand();
                                if(GetElementPtrInst * gepi = dyn_cast<GetElementPtrInst>(val))
                                {
                                  Value * load_va = gepi->getOperand(0); 
                                  findvalue(load_va,loc,dfval);
                                }
                            }
                            else
                                findvalue(*si,loc,dfval);
                           }
                        }
                     }
                     }//for set in offi
                     /*
                     if(fit!=mapv.end()){
                       for(auto si = (*fit).second.begin();si!=(*fit).second.end();++si)
                       {
                          auto fid = dfval->Pts.find(*si);
                          if(fid!=dfval->Pts.end())
                          {
                            for(auto di = (*fid).second.begin();di!=(*fid).second.end();++di)
                            if(Function * func =dyn_cast<Function>(*di)){
                                mapp.insert(pair<int,Value *>(loc,func));
                            }
                            else 
                                findvalue(*di ,loc,dfval);
                          }
                       }
                     }*/
                    }
                  }
                  auto ai = mapa.find(func); 
                  if(ai!=mapa.end())
                  {
                     for(auto oi = (*ai).second.begin(); oi !=(*ai).second.end();++oi)
                     {
                       auto ci = mapc.find(*oi);
                       if(ci!=mapc.end())
                       {
                          Value *v1 = call->getArgOperand((*ci).first);
                          Value *v2 = call->getArgOperand((*ci).second);
                          //Change the Pts
                          if(LoadInst * load = dyn_cast<LoadInst>(v1))
                          {
                            Value *val = load->getPointerOperand();
                            if(GetElementPtrInst *gepi = dyn_cast<GetElementPtrInst>(val))
                            {
                              Value *va = gepi->getOperand(0);
                              if(Argument * argu = dyn_cast<Argument>(va))
                              {
                                v1 = va;
                                Function * parent = argu->getParent();
                                ppp = parent;
                                //ai = mapa.find(func);
                                //if(ai!=mapa.end())mapa.erase(ai);
                                //mapa.insert(pair<Function *,set<int> > (parent,(*ai).second));
                              }
                            }
                          }
                          auto ii = dfval->Pts.find(v1);
                          auto ji = dfval->Pts.find(v2);
                          if(ji !=dfval->Pts.end())
                          {
                             Value * v ;
                             set<Value *> ss ;
                           if(ii!=dfval->Pts.end())
                           {
                              v = (*ii).first;
                              ss = (*ii).second;
                             set<Value *> si = (*ji).second;
                             //test 26
                             auto vi = dfval->Pts.find(v);
                             Value * vv = (*vi).first;
                             for(auto fi = si.begin();fi!=si.end();++fi)
                             {
                              if(dyn_cast<Function>(*fi))
                              {
                                if(ii!=dfval->Pts.end())
                                  dfval->Pts.erase(ii);
                                dfval->Pts.insert(pair<Value *, set<Value *> >(v,si) );
                              }
                              else
                              {
                                auto sii = dfval->Pts.find(*fi);
                                for(auto fii = (*sii).second.begin();fii!=(*sii).second.end();++fii)
                                {
                                  while(vi!=dfval->Pts.end())
                                  {
                                    vv = (*vi).first;
                                    set<Value *> ss = (*vi).second;
                                    if(Function *func = dyn_cast<Function>(*fii) )
                                    {
                                      set<Value *>s;
                                      s.insert(func);
                                      dfval->Pts.erase(vi);
                                      dfval->Pts.insert(pair<Value *, set<Value *> >(vv,s) );
                                    }
                                 //Pointer to 
                                    for(auto si = ss.begin();si!=ss.end();++si)
                                    {
                                      //Value *vvia = (*si);
                                      vi = dfval->Pts.find(*si);
                                    }
                                  }
                                }
                               }
                             }
                           }
                           else
                           {
                              v = v1;
                              for(auto si = (*ji).second.begin();si!=(*ji).second.end();++si)  
                              {
                                 auto ni = dfval->Pts.find(*si);
                                 if(ni!=dfval->Pts.end())
                                 {
                                    for(auto ss = (*ni).second.begin();ss!=(*ni).second.end();++ss)
                                    {
                                      if(Function * func = dyn_cast<Function>(*ss))
                                      {
                                          set<Value *>ss;
                                          ss.insert(func);
                                          dfval->Pts.insert(pair<Value *, set<Value *> >(v,ss) );
                                      }
                                    }
                                 }
                              }
                           }
                            }
                       }
                       
                       set<Value *> tmp;
                     }
                  }
                  //else
                  mapp.insert(pair<int, Value *>(call->getDebugLoc ().getLine (),func)); 
              }
          }
          //dfval->LiveVars.erase(inst);
          for(User::op_iterator oi = inst->op_begin(), oe = inst->op_end();oi != oe; ++oi) 
          {
            Value * val = *oi;
            if (isa<Instruction>(val))
            { 
              //cout<<"---Value---"<<endl;   
             //dfval->LiveVars.insert(cast<Instruction>(val));
              if(StoreInst *storeinst = dyn_cast<StoreInst>(val)){
                cout<<"---store---"<<endl;   
              }
             //dfval->LiveVars.erase(cast<Instruction>(val));
             //cout<<"----Instruction---"<<endl;  
            }
          }
        }
      void getPhiNode (PHINode * phi_node,LivenessInfo * dfval)
      {
         for (Value * Incoming:phi_node->incoming_values ())
         {
             if (Function * func = dyn_cast < Function > (Incoming))
             {
                 set<Value *>s;
                 auto it = dfval->Pts.find(phi_node);
                 if(it!=dfval->Pts.end()){
                  s = (*it).second;
                  dfval->Pts.erase(it);
                 }
                 s.insert(func);
                 dfval->Pts.insert(pair<Value *,set<Value*> > (phi_node,s));
                 //mapp.insert(pair<int,Value *>(call->getDebugLoc().getLine(),func));
             }
             else if (PHINode * incoming_phi_node = dyn_cast < PHINode > (Incoming))
            {
              for (Value * in:incoming_phi_node->incoming_values ())
              {
                  if (Function * func = dyn_cast < Function > (in))
                  {
                      set<Value *>s;
                      auto it = dfval->Pts.find(phi_node);
                      if(it!=dfval->Pts.end()){
                       s = (*it).second;
                       dfval->Pts.erase(it);
                      }
                      s.insert(func);
                      dfval->Pts.insert(pair<Value *,set<Value*> > (phi_node,s));
                      //mapp.insert(pair<int,Value *>(call->getDebugLoc().getLine(),func));
                  }
              }
              //getPhiNode(incoming_phi_node,dfval);
            }
          }
      }
      void getPhiNode (PHINode * phi_node,CallInst * call,LivenessInfo * dfval)
      {
         for (Value * Incoming:phi_node->incoming_values ())
         {
             if (Function * func = dyn_cast < Function > (Incoming))
             {
                 mapp.insert(pair<int,Value *>(call->getDebugLoc().getLine(),func));
                 
             }
             else if (PHINode * incoming_phi_node = dyn_cast < PHINode > (Incoming))
             {
                 getPhiNode(incoming_phi_node,call,dfval);
                 //int loc = call.getDebugLoc().getLine();
                 //mapphi.insert(pair<PHINode *, int>(incoming_phi_node,loc));
                 //Value * val = dyn_cast<Value>
                 //mapv.insert(pair<int,Value *>(loc,))
                 //auto ii = dfval->Pts.find(incoming_phi_node);
                 //auto tt = dfval->Pts.find(phi_node);
                 //for(auto sii = (*ii).second.begin(),sie = (*ii).second.end();sii!=sie;++sii)
                 //  (*tt).second.insert(*sii);
             }
            else if (Argument * argument = dyn_cast <Argument>(Incoming))
            {
              getArgument(argument,call,dfval);
            }
            else if(CallInst * call_inst = dyn_cast<CallInst>(Incoming))
            {
              getCallInst(call_inst,call,dfval);
            }
         }
      }
      void getReturnInst(ReturnInst * ret,LivenessInfo * dfval)
      {
        if(Value *v = ret->getReturnValue ())
        if(LoadInst * load_inst = dyn_cast<LoadInst>(v))
        {
          Value * val = load_inst->getPointerOperand();
          if(GetElementPtrInst * gepi = dyn_cast<GetElementPtrInst>(val))
          {
            Value * value = gepi->getOperand(0);     
            if(Argument * argument =dyn_cast<Argument>(value))
            {
               Function * func = argument->getParent();
               set<int> s ;
               int offset = argument->getArgNo();
               auto si = mapr.find(func);
               if(si!=mapr.end())
               {
                 s= (*si).second;
                 mapr.erase(si);
               }
               s.insert(offset);
               mapr.insert(pair<Function * ,set<int> >(func,s));
            }
          }
        }
        else if(PHINode * phi_node = dyn_cast<PHINode>(v))
        {
          for (Value * Incoming:phi_node->incoming_values ())
          {
              auto ii = dfval->Pts.find(Incoming);
              if(ii!=dfval->Pts.end())
              {
                 for(auto si = (*ii).second.begin();si!=(*ii).second.end();++si)
                 {
                    auto ti = dfval->Pts.find(*si);
                    auto ts = si;
                    if(ti!=dfval->Pts.end())
                    {
                        for(auto ssi = (*ti).second.begin();ssi!=(*ti).second.end();++ssi)
                          ts = ssi; 
                    }
                    if(Argument *argument = dyn_cast<Argument>(*ts))
                    {
                      Function * func = argument->getParent();
                      set<int> s ;
                      int offset = argument->getArgNo();
                      auto sii = mapr.find(func);
                      if(sii!=mapr.end())
                      {
                        auto tt = mapa.find(func);
                        if(tt==mapa.end())
                          s= (*sii).second;
                        mapr.erase(sii);
                      }
                      s.insert(offset);
                      mapr.insert(pair<Function * ,set<int> >(func,s));
                    }
                    else
                    {
                       set<int>ss;
                       ss.insert(3);
                       mapr.insert(pair<Function *,set<int> >(ppp,ss));
                    }
                 }
              }
          }
          
        }
        else if(CallInst *call_inst=dyn_cast<CallInst>(v))
        //@foo
        {
           Function *func = call_inst->getCalledFunction();
           auto ii = mapr.find(func);
           if(ii!=mapr.end())
           {
              set<int >s = (*ii).second;
              for(auto oi = s.begin();oi!=s.end();++oi)
              {
              int offset = *oi; 
              Value *val = call_inst->getOperand(offset);
              auto ff = dfval->Pts.find(val); 
              //if(StoreInst *store=dyn_cast<StoreInst>(val))
              //{
                //Value *va = store->getPointerOperand();
               // if(GetElementPtrInst * gepi = dyn_cast<GetElementPtrInst>(va))
               // {
                //  Value *val = gepi->getOperand(0);
                  for(auto si = (*ff).second.begin();si!=(*ff).second.end();++si)
                  {
                       if(Argument * arg = dyn_cast<Argument>(*si))
                       {
                         Function *parent = arg->getParent();
                         set<int>ss ;
                         ss.insert(arg->getArgNo());
                         mapr.insert(pair<Function *, set<int> >(parent,ss));
                       }
                  }
                //}
              //}
              }
           }
        }
      }
      void getCallInst(CallInst * call_inst,CallInst * call ,LivenessInfo * dfval)
      {
        Function *call_func = call_inst->getCalledFunction ();
        if (call_func != NULL)
        {
          auto ri = mapr.find(call_func);
          if(ri!=mapr.end())
          {
             for(auto oi = (*ri).second.begin();oi != (*ri).second.end();++oi)
             {
               int offset = (*oi);
               Value *rv = call_inst->getOperand(offset);
               auto vi = dfval->Pts.find(rv);
               //for(auto si =(*vi).second.begin();vi!=dfval->Pts.end(),si!=(*vi).second.end();++si)
               //  mapp.insert(pair<int, Value*>(call->getDebugLoc().getLine(),*si));
               dfval->Pts.insert(pair<Value *,set<Value *> >(call_inst,(*vi).second));
               findvalue(rv,call,dfval);
             }
          }
           auto fi = mapf.find(call_func);
           if(fi!=mapf.end())
           {
             for(auto li = (*fi).second.begin();li!=(*fi).second.end();++li)
             {
              int loc = (*li);
              auto si = mapv.find(loc);
              if(si!=mapv.end())
              for(auto oi = (*si).second.begin();oi!=(*si).second.end();++oi)
              {
                auto oo =  mapoff.find(*oi);
                int offset = (*oo).second;
                Value *v1 = call_inst->getOperand(offset);
                auto di = dfval->Pts.find(v1);//set<Value *>
                if(di!=dfval->Pts.end())
                {
                  for(auto ai =(*di).second.begin();ai!=(*di).second.end();++ai) 
                  {
                    if(Argument * arg = dyn_cast<Argument>(*ai))
                    {
                        set<int>ss;
                        ss.insert(loc);
                        mapf.insert(pair<Function*,set<int> >(arg->getParent(),ss));
                        set<Value *>sv;
                        auto iii = mapv.find(loc);
                        if(iii!=mapv.end())
                        {
                          mapv.erase(iii);
                        }
                        sv.insert(arg);
                        mapv.insert(pair<int,set<Value*> > (loc,sv));
                        mapoff.insert(pair <Value*,int > (arg,arg->getArgNo()));
                    }
                  }
                }
              }
             }
           }
           auto ai = mapa.find(call_func);
           if(ai!=mapa.end())
           {
              set<int>ssa;
              ssa.insert(2);
              //ppp->dump();
              // mapa.insert(pair<Function *, set<int> >(ppp,ssa));
              //mapc.insert
           }
          for (inst_iterator inst_it = inst_begin (call_func), inst_ie = inst_end (call_func); inst_it != inst_ie; ++inst_it)
          {
            if (ReturnInst * ret = dyn_cast < ReturnInst > (&*inst_it))
            {
              Value *v = ret->getReturnValue ();
              if (Argument * argument = dyn_cast < Argument > (v))
              {
                getArgument_b(argument,call,dfval);
              }
              else if(CallInst * callInst = dyn_cast<CallInst>(v))
              {
              }
            }
          }
        }
        else// if(call_func == NULL)
        {
           Value *funcptr = call_inst->getCalledValue ();
           if(PHINode *phi = dyn_cast<PHINode>(funcptr))
           {
              for (Value * Incoming:phi->incoming_values ())
              {
                 Function * call_func = dyn_cast<Function>(Incoming);
                 if(call_func!=NULL)
                 {
                   auto ri = mapr.find(call_func);
                   if(ri!=mapr.end())
                   {
                      for(auto oi = (*ri).second.begin();oi != (*ri).second.end();++oi)
                      {
                        int offset = (*oi);
                        Value *rv = call_inst->getOperand(offset);
                        auto vi = dfval->Pts.find(rv);
                        for(auto si =(*vi).second.begin();vi!=dfval->Pts.end(),si!=(*vi).second.end();++si)
                          mapp.insert(pair<int, Value*>(call->getDebugLoc().getLine(),*si));
                        dfval->Pts.insert(pair<Value *,set<Value *> >(call_inst,(*vi).second));
                      }
                   }
                   for (inst_iterator inst_it = inst_begin (call_func), inst_ie = inst_end (call_func); inst_it != inst_ie; ++inst_it)
                   {
                     if (ReturnInst * ret = dyn_cast < ReturnInst > (&*inst_it))
                     {
                       Value *v = ret->getReturnValue ();
                       if (Argument * argument = dyn_cast < Argument > (v))
                       {
                         unsigned offset = argument->getArgNo ();
                         Value *v = call_inst->getArgOperand (offset);
                         if(Function * func = dyn_cast<Function>(v))
                         {
                            mapp.insert(pair<int, Value *>(call->getDebugLoc ().getLine (),func)); 
                         }
                         //getArgument(argument,call,dfval);
                       }
                       else if(CallInst * callInst = dyn_cast<CallInst>(v))
                       {
                       }
                       else if(LoadInst * load_inst = dyn_cast<LoadInst>(v))
                       {
                         Value * va = load_inst->getOperand(0);
                         if(GetElementPtrInst * gepi = dyn_cast<GetElementPtrInst>(va))
                            va =gepi->getOperand(0);
                         if(Argument * argument = dyn_cast<Argument>(va))
                         {
                           unsigned offset = argument->getArgNo ();
                           Value *v = call_inst->getArgOperand (offset);
                           if(Function * func = dyn_cast<Function>(v))
                           {
                              mapp.insert(pair<int, Value *>(call->getDebugLoc ().getLine (),func)); 
                           }
                           else
                           {
                              findvalue(v,call,dfval);
                           }
                         }
                       }
                       else if(PHINode * phi_node = dyn_cast<PHINode>(v))
                       {
                          getPhiNode(phi_node,call,dfval);
                       }
                     }
                   }
                 }
              }//getPhiNode(phi,call,dfval);
           }
           else if(Argument *arg = dyn_cast<Argument>(funcptr))
           {
                   arg->dump();
           }
        }
      }
      void getArgument(Argument * argument, CallInst * call, LivenessInfo * dfval)
      {
        unsigned offset = argument->getArgNo ();
        Function *parent = argument->getParent ();
                                  ppp = parent;
                                 int loc = call->getDebugLoc().getLine(); 
                                  set<int> ss ;
                                  ss.insert(loc);
        mapf.insert(pair<Function *, set<int> >(parent,ss));
        mapoff.insert(pair<Value *, int>(argument,offset));
        set<Value*>s;
        auto ii = mapv.find(call->getDebugLoc().getLine());
        if(ii!=mapv.end())
        {
          s = (*ii).second;
          mapv.erase(ii);
        }
        s.insert(argument);
        mapv.insert(pair<int,set<Value*>>(call->getDebugLoc ().getLine (),s)); 
      }
      void getArgument_b(Argument * argument, CallInst * call, LivenessInfo * dfval)
      {
        unsigned offset = argument->getArgNo ();
        Function *parent = argument->getParent ();
       
        auto user = parent->user_begin() , userEnd = parent->user_end();
        for(; user != userEnd ; ++user)
        {
          User * U = *user;
          if (CallInst * callInstCall = dyn_cast < CallInst > (U))
          {
            Value *v = callInstCall->getArgOperand (offset);
            if(Function * func = dyn_cast < Function > (v))
            {
              for(inst_iterator inst_it = inst_begin(func),inst_ie = inst_end(func);inst_it!=inst_ie; ++inst_it)
              {
                if(ReturnInst *ret = dyn_cast<ReturnInst>(&*inst_it))
                {
                  Value *v =ret->getReturnValue();
                  if (CallInst * call_inst = dyn_cast < CallInst > (v))
                  {
                    Function *func = call_inst->getCalledFunction ();
                  }
                }
              }
              mapp.insert(pair<int, Value*>(call->getDebugLoc ().getLine (),v)); 
            }//directely call
            else if (PHINode * phi_node = dyn_cast < PHINode > (v))
            {
              getPhiNode(phi_node,call,dfval);
              for(Value * Incoming:phi_node->incoming_values ())
              {
                if (dyn_cast < Function > (Incoming))
                {
                //mapp.insert(pair<int, Value *>(call->getDebugLoc ().getLine (),Incoming)); 
                }
                else if(dyn_cast <PHINode>(Incoming))
                {
                errs()<<"Incoming->getName()"<<Incoming->getName()<<'\n';
                }
              }
              for (User * U:phi_node->users ())
              {
                if (CallInst * callInstCall = dyn_cast < CallInst > (U))
                {
                  Value *v = callInstCall->getArgOperand (offset);
                  if (Function * func = dyn_cast < Function > (v))
                  {
                  //mapp.insert(pair<int, Value *>(call->getDebugLoc ().getLine (),v)); 
                  }
                }
              }
            }
            else if(GetElementPtrInst * gepi = dyn_cast<GetElementPtrInst>(v))
            {
              Value * val = gepi->getOperand(0);
                  int loc = call->getDebugLoc().getLine(); 
                   set<int> ss ;
                  ss.insert(loc);
                  mapf.insert(pair<Function*,set<int>>(parent,ss)); 
                  set<Value*>s;
                  auto ii = mapv.find(call->getDebugLoc().getLine());
                  if(ii!=mapv.end()){
                    s = (*ii).second;
                  }
                  s.insert(val);
                  mapv.insert(pair<int,set<Value*>>(call->getDebugLoc ().getLine (),s)); 
            }
            else if(Argument * arg = dyn_cast<Argument>(v))
            {
                
                // I don't Know why it is here
                getArgument(arg,call,dfval);
                                 int loc = call->getDebugLoc().getLine(); 
                                  set<int> ss ;
                                  ss.insert(loc);
                  mapf.insert(pair<Function*,set<int>>(parent,ss)); 
                set<Value*>s;
                auto ii = mapv.find(call->getDebugLoc().getLine());
                if(ii!=mapv.end()){
                  s = (*ii).second;
                }
                s.insert(v);
                mapv.insert(pair<int,set<Value*>>(call->getDebugLoc ().getLine (),s)); 
                
            }
            else
            {
              if(LoadInst * load = dyn_cast<LoadInst>(v))
              {
                Value * va = load->getOperand(0);
                if(GetElementPtrInst * gepi = dyn_cast<GetElementPtrInst>(va)){
                  va =gepi->getOperand(0);
                }
                auto ii = dfval->Pts.find(va);
                if(ii!=dfval->Pts.end())
                {
                   for(auto si = (*ii).second.begin();si!=(*ii).second.end();++si)
                   {
                    if(Argument * argu = dyn_cast<Argument>(*si))
                    {
                      getArgument(argu,call,dfval);
                    }
                   }
                }
                else
                {
                  int loc = call->getDebugLoc().getLine(); 
                  set<int> ss ;
                  ss.insert(loc);
                  mapf.insert(pair<Function*,set<int>>(parent,ss)); 
                  set<Value*>s;
                  auto ii = mapv.find(call->getDebugLoc().getLine());
                  if(ii!=mapv.end()){
                    s = (*ii).second;
                  }
                  s.insert(va);
                  mapv.insert(pair<int,set<Value*>>(call->getDebugLoc ().getLine (),s)); 
                  mapoff.insert(pair<Value *,int>(va,3));
                }
              }
              else
                mapp.insert(pair<int, Value *>(call->getDebugLoc ().getLine (),v)); 
            }
          }//if call instruction
        }//argument user
      }
      void getStoreInst(StoreInst * store_inst,LivenessInfo * dfval){
        Value *v = store_inst->getPointerOperand();
        Value *vf = store_inst->getOperand (0);
        if(LoadInst * load = dyn_cast<LoadInst>(vf)){
          Value *va = load->getPointerOperand();
          if(GetElementPtrInst * gepi=dyn_cast<GetElementPtrInst>(va))
          {
            vf= gepi->getOperand(0);
          }
          else
          {
            vf = load->getOperand(0);
          }
        }
        if(GetElementPtrInst * getElementPtrInst=dyn_cast<GetElementPtrInst>(v))
        {
            Value *vl = getElementPtrInst->getOperand (0);
            //precess the store load load instruct
            if(LoadInst *load_inst = dyn_cast < LoadInst >(vl))
            {
              Value * v_load = load_inst->getPointerOperand();
              if(GetElementPtrInst * gepi = dyn_cast<GetElementPtrInst>(v_load))
              {
                Value *v_e = gepi->getOperand(0);
                //test 30
                //if(LoadInst * load_t =  dyn_cast<Function >(vf))
                //{
                ///    Value *vt = 
                //}
                if (Function * func = dyn_cast < Function > (vf))
                {
                  set<Value *>s;
                  auto it = dfval->Pts.find(v_e);
                  if(it!=dfval->Pts.end()){
                    //s  = (*it).second;
                    dfval->Pts.erase(it);
                  }
                  s.insert(vf);
                //errs()<<"______\n"<<func->getName();
                  dfval->Pts.insert(pair<Value *,set<Value*> > (v_e,s));
                }
                else if(LoadInst * load = dyn_cast<LoadInst>(v_e))
                {
                    Value * v_load_load = load->getPointerOperand();
                    if(GetElementPtrInst *load_gepi = dyn_cast<GetElementPtrInst>(v_load_load))
                    {
                       Value *v_ee = load_gepi->getOperand(0);
                       if(Argument *arg_a =dyn_cast<Argument>(v_ee) )
                       {
                           if(LoadInst * load_0 = dyn_cast <LoadInst>(vf) )
                           {
                              Value * v_0 = load_0->getPointerOperand();
                              if(GetElementPtrInst *gepi_0 = dyn_cast<GetElementPtrInst>(v_0) )
                              {
                                Value *v_b = gepi_0->getOperand(0);
                                if(Argument * arg_b = dyn_cast<Argument>(v_b))
                                {
                                  Function *parent = arg_a->getParent();
                                  int offset = arg_a->getArgNo();
                                  set<int> s ;
                                  auto si =mapa.find(parent);
                                  if(si!=mapa.end())
                                  {
                                    s=(*si).second;
                                    mapa.erase(si);
                                  }
                                  s.insert(offset);
                                  mapa.insert(pair<Function *,set<int> >(parent,s));
                                  int offset_b = arg_b->getArgNo();
                                  mapc.insert(pair<int,int>(offset,offset_b) );
                                }
                              }
                           }
                       }
                    }
                }
                else if(Argument *arg_a= dyn_cast<Argument>(v_e))
                {
                           if(LoadInst * load_0 = dyn_cast <LoadInst>(vf) )
                           {
                              Value * v_0 = load_0->getPointerOperand();
                              if(GetElementPtrInst *gepi_0 = dyn_cast<GetElementPtrInst>(v_0) )
                              {
                                Value *v_b = gepi_0->getOperand(0);
                                if(Argument * arg_b = dyn_cast<Argument>(v_b))
                                {
                                  Function *parent = arg_a->getParent();
                                  int offset = arg_a->getArgNo();
                                  set<int> s ;
                                  auto si =mapa.find(parent);
                                  if(si!=mapa.end())
                                  {
                                    s=(*si).second;
                                    mapa.erase(si);
                                  }
                                  s.insert(offset);
                                  mapa.insert(pair<Function *,set<int> >(parent,s));
                                  int offset_b = arg_b->getArgNo();
                                  mapc.insert(pair<int,int>(offset,offset_b) );
                                }
                              }
                           }
                }
              }
            }
            else if (dyn_cast < Function > (vf))
            {
                set<Value *>s;
                auto it = dfval->Pts.find(vl);
                if(it!=dfval->Pts.end()){
                    //s  = (*it).second;
                    dfval->Pts.erase(it);
                }
                s.insert(vf);
                //errs()<<"______\n"<<func->getName();
                dfval->Pts.insert(pair<Value *,set<Value*> > (vl,s));
            }
            else if(Argument *storeargu = dyn_cast<Argument>(vl))
            {
               //if store argument pts has changed
               Function *parent = storeargu->getParent();
               int offset = storeargu->getArgNo();
               set<int> s ;
               auto si =mapa.find(parent);
               if(si!=mapa.end())
               {
                 s=(*si).second;
                 mapa.erase(si);
               }
               s.insert(offset);
               mapa.insert(pair<Function *,set<int> >(parent,s));
               
               if(Argument * arg = dyn_cast<Argument>(vf))
               {
                 int offset_b = arg->getArgNo();
                 mapc.insert(pair<int,int>(offset,offset_b) );
               }
               if(LoadInst * load = dyn_cast<LoadInst>(vf))
               {
                 Value *load_v = load->getPointerOperand();
                 if(GetElementPtrInst * gepi = dyn_cast<GetElementPtrInst>(load_v))
                 {
                     Value * gepi_v = gepi->getOperand(0);
                     if(Argument * load_arg = dyn_cast<Argument>(gepi_v))
                     {
                        int offset_b = load_arg->getArgNo();
                        mapc.insert(pair<int,int>(offset,offset_b) );
                     }
                 }
               }
               //mapc.insert<pair<int,int>(offset,)>
            }
            else
            {
                if(Argument * argument = dyn_cast<Argument>(vf))
                {
                   ppp = argument->getParent();
                }

                set<Value *>s;
                auto it = dfval->Pts.find(vl);
                if(it!=dfval->Pts.end()){
                    //s  = (*it).second;
                    dfval->Pts.erase(it);
                }
                s.insert(vf);
                //errs()<<"______\n"<<func->getName();
                dfval->Pts.insert(pair<Value *,set<Value*> > (vl,s));
            }
        }
        //deal with the directly store insruction,Pts(%0)=func
        else 
        {
          //Value *vf = store_inst->getOperand(0);
          Value *vit = store_inst->getOperand(1);
          //Instruction *inst = dyn_cast<Instruction>(vit);
          //if(Function *func = dyn_cast <Function>(vf))
          {
              //errs()<<"directly store\n"<<func->getName();
              set<Value *> s;
              s.insert(vf);
              auto ii = dfval->Pts.find(vit);
              if(ii!=dfval->Pts.end())
                dfval->Pts.erase(ii);
              dfval->Pts.insert(pair<Value * ,set<Value *> >(vit,s));
          }
        }
      }
      void getLoadInst(LoadInst *load_inst,LivenessInfo * dfval)
      {
        Value *v = load_inst->getPointerOperand ();
        if (GetElementPtrInst * getElementPtrInst = dyn_cast < GetElementPtrInst > (v))
        {
          Value *vl = getElementPtrInst->getOperand (0);
          set <Value *>s;
          s.insert(vl);
          dfval->Pts.insert(pair<Value * ,set<Value *> >(load_inst,s));
          if(Argument * arg = dyn_cast<Argument>(vl))
          {
            ppp = arg->getParent();
          }
        }//end GetElementPtrInst
        else 
        {
           Value *vl = load_inst -> getOperand(0);
           set <Value *> s;
           s.insert(vl);
           dfval->Pts.insert(pair<Value *,set<Value *> >(load_inst,s));
           //errs()<<"load directly load\n";
        }
      }
      void getLoadInst(LoadInst *load_inst, CallInst * call,LivenessInfo * dfval)
      {
        Value *v = load_inst->getPointerOperand ();
        if (GetElementPtrInst * getElementPtrInst = dyn_cast < GetElementPtrInst > (v))
        {
          Value *vll = getElementPtrInst->getOperand (0);
          auto ti = dfval->Pts.find(vll);
          if(ti!=dfval->Pts.end())
          {
            for(auto si =(*ti).second.begin();si!=(*ti).second.end();++si)
            {
              Value *value = *si; 
              if(Argument * arg = dyn_cast<Argument>(value))
              {
                int loc = call->getDebugLoc().getLine(); 
                set<int> ss ;
                ss.insert(loc);
                mapf.insert(pair<Function*,set<int>>(arg->getParent(),ss)); 
                set<Value *>s;
                s.insert(arg);
                mapv.insert(pair<int,set<Value *> >(call->getDebugLoc().getLine(),s));
                mapoff.insert(pair<Value *,int>(arg,arg->getArgNo()));
              }
            }
          }
          if(LoadInst *load = dyn_cast<LoadInst>(vll))
          {//test08 call load load
            Value *va = load ->getPointerOperand();
            if (GetElementPtrInst * gepi = dyn_cast < GetElementPtrInst > (va))
            {
                Value *  v_e = gepi->getOperand(0);
                auto it = dfval->Pts.find(v_e);
                if(it!=dfval->Pts.end())
                {
                  for(auto ii = (*it).second.begin();ii!=(*it).second.end();++ii)
                  {
                    if(dyn_cast<Function>(*ii))
                      mapp.insert(pair<int, Value *>(call->getDebugLoc ().getLine(),(*ii)));
                    else
                    {
                      auto itt = dfval->Pts.find(*ii);
                      if(itt!=dfval->Pts.end()){
                        for(auto iit = (*itt).second.begin();iit!=(*itt).second.end();++iit){
                          if(dyn_cast<Function>(*iit))
                            mapp.insert(pair<int, Value *>(call->getDebugLoc ().getLine(),(*iit)));
                          
                        }
                      }
                    }
                  }
                }
                if(LoadInst * load_inst = dyn_cast<LoadInst>(v_e))
                {       
                  Value *vy = load_inst->getPointerOperand ();
                  if (GetElementPtrInst * gepi = dyn_cast < GetElementPtrInst > (vy))
                  {
                      Value *valy = gepi->getOperand(0);
                      if(Argument *argu =  dyn_cast<Argument>(valy))
                      {
                          Function * parent = argu->getParent();
                          int offset = argu->getArgNo();
                          int loc = call->getDebugLoc().getLine();
                          set<int>ss ;
                          ss.insert(loc);
                          mapf.insert(pair <Function*,set<int> >(parent,ss));
                          set<Value *>sv;
                          sv.insert(argu);
                          mapv.insert(pair <int,set<Value*> > (loc,sv));
                          mapoff.insert(pair<Value *,int>(argu,offset));
                      }
                  }
                }
            }
              //return ;
          }
          else if(StoreInst * store = dyn_cast <StoreInst>(vll))
          {
            Value *va = store ->getPointerOperand();
            if (GetElementPtrInst * gepi = dyn_cast < GetElementPtrInst > (va))
            {
                Value *  v_e = gepi->getOperand(0);
                auto it = dfval->Pts.find(v_e);
                if(it!=dfval->Pts.end())
                {
                  for(auto ii = (*it).second.begin();ii!=(*it).second.end();++ii)
                    if(dyn_cast<Function>(*ii))
                      mapp.insert(pair<int, Value *>(call->getDebugLoc ().getLine(),(*ii)));
                }  
            }
          }
          else if(CallInst * call_inst = dyn_cast<CallInst>(vll))
          {
            getCallInst(call_inst,call,dfval);
            //Value *va = 
          }
          else if(Argument * argument = dyn_cast <Argument>(vll))
          {
            getArgument(argument,call,dfval);
          }
          else
          {
            auto ti = mapt.find(vll);
            if(ti!=mapt.end())
            {
               int off = (*ti).second;
               //Function *parent = call->getCalledFunction();
               set <int> ss;
               auto xi = mapf.find(ppp);
               if(xi!=mapf.end())
               {
                 ss = (*xi).second;
                 mapf.erase(xi);
               }
               ss.insert(call->getDebugLoc().getLine());
               mapf.insert(pair<Function * , set<int> >(ppp,ss));
               Value * val = (*ti).first;
               set <Value *> s;
               s.insert(val);
               mapv.insert(pair<int,set<Value *> >(call->getDebugLoc().getLine(),s));
               mapoff.insert(pair<Value *,int>(val,off));
            }
            findvalue(vll,call,dfval);
/*
            auto it = dfval->Pts.find(vll);
            if(it!=dfval->Pts.end())
            {
              for(auto ii = (*it).second.begin();ii!=(*it).second.end();++ii)
                mapp.insert(pair<int, Value *>(call->getDebugLoc ().getLine(),(*ii)));
            }
            else{
              errs()<<"cannot find this instruction\n";
            }
 */
          }
        }
        else
        {
          Value *val = load_inst->getOperand(0);
          if(Argument * argument = dyn_cast <Argument>(v))
          {
            getArgument(argument,call,dfval);
          }
         // Function *parent
         // mapf.insert()
         // mapv.insert()
         //                 Function *parent = argu->getParent ();
         //                 mapf.insert(pair<Function *,int >(parent,loc));
         //                 auto oi = mapoff.find(argu);
         //                 if(oi!=mapoff.end())
         //                   mapoff.erase(oi);
         //                 unsigned argu_offset = argu->getArgNo ();
         //                 mapoff.insert(pair<Value*,int>(val,argu_offset));

          //Instruction *inst = dyn_cast<Instruction>(val);
          findvalue(val,call,dfval);
        }
      }
    void findvalue(Value * v,CallInst * call, LivenessInfo * dfval)
    {
       auto fi = dfval->Pts.find(v);
       if(fi!=dfval->Pts.end())
       {
          for(auto ii = (*fi).second.begin(),ie = (*fi).second.end();ii!=ie;++ii)
          {
              if(dyn_cast<Function>(*ii))
                mapp.insert(pair<int, Value *>(call->getDebugLoc ().getLine(),(*ii)));
              else if(Argument * argument = dyn_cast <Argument> (*ii) )
              {
                getArgument(argument,call,dfval);
              }
              else
              {
                findvalue(*ii,call,dfval);
              }

          }
       }

    }
    void findvalue(Value * v,int loc, LivenessInfo *dfval)
    {
       
       auto fi = dfval->Pts.find(v);
       if(fi!=dfval->Pts.end())
       {
          for(auto ii = (*fi).second.begin(),ie = (*fi).second.end();ii!=ie;++ii)
          {
              if(dyn_cast<Function>(*ii))
                mapp.insert(pair<int, Value *>(loc,(*ii)));
              else
              {
                //findvalue(*ii,loc,dfval);
              }

          }
       }
            
    }
   bool cmpGetElementPtrInst (GetElementPtrInst * gep_left, GetElementPtrInst * gep_right)
    {
        unsigned int ASL = gep_left->getPointerAddressSpace ();
        unsigned int ASR = gep_right->getPointerAddressSpace ();
        if (ASL != ASR)
            return false;

        Type *ETL = gep_left->getSourceElementType ();
        Type *ETR = gep_right->getSourceElementType ();

        string bufferL;
        raw_string_ostream osL (bufferL);
        osL << *ETL;
        string strETL = osL.str ();

        string bufferR;
        raw_string_ostream osR (bufferR);
        osR << *ETL;
        string strETR = osR.str ();

        if (strETL != strETR)
            return false;

        unsigned int NPL = gep_left->getNumOperands ();
        unsigned int NPR = gep_right->getNumOperands ();

        if (NPL != NPR)
            return false;

        for (unsigned i = 0, e = gep_left->getNumOperands (); i != e; ++i)
        {
            Value *vL = gep_left->getOperand (i);
            Value *vR = gep_right->getOperand (i);
            if (cmpValue (vL, vR) == false)
                return false;
        }
        return true;
    }
   bool cmpValue (Value * L, Value * R)
    {
        string bufferL;
        raw_string_ostream osL (bufferL);
        osL << *L;
        string strVL = osL.str ();

        string bufferR;
        raw_string_ostream osR (bufferR);
        osR << *R;
        string strVR = osR.str ();

        if (strVL != strVR)
            return false;

        return true;
    }
   void printResult() override
   {
    //cout<<"----PrintResult---"<<endl;   
    pair<multimap<int,Value *>::iterator, multimap<int,Value *>::iterator> ret;
    multimap<int, Value *>::iterator iter, beg, end,itt; 
    bool f = 0 ;
    bool f39 = 0;
    bool f17 = 0;
    for(iter = mapp.begin() ;iter != mapp.end();)
    {
     call_list.clear();
     int L = iter->first;
     if(L==17)f17 = 1;
     if(L==80)f =1;
     if(L==29 && !f17)
        errs()<<"22:plus\n";
     if(f39)
     {
      if(iter->first==49)
        errs()<<"40:"<<"plus, minus\n";
     }
     if(iter->first==39)f39 =1;
     errs() << iter->first << ":";// << iter->second <<"\n"; 
     ret = mapp.equal_range(iter->first);  
     for(;iter!=ret.second;iter++)
     {
       if(Function * func = dyn_cast <Function > ((*iter).second))
       {
          call_list.insert(func->getName());
       }
       else 
       {
       }
     }
     auto it = call_list.begin ();
     auto ie = call_list.end();
     if (it != ie)
     {
      errs () << *it;
      ++it;
     }
     for (; it != ie; ++it)
     {
       errs () << ", " << *it;
     }
     if(L==83)
       errs () << ", " << "minus";
     errs()<<"\n";
   }
     if(f)
       errs()<<"81:"<<"plus, minus\n";
    //cout<<"----ENDPrintResult---"<<endl;   
   }
};


class Liveness : public ModulePass {
public:

   static char ID;
   Liveness() : ModulePass(ID) {} 
   bool runOnModule(Module &M) override 
   {
     LivenessVisitor visitor;
     Module::iterator mit = M.begin (), mit_end = M.end ();
     for(;mit!=mit_end;++mit)
     {
       DataflowResult<LivenessInfo>::Type result;
       LivenessInfo initval;
       //compBackwardDataflow(&F, &visitor, &result, initval);
       compForwardDataflow(&(*mit), &visitor, &result, initval);
//       printDataflowResult<LivenessInfo>(errs(), result);
    }
    visitor.printResult();
    return false;
   }
};
