#define DEBUG_TYPE "coffee"
#include <iostream>
#include <map>
#include <set>
#include <algorithm>
#include "llvm/IR/DebugInfo.h"
#include "llvm/Pass.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Analysis/Interval.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/DebugInfoMetadata.h"

using namespace llvm;
using namespace std;

namespace {
    struct Coffee : public BasicBlockPass {
        static char ID;     // Pass identification
        Coffee(): BasicBlockPass(ID) { }
        
        map<pair<Instruction *, string>, Instruction *> btd_table;
        map<BasicBlock*, set<pair<Instruction *, string>>&> USE;
        map<BasicBlock*, set<pair<Instruction *, string>>&> DEF;
        map<BasicBlock*, set<pair<Instruction *, string>>&> IN;
        map<BasicBlock*, set<pair<Instruction *, string>>&> OUT;
        
        virtual bool runOnBasicBlock(BasicBlock &bb) {
            eval_USEDEF(&bb);
        }
        
        virtual bool  doInitialization(Function &f) {
            for (Function::iterator bb = f.begin(); bb != f.end(); bb++) {
                BasicBlock &temp = *bb;
                USE.insert(pair<BasicBlock*, set<pair<Instruction *, string>>&>(&temp, * new set<pair<Instruction *, string>>()));
                DEF.insert(pair<BasicBlock*, set<pair<Instruction *, string>>&>(&temp, * new set<pair<Instruction *, string>>()));
                IN.insert(pair<BasicBlock*, set<pair<Instruction *, string>>&>(&temp, * new set<pair<Instruction *, string>>()));
                OUT.insert(pair<BasicBlock*, set<pair<Instruction *, string>>&>(&temp, * new set<pair<Instruction *, string>>()));
                
            }
            return true;
        }
        
        /*****      TO DO : refactoring         *****/
        virtual bool doFinalization(Function &f) {
            eval_AllINOUT(f);
            
            errs() << "******* Backward Taing Analysis Result *******\n";
            int bb_count = 0;
            for (Function::iterator bb = f.begin(); bb != f.end(); bb_count++,bb++) {
                BasicBlock &temp = *bb;
                // printUSEDEF(bb_count, bb); // optional
                //printINOUT(bb_count, &temp);
            }
            
            printTable(btd_table);
            errs() << "\n\n";
            errs() << "*********       end of the result       *********\n";
            
            return true;
        }
        
        
    private:  bool is_inDEF(BasicBlock * bb, string s){ // check <P,  src>  in  DEF(X)
        if (DEF.count(bb) < 1) return false; // throw exception
        
        set<pair<Instruction *, string>> & bbDEF = DEF.find(bb)->second;
        int checkIn = 0;
        
        for(set<pair<Instruction *,string>>::iterator i = bbDEF.begin() ; i != bbDEF.end(); i++){
            if(i->second == s){
                checkIn++;
            }
        }
        return (checkIn >= 1) ;
    }
        
    private:  Instruction* getPC_inDEF(BasicBlock * bb, string s){ // check <P,  src>  in  DEF(X)
        set<pair<Instruction *, string>> & bbDEF = DEF.find(bb)->second;
        for(set<pair<Instruction *,string>>::iterator i = bbDEF.begin() ; i != bbDEF.end(); i++){
            if(i->second == s){
                return i->first;
            }
        }
    }
        
    private: bool is_ignorableInst(Instruction* inst) {
        string opcodeName = inst->getOpcodeName();
        unsigned int numOperands = inst->getNumOperands();
        
        return
        (opcodeName == "br" && numOperands == 1)
        // unconditional branch : no src or dest
        || (opcodeName == "alloca") ;
        // alloca :  no src or dest
        
    }
        
    private: bool is_ignorableOprd(Instruction * inst, unsigned int i_oprd) {
        string opcodeName = inst->getOpcodeName();
        return opcodeName == "br" && i_oprd > 0;
        // conditional branch has multiple operands
        // only the first is considered "used", others are "labels"
        
        // to do : more cases
    }
        
    private: bool is_destOprd(Instruction * inst, unsigned int i_oprd) {
        string opcodeName = inst->getOpcodeName();
        
        return opcodeName == "store"  && i_oprd == 1;
        // store's 1'th operand (not 0'th) is "dest"
        // to do : more cases
    }
        
    private:  void eval_USEDEF(BasicBlock * bb) {
        if (USE.count(bb) < 1 || DEF.count(bb) < 1) return; // throw exception
        
        set<pair<Instruction *, string>> & bbUSE = USE.find(bb)->second;
        set<pair<Instruction *, string>> & bbDEF = DEF.find(bb)->second;
        
        for (BasicBlock::iterator inst = bb->begin(); inst != bb->end(); inst++) {
            Instruction &bbInst = *inst;
            if(is_ignorableInst(&bbInst)) continue;
            
            //            string tempGetName =bbInst.getName();
            string tempGetName =bbInst.getOperand(0)->getName();
            
            pair<Instruction *,string> dest(&bbInst, tempGetName);
            
            string opcodeName = bbInst.getOpcodeName();
            unsigned int numOperands = bbInst.getNumOperands();
            
            for (int i_oprd = 0; i_oprd < numOperands; i_oprd++) {
                if (is_ignorableOprd(&bbInst, i_oprd)) break;
                
                string src_val = bbInst.getOperand(i_oprd)->getName();
                if(src_val == "") break;
                
                pair<Instruction *,string> src (&bbInst, src_val);
                
                if(is_inDEF(bb, src_val)){ // if  (<P,  src>  in  DEF(X))  for  some  P
                    btd_table.insert(pair<pair<Instruction *, string>, Instruction *>(pair<Instruction *, string>(&bbInst, src_val), getPC_inDEF(bb, src_val)));
                }
                
                if (is_destOprd(&bbInst, i_oprd))
                    dest = src;
                
                if (!is_inDEF(bb, src_val)) // src  not  in  DEF(X) : USE(X)  +=  <current_pc,  src>
                    bbUSE.insert(pair<Instruction *, string>(&bbInst, src_val));
            }
            
            if(is_inDEF(bb, dest.second) && getPC_inDEF(bb, dest.second) != &bbInst){
                bbDEF.erase(make_pair(getPC_inDEF(bb, dest.second), dest.second));
            }
            bbDEF.insert(dest);     // DEF(X)  +=  <current_pc,  dest>
        }
    }
        
    private: set<BasicBlock*> * getSuccessors(BasicBlock *bb) {
        set<BasicBlock *> * succs = new set<BasicBlock*>();
        
        TerminatorInst * term_inst = bb->getTerminator();
        for (int i = 0; i < term_inst->getNumSuccessors(); i++)
            succs->insert(term_inst->getSuccessor(i));
        
        return succs;
    }
        
    private:  void eval_AllINOUT(Function &f){
        bool change = true;
        while (change) {
            change = false;
            for (Function::iterator bb = f.begin(); bb != f.end(); bb++) {
                BasicBlock &temp = *bb;
                if (USE.count(&temp) < 1 || DEF.count(&temp) < 1
                    || IN.count(&temp) < 1 || OUT.count(&temp) < 1) return; //exception
                
                set<pair<Instruction *, string>> & bbUSE = USE.find(&temp)->second;
                set<pair<Instruction *, string>> & bbDEF = DEF.find(&temp)->second;
                set<pair<Instruction *, string>> & bbIN = IN.find(&temp)->second;
                set<pair<Instruction *, string>> & bbOUT = OUT.find(&temp)->second;
                
                // OLD_IN = IN;
                set<pair<Instruction *, string>> old_in = bbIN;    // value by value copy
                
                // OUT = INs of successors
                set<BasicBlock*> * succrs = getSuccessors(&temp);
                
                for(set<BasicBlock*>::iterator succ = succrs->begin(); succ != succrs->end(); succ++){
                    set<pair<Instruction *, string>> succset = IN.find(*succ)->second;    // the successor's IN set
                    bbOUT.insert(succset.begin(), succset.end());    // add to OUT
                }
                
                set<pair<Instruction *, string>> newout_woDEF;
                set<pair<Instruction *, string>> newout_withDEF;
                
                for(set<pair<Instruction *,string>>::iterator i = bbOUT.begin() ; i != bbOUT.end(); i++){
                    // OUT_woDEF(X) = (OUT(X) - DEF(X))
                    if(!is_inDEF(&temp, i->second)){
                        newout_woDEF.insert(pair<Instruction *, string>(i->first, i->second));
                    }
                    //OUT_withDEF(X)
                    if(is_inDEF(&temp, i->second) && getPC_inDEF(&temp, i->second) != i->first){
                        
                        newout_withDEF.insert(pair<Instruction *, string>(i->first, i->second));
                        btd_table.insert(pair<pair<Instruction *, string>, Instruction *>(pair<Instruction *, string>(i->first, i->second), getPC_inDEF(&temp, i->second)));
                    }
                }
                
                // IN = USE(X) + OUT_woDEF(X)
                bbIN = bbUSE;                // value by value copy
                bbIN.insert(newout_woDEF.begin(), newout_woDEF.end());
                
                if (old_in != bbIN)
                    change = true;
            }
        }
    }
        
    private:  void printUSEDEF(int bb_number, BasicBlock *bb){
        if (USE.count(bb) < 1 || DEF.count(bb) < 1) return ; // throw exception
        
        errs() << "BASIC BLOCK[" << bb_number << "]" << "\n";
        
        errs() <<  "  USE  : \n";
        printVars(USE.find(bb)->second);
        
        errs() <<  "  DEF : \n";
        printVars(DEF.find(bb)->second);
        
    }
    private:  void printINOUT(int bb_number, BasicBlock *bb){
        if (IN.count(bb) < 1 || OUT.count(bb) < 1) return ; // throw exception
        
        errs() << "BASIC BLOCK[" << bb_number << "]" << "\n";
        
        errs() <<  "  IN  : ";
        printVars(IN.find(bb)->second);
        
        errs() <<  "  OUT : ";
        printVars(OUT.find(bb)->second);
        
    }
        
    private:  void printTable(map<pair<Instruction *, string>, Instruction *> table){
        errs() << "\n\n\n";
        errs() << "######################### Backward Taint Analysis Table Data #########################" << "\n";
        map<pair<Instruction *, string>, Instruction *>::iterator iter;
        unsigned useLine, defLine;
        StringRef File, Dir;
        
        for(iter = table.begin() ; iter != table.end() ; iter++ ){
            if (DILocation *uLoc = ((iter->first).first)->getDebugLoc()) {
                useLine = uLoc->getLine();
            }
            if (DILocation *Loc = (iter->second)->getDebugLoc()) { // Here I is an LLVM instruction
                defLine = Loc->getLine();
                File = Loc->getFilename();
                Dir = Loc->getDirectory();
            }
            
            string src_val = (iter->second)->getOperand(0)->getName();
            
            errs() << "<<USE line "<< useLine << " : " << (iter->first).first << ", " << (iter->first).second << ">, DEF line "<< defLine << " : " << iter->second << " > \n\n";
        }
        errs() << "#######################################################################################" << "\n";
    }
        
    private:  void printVars(set<pair<Instruction *, string>> vars) {
        for( set<pair<Instruction *, string>>::iterator v = vars.begin(); v != vars.end(); v++)
            errs() << "Intstruction address : " << v->first << "         variable : " << v->second << "\n" ;
        errs() << "\n";
    }
    };
}

char Coffee::ID = 1;
static RegisterPass<Coffee> X("coffee", "LV Pass");
