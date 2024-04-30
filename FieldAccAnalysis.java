import java.util.*;
import soot.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.SimpleLiveLocals;
import soot.toolkits.scalar.LiveLocals;

import soot.jimple.*;
import soot.jimple.internal.*;
import soot.toolkits.scalar.BackwardFlowAnalysis;
import soot.toolkits.scalar.FlowSet;
import soot.toolkits.scalar.ForwardFlowAnalysis;


/*
 *  We do an analysis to compute in, out sets at each unit for each local, which stores this info
 * 
 * out[u][x] has the set of fields f such that x.f is used in some path from u to exit EXCLUDING u without a redefinition of x.
 * int[u][x] has the set of fields f such that x.f is defined in some path from u to exit INCLUDING u without a redefinition of x.
 *
 * We do this, to know which fields of a current redefinition of x to take a copy of
 * some fields may be set, but not used.. in such case we need not take a snapshot.. but we need to translate those changes after that
 * 
 * We do this optimimization only for those locals, whose reference is not escaped or assigned to some other variable.
 * If thereference gets leaked, then the object can be modified or used by some other variable creating a lot of issues i think
 * and its hard to think how to get over that issue...? maybe try to track field accesses based on objects, not on locals etc etc ideas
 * 
 * So We decided to just apply the optimization for the following simple case.
 * local x is assined to new() AND
 *      1) it is not copied to some y = x
 *      2) it can be passed as arg to f(x,....) or maybe x.f(.....) In this case x must not escape and also the return value of function
 *          should not have the reference to x ( atleast it should not be captured by some lhs)
 *          basically x should not alias to any other variable even after the call
 *          In this case, we can restore the dirty fields of x in x.f before the call to keep the object consistent
 *      
 *      3) We should do the same with return x as well, try to re construct the dirty fields of x in x.f after the call
 *      
 * 
 * 
 *      4) all the field loads, stores are handled by scalar replaced fields corresponding to x 
 *      5) this is limited to non static fields only, static fields and their accesses are left un touched
 * 
 *      we ignore arrays ovbiously
 * 
 *      6) x should also not be assigned to anything else except x = new()....in such a case, we can igore updating fields of the older x.
 * 
 * 
 * SO WE NEED TO MAKE A SORT OF DIRTY FIELD ANALYSIS TO SAY WHICH FIELDS TO RECONSTRUCT.
 * THIS, I THINK CAN BE A FORWARD ANALYSIS???
 */

public class FieldAccAnalysis {
    Set<SootMethod> methods;
    Map<SootMethod, Map<Unit, Map<Local, Set<String>>> > in;
    Map<SootMethod, Map<Unit, Map<Local, Set<String>>> > out;

    public FieldAccAnalysis( Set<SootMethod> methods) {
        this.methods = methods;
        in = new HashMap<>();
        out = new HashMap<>();
    }

    public void doAnalysis() {

        for (SootMethod m : methods) {
            if( m.toString().contains("init") ) { continue; }
            processCFG(m);
        }

    }

    public void processCFG(SootMethod method) {
        Body body = method.getActiveBody();
        UnitGraph cfg = new BriefUnitGraph(body);
        PatchingChain<Unit> units = body.getUnits();


        Map<Unit, Map<Local, Set<String>>> in = new HashMap<>();
        Map<Unit, Map<Local, Set<String>>> out = new HashMap<>();
        for(Unit u : units){
            in.put(u, new HashMap<>());
            out.put(u, new HashMap<>());

            for(Local l : body.getLocals()){

                if(l.getType() instanceof RefType){
                    in.get(u).put(l, new HashSet<>());
                    out.get(u).put(l, new HashSet<>());
                }
            }

        }

        while( true ){

            Map<Unit, Map<Local, Set<String>>> old_in = new HashMap<>();
            for(Unit u : units){
                old_in.put(u, new HashMap<>());
                for(Local l : body.getLocals()){
                    if(l.getType() instanceof RefType){
                        old_in.get(u).put(l, new HashSet<>(in.get(u).get(l)));
                    }
                }
            }

            for(Unit u : units){
                //Geting the out set of u form all its successors, copying it to in set of u
                for(Local l : body.getLocals()){
                    if(l.getType() instanceof RefType){
                        out.get(u).get(l).clear();
                        in.get(u).get(l).clear();
                        for( Unit succ : cfg.getSuccsOf(u) ){
                            out.get(u).get(l).addAll(in.get(succ).get(l));
                        }
                        in.get(u).get(l).addAll(out.get(u).get(l));
                    }
                }



                if(u instanceof JAssignStmt ){
                    JAssignStmt stmt = (JAssignStmt) u;
                    Value right = stmt.getRightOp();
                    Value left = stmt.getLeftOp();

                    if(left instanceof Local && left.getType() instanceof RefType){
                        Local l = (Local) left;
                        in.get(u).get(l).clear();
                    }

                    if(right instanceof JInstanceFieldRef){
                        JInstanceFieldRef ref = (JInstanceFieldRef) right;
                        Local base = (Local) ref.getBase();
                        String field = ref.getField().getName();
                        in.get(u).get(base).add(field);
                    }
                    else if(left instanceof JInstanceFieldRef){
                        JInstanceFieldRef ref = (JInstanceFieldRef) left;
                        Local base = (Local) ref.getBase();
                        String field = ref.getField().getName();
                        in.get(u).get(base).remove(field);
                    }

                }
            }
    
            boolean changed = false;
            for(Unit u : units){
                if(changed) break;
                for(Local l : body.getLocals()){
                    if(! (l.getType() instanceof RefType) ) continue;
                    if( !old_in.get(u).get(l).equals(in.get(u).get(l)) ){
                        changed = true;
                        break;
                    }
                }
            }

            if(!changed) break;
        }
        this.in.put(method, in);
        this.out.put(method, out);
    }

    public void print(){
        for(SootMethod m : methods){
            if( m.toString().contains("init") ) { continue; }
            System.out.println("=====================================================");
            System.out.println("Method: " + m);
            Map<Unit, Map<Local, Set<String>>> in = this.in.get(m);
            Map<Unit, Map<Local, Set<String>>> out = this.out.get(m);
            for(Unit u : m.getActiveBody().getUnits()){
                System.out.println("Unit: " + u);
                for(Local l : in.get(u).keySet()){
                    if(in.get(u).get(l).isEmpty() && out.get(u).get(l).isEmpty()){
                        continue;
                    }
                    System.out.print("\tLocal: " + l);
                    System.out.print(" In: " + in.get(u).get(l));
                    System.out.println(" Out: " + out.get(u).get(l));
                }
            }
        }
    }
}
