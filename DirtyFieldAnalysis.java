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
 *  We do reconstruction at method calls and parameter sends and returns
 * 
 * out[u][x] has the set of fields f that are different from the object pointedby x. 
 *      If x changed inside u, we dont care bcz the prev obj is going to be garbage collected.. since we are working with an assumption that reference of x wont be escpaed to any other local
 * int[u][x] has the set of fields f that are different from the object(incoming) pointed by x
 * 
 * Here we take the assumption that a reconstruction is done whenever necessary... and we treat an unit u as a hybrid of | reconstruction + u |
 * Basically at any objectified usage of x... we will reconstruct the fields based on in[]. 
 * And we take this into consideratin in the analysis also, by ensuring that the out of such objectified statements is empty set bcz the object is up to date.
 */

public class DirtyFieldAnalysis {
    Set<SootMethod> methods;
    Map<SootMethod, Map<Unit, Map<Local, Set<String>>> > in;
    Map<SootMethod, Map<Unit, Map<Local, Set<String>>> > out;

    public DirtyFieldAnalysis( Set<SootMethod> methods) {
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

        Set<Unit> worklist = new HashSet<>();

        for(Unit u : units){
            worklist.add(u);
        }

        while( true){
            Map<Unit, Map<Local, Set<String>> > old_out = new HashMap<>( );
            for(Unit u : units){
                old_out.put(u, new HashMap<>());
                for(Local l : body.getLocals()){
                    if(l.getType() instanceof RefType){
                        old_out.get(u).put(l, new HashSet<>(out.get(u).get(l)));
                    }
                }
            }


            for(Unit u : units){
                

                //Geting the in set of u form all its predecessors, copying it to out set of u
                for(Local l : body.getLocals()){
                    if(l.getType() instanceof RefType){
                        in.get(u).get(l).clear();
                        out.get(u).get(l).clear();
                        for( Unit pred : cfg.getPredsOf(u) ){
                            in.get(u).get(l).addAll(out.get(pred).get(l));
                        }
                        out.get(u).get(l).addAll(in.get(u).get(l));
                    }
                }


                if(u instanceof JAssignStmt ){
                    JAssignStmt stmt = (JAssignStmt) u;
                    Value right = stmt.getRightOp();
                    Value left = stmt.getLeftOp();

                    if(right instanceof JVirtualInvokeExpr || right instanceof JStaticInvokeExpr
                         || right instanceof JInterfaceInvokeExpr || right instanceof JSpecialInvokeExpr){
                        for(ValueBox vb : right.getUseBoxes()){
                            if(vb.getValue() instanceof Local){
                                Local l = (Local) vb.getValue();
                                if(l.getType() instanceof RefType) out.get(u).get(l).clear();
                            }
                        }
                    }

                    if(left instanceof Local && left.getType() instanceof RefType){
                        Local l = (Local) left;
                        out.get(u).get(l).clear();
                    }
                    else if(left instanceof JInstanceFieldRef){
                        JInstanceFieldRef ref = (JInstanceFieldRef) left;
                        Local base = (Local) ref.getBase();
                        String field = ref.getField().getName();
                        out.get(u).get(base).add(field);
                    }
                }
                else if(u instanceof JInvokeStmt){
                    //All the involved locals are empty in the out set.
                    for(ValueBox vb : u.getUseBoxes()){
                        if(vb.getValue() instanceof Local){
                            Local l = (Local) vb.getValue();
                            if(l.getType() instanceof RefType) out.get(u).get(l).clear();
                        }
                    }
                }
                else if(u instanceof JReturnStmt ){
                    for(Local l : out.get(u).keySet()){
                        out.get(u).get(l).clear();
                    }
                }

            }

    
            boolean changed = false;
            for(Unit u : units){
                if(changed) break;
                for(Local l : body.getLocals()){
                    if(! (l.getType() instanceof RefType) ) continue;
                    if( !old_out.get(u).get(l).equals(out.get(u).get(l)) ){
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
                    System.out.print("\tLocal: " + l);
                    System.out.print(" In: " + in.get(u).get(l));
                    System.out.println(" Out: " + out.get(u).get(l));
                }
            }
        }
    }
}
