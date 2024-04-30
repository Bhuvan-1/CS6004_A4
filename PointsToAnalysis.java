import java.util.*;
import soot.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.SimpleLiveLocals;
import soot.toolkits.scalar.LiveLocals;

import soot.jimple.AnyNewExpr;
import soot.jimple.FieldRef;
import soot.jimple.IdentityRef;
import soot.jimple.ParameterRef;
import soot.jimple.StaticFieldRef;
import soot.jimple.ThisRef;
import soot.jimple.internal.*;
import soot.toolkits.scalar.BackwardFlowAnalysis;
import soot.toolkits.scalar.FlowSet;
import soot.toolkits.scalar.ForwardFlowAnalysis;


/*
 * This analysis does an inter - procedural points to analysis for all the methods reachable from main
 * Also this removes the methods that are not reachable from main.
 * This info will be used in the later stages to find out which objects escape and which can be Scalar Replaced etc.
 */

public class PointsToAnalysis {
    CallGraph cg;
    Set<SootMethod> methods;
    public Map<String, PTOG> exit_ptogs;
    public Map<String, Set<String> > all_escapes;       //DOES NOT INCLUDE RETURNS.
    public Map<String, Set<String> > returns;
    public Map<String, Set<String> > return_objs;
    public Map<String, List<Local> > params_list;
    public Map<SootMethod, Map<Unit, PTOG>> ptsToInfoOut;
    public Map<SootMethod, Map<Unit, PTOG>> ptsToInfoIn;

    public PointsToAnalysis( CallGraph cg , Set<SootMethod> methods ){
        this.cg = cg;
        this.methods = methods;

        ptsToInfoOut = new HashMap<>();
        ptsToInfoIn = new HashMap<>();

        exit_ptogs = new HashMap<>();
        all_escapes = new HashMap<>();
        returns = new HashMap<>();
        return_objs = new HashMap<>();
        params_list = new HashMap<>();
    }


    public Set<String> get_objs_field(String base, String field, PTOG in){
        Set<String> newobjs = new HashSet<>();

        if ( !in.Stack.containsKey(base) ){
            return newobjs;
        }

        Set<String> objs = in.Stack.get(base);
        for ( String obj : objs ){
            if ( obj.contains("_") ){
                newobjs.add(obj);
            }

            if ( !in.Heap.containsKey(obj) || !in.Heap.get(obj).containsKey(field) ){
                continue;
            }

            newobjs.addAll( in.Heap.get(obj).get(field) );
        }
        return newobjs;
    }
    
    public void set_objs_field(String base, String field, Set<String> objs, PTOG out){

        if ( !out.Stack.containsKey(base) ){
            return;
        }

        Set<String> oldobjs = out.Stack.get(base);
        for ( String obj : oldobjs ){
            if ( !out.Heap.containsKey(obj) ){
                out.Heap.put(obj, new HashMap<>());
            }
            if ( !out.Heap.get(obj).containsKey(field) ){
                out.Heap.get(obj).put(field, new HashSet<>());
            }
            out.Heap.get(obj).get(field).addAll(objs);
        }
    }

    public Set<String> get_objs( Unit u, Value rvalue, PTOG in ){
            Set<String> ret = new HashSet<>();

            if ( rvalue instanceof JimpleLocal ){
                JimpleLocal jl = (JimpleLocal) rvalue;
                String var = jl.getName();

                if ( in.Stack.containsKey(var) ){
                    ret.addAll( in.Stack.get(var) );
                }
            }
            else if (rvalue instanceof JNewExpr ){
                int linenum = u.getJavaSourceStartLineNumber();
                ret.add( Integer.toString(linenum) );
            }
            else if (rvalue instanceof JArrayRef ){
                String var = ((JimpleLocal) ((JArrayRef) rvalue).getBase()).getName();
                return get_objs_field(var, "[]", in);
            }
            else if (rvalue instanceof JInstanceFieldRef ){

                String var = ((JimpleLocal) ((JInstanceFieldRef) rvalue).getBase()).getName();
                String field = ((JInstanceFieldRef) rvalue).getField().getName();
                return get_objs_field(var, field, in);
            }
            else if (rvalue instanceof StaticFieldRef ){
                String field = ((StaticFieldRef) rvalue).getField().getName();
                return get_objs_field("this", field, in);
            }
            else if( rvalue instanceof JNewArrayExpr ){
                int linenum = u.getJavaSourceStartLineNumber();
                ret.add( Integer.toString(linenum) );
            }
            else if( rvalue instanceof JNewMultiArrayExpr){
                int linenum = u.getJavaSourceStartLineNumber();
                ret.add( Integer.toString(linenum) );
            }
            else if( rvalue instanceof JCastExpr ){
                String var = ((JimpleLocal) ((JCastExpr) rvalue).getOp()).getName();
                
                if ( in.Stack.containsKey(var) ){
                    ret.addAll( in.Stack.get(var) );
                }
            }
            else if( rvalue instanceof JVirtualInvokeExpr || rvalue instanceof JStaticInvokeExpr ){
                ret.add("O_dummy*");
            }

            return ret;
    }

    public Set<String> get_reachable_objs( String var, PTOG out ){
        Set<String> reachable_objs = new HashSet<>();
        Set<String> to_process = new HashSet<>();
        if (! out.Stack.containsKey(var) ){
            return reachable_objs;
        }

        to_process.addAll( out.Stack.get(var) );

        while( !to_process.isEmpty() ){
            String obj = to_process.iterator().next();

            reachable_objs.add(obj);
            to_process.remove(obj);

            if ( !out.Heap.containsKey(obj) ){
                continue;
            }

            for ( String field : out.Heap.get(obj).keySet() ){
                for ( String obj_ : out.Heap.get(obj).get(field) ){
                    if ( !reachable_objs.contains(obj_) ){
                        to_process.add(obj_);
                    }
                }
            }
        }

        return reachable_objs;
    }

    public Set<String> get_reachable_objs_heap( String var, PTOG out){
        Set<String> reachable_objs = new HashSet<>();
        Set<String> to_process = new HashSet<>();
        if (! out.Heap.containsKey(var) ){
            return reachable_objs;
        }

        to_process.add(var);

        while( !to_process.isEmpty() ){
            String obj = to_process.iterator().next();

            reachable_objs.add(obj);
            to_process.remove(obj);

            if ( !out.Heap.containsKey(obj) ){
                continue;
            }

            for ( String field : out.Heap.get(obj).keySet() ){
                for ( String obj_ : out.Heap.get(obj).get(field) ){
                    if ( !reachable_objs.contains(obj_) ){
                        to_process.add(obj_);
                    }
                }
            }
        }

        return reachable_objs;
    }

    public Set<String> get_param_escapes( Body body, PTOG out ){
        Set<String> escapes = new HashSet<>();
        List<Local> params = body.getParameterLocals();

        for (Local param : params){

            Type paramtype = param.getType();
            String param_name = param.getName();
            if(! (paramtype instanceof RefType || paramtype instanceof ArrayType) ){
                continue;
            }

            // No need to check for key, coz its already checked in get_reach_objs
            escapes.addAll( get_reachable_objs_heap("O_" + param_name, out) );
        }
        return escapes;
    }

    public Set<String> get_field_escapes( PTOG out){
        return get_reachable_objs("this", out);
    }

    public Set<String> get_all_escapes(Body body, PTOG out ){
        Set<String> ret = new HashSet<>();

        ret.addAll( get_param_escapes(body, out) );
        ret.addAll( get_field_escapes(out));
        ret.addAll( get_reachable_objs_heap("O_dummy*", out) );
        ret.addAll( get_reachable_objs_heap("O_this", out) );

        return ret;
    }

    public void patch(PTOG callr,  PTOG rcv , List<Local> call_params, List<Local> rcv_params, Set<String> return_objs){
        // merge the ptsto info for caller and that of receiver... callle ptog only for the parameters
        //If O_p in rcvr is poinitng to some objects.. and the same parameter points to O1 in callr
        // then O1 should include ALL the info as reachbale from O_p

        Set<String> visited = new HashSet<>();
        Set<String> to_process = new HashSet<>();
        Map<String, String> rcv2callr = new HashMap<>();

        for ( int i = 0; i < call_params.size(); i++ ){
            Local param = call_params.get(i);
            if( param == null ) continue;

            Type type = param.getType();

            if(! (type instanceof RefType || type instanceof ArrayType) ){
                continue;
            }

            String caller_param_name = param.getName();
            String receiver_param_name = rcv_params.get(i).getName();
            String obj_name = "O_" + receiver_param_name;
            
            rcv2callr.put(obj_name, caller_param_name);
            to_process.add(obj_name);
        }

        to_process.addAll(return_objs);
        
        while( !to_process.isEmpty() ){
            String obj = to_process.iterator().next();
            to_process.remove(obj);
            visited.add(obj);

            if ( !rcv.Heap.containsKey(obj) ){
                continue;
            }

            for ( String field : rcv.Heap.get(obj).keySet() ){
                for ( String obj_ : rcv.Heap.get(obj).get(field) ){
                    if ( !visited.contains(obj_) ){
                        to_process.add(obj_);
                    }
                }
            }

            Set<String> lhs_objs = new HashSet<>();
            if( obj.contains("_") ){
                if( rcv2callr.containsKey(obj) ){
                    lhs_objs = callr.Stack.get(rcv2callr.get(obj));
            
                }
            }
            else{
                lhs_objs.add(obj);
            }

            for ( String lhs_obj : lhs_objs ){
                if ( !callr.Heap.containsKey(lhs_obj) ){
                    callr.Heap.put(lhs_obj, new HashMap<>());
                }

                for ( String field : rcv.Heap.get(obj).keySet() ){
                    if ( !callr.Heap.get(lhs_obj).containsKey(field) ){
                        callr.Heap.get(lhs_obj).put(field, new HashSet<>());
                    }

                    for( String obj_ : rcv.Heap.get(obj).get(field) ){
                        if( obj_.contains("_") && rcv2callr.containsKey(obj_) ){
                            callr.Heap.get(lhs_obj).get(field).addAll( callr.Stack.get(rcv2callr.get(obj_)) );
                        }
                        else if(! obj_.contains("_")){
                            callr.Heap.get(lhs_obj).get(field).add(obj_);
                        }
                    }
                }
            }

        }

    }

    public Set<String> patch_objs(Set<String> ret_objs,  PTOG callr, List<Local> call_params, List<Local> rcv_params ){
        Set<String> ret = new HashSet<>();
        Map<String, String> rcv2callr = new HashMap<>();

        for ( int i = 0; i < call_params.size(); i++ ){
            Local param = call_params.get(i);
            if( param == null ) continue;

            Type type = param.getType();

            if(! (type instanceof RefType || type instanceof ArrayType) ){
                continue;
            }

            String caller_param_name = param.getName();
            String receiver_param_name = rcv_params.get(i).getName();
            String obj_name = "O_" + receiver_param_name;
            
            rcv2callr.put(obj_name, caller_param_name);
        }

        for ( String obj : ret_objs ){
            if( obj.contains("_") && rcv2callr.containsKey(obj) ){
                if( callr.Stack.containsKey(rcv2callr.get(obj)) ) ret.addAll( callr.Stack.get(rcv2callr.get(obj)) );
            }
            else if(!obj.contains("_")){
                ret.add(obj);
            }
        }

        return ret;
    }

    public Set<String> handle_func_call(Unit u, Value v, PTOG out){
        List<Value> args;
        Set<String> objs = new HashSet<>();

        //if it is a library function, then we don't need to do anything
        if( v instanceof JStaticInvokeExpr ){
            JStaticInvokeExpr expr = (JStaticInvokeExpr) v;
            if( expr.getMethod().isJavaLibraryMethod() ){
                return objs;
            }
            args = expr.getArgs();
        }
        else if(v instanceof JVirtualInvokeExpr){
            JVirtualInvokeExpr expr = (JVirtualInvokeExpr) v;
            if( expr.getMethod().isJavaLibraryMethod()  ){
                return objs;
            }
            args = expr.getArgs();
        }
        else{
            return objs;
        }


        //Need to get all possible calllee's... considering inheritance using the call graph
        List<String> callees = new ArrayList<>();
        Iterator<Edge> edges = cg.edgesOutOf(u);
        while (edges.hasNext()) {
            Edge edge = edges.next();
            SootMethod target = edge.tgt();
            String key = target.getDeclaringClass() + ":" + target.getName();
            callees.add(key);
        }


        List<Local> call_params = new ArrayList<>();
        for ( Value arg : args ){
            if( arg instanceof JimpleLocal ){
                call_params.add( (JimpleLocal) arg );
            }
            else call_params.add(null);
        }

        PTOG callr_ptg = new PTOG();

        for( String key : callees ){
            PTOG tmp = out.clone();
            PTOG return_ptog = exit_ptogs.get(key);
            objs.addAll( this.patch_objs( returns.get(key), out, call_params, params_list.get(key) ) );
            this.patch(tmp, return_ptog, call_params, params_list.get(key) , return_objs.get(key) );

            callr_ptg.union(tmp);
        }

        out.union(callr_ptg);

        return objs;
    }

    public void doAnalysis() {
        // Create a graph of methods
        Map<SootMethod, Set<SootMethod>> methodGraph = new HashMap<>();
        for (SootMethod m : methods) {
            methodGraph.put(m, new HashSet<>());
        }

        // Populate the graph
        for (SootMethod m : methods) {
            Iterator<Edge> edges = cg.edgesOutOf(m);
            while (edges.hasNext()) {
                Edge edge = edges.next();
                SootMethod target = edge.tgt();
                if (methods.contains(target)) {
                    methodGraph.get(m).add(target);
                }
            }
        }

        // Topological sort
        List<SootMethod> sortedMethods = new ArrayList<>();
        Set<SootMethod> visited = new HashSet<>();
        while( sortedMethods.size() < methods.size() ) {
            for (SootMethod m : methods) {
                if (!visited.contains(m) && methodGraph.get(m).stream().allMatch(visited::contains)) {
                    sortedMethods.add(m);
                    visited.add(m);
                }
            }
        }

        for (SootMethod m : sortedMethods) {
            if( m.toString().contains("init") ) { continue; }
            processCFG(m);
        }

    }

    protected void processCFG(SootMethod method) {
        Body body = method.getActiveBody();
        UnitGraph cfg = new BriefUnitGraph(body);
        PatchingChain<Unit> units = body.getUnits();
        
        Map<Unit, PTOG> in = new HashMap<>();
        Map<Unit, PTOG> out = new HashMap<>();
        ptsToInfoIn.put(method, in);
        ptsToInfoOut.put(method, out);
        
        for (Unit u : units) {
            in.put(u, new PTOG());
            out.put(u, new PTOG());
        }

        List<Local> params = body.getParameterLocals();

        for( Unit entry_ : cfg.getHeads() ){
            PTOG start = in.get( entry_ );
            start.Stack.put("this", new HashSet<>());
            start.Stack.get("this").add("O_this");

            //All params of func point to O_P where P is the parameter name

            for (Local param : params){

                Type paramtype = param.getType();
                if(! (paramtype instanceof RefType || paramtype instanceof ArrayType) ){
                    continue;
                }

                start.Stack.put(param.getName(), new HashSet<>());
                start.Stack.get(param.getName()).add("O_" + param.getName());
            }
        }

        Map<Unit, PTOG> out_ = new HashMap<>();

        boolean changed = true;
        

        while (true){
            if(!changed ) break;
            for (Unit u : units) {
                out_.put(u, out.get(u).clone());
            }

            for (Unit u : units) {
                
                if(! cfg.getPredsOf(u).isEmpty() ){
                    PTOG ptog = new PTOG();
                    for( Unit pred : cfg.getPredsOf(u) ){
                        ptog.union( out.get(pred) );
                    }
    
                    in.put(u, ptog);                
                }

                out.put(u, in.get(u).clone());

                if (u instanceof JAssignStmt) {
                    JAssignStmt stmt = (JAssignStmt) u;
                    Value rhs = stmt.getRightOp();
                    Value lhs = stmt.getLeftOp();
                    
                    Set<String> objs;
                    if( rhs instanceof JVirtualInvokeExpr || rhs instanceof JStaticInvokeExpr ){
                        objs = handle_func_call(u, rhs, out.get(u));
                    }
                    else {
                        objs = get_objs(u, rhs, in.get(u));
                    }


                    Type lhstype = lhs.getType();
                    //If rhs type is not an object, then we don't need to do anything
                    if (! (lhstype instanceof RefType || lhstype instanceof ArrayType) ){
                        continue;
                    }

                    if( lhs instanceof JimpleLocal ){
                        String var = ((JimpleLocal) lhs).getName();
                        out.get(u).Stack.put(var, objs);
                    }
                    else if( lhs instanceof JInstanceFieldRef){
                        String var = ((JimpleLocal) ((JInstanceFieldRef) lhs).getBase()).getName();
                        String field = ((JInstanceFieldRef) lhs).getField().getName();	//Dummy object escapes.
                        set_objs_field(var, field,objs, out.get(u));
                    }
                    else if( lhs instanceof StaticFieldRef){
                        String field = ((StaticFieldRef) lhs).getField().getName();
                        set_objs_field("this", field, objs, out.get(u));
                    }
                    else if ( lhs instanceof JArrayRef ){
                        String var = ((JimpleLocal) ((JArrayRef) lhs).getBase()).getName();
                        set_objs_field(var, "[]", objs, out.get(u));
                    }
                }
                else if ( u instanceof JIdentityStmt ){
                    JIdentityStmt stmt = (JIdentityStmt) u;
                    Value lhs = stmt.getLeftOp();
                    String lhs_name = ((JimpleLocal)lhs).getName();

                    Value rhs = stmt.getRightOp();
                    String rhs_name = "";

                    if( rhs instanceof ThisRef ){
                        rhs_name = "this";
                    }
                    else if( rhs instanceof ParameterRef ){
                        int idx = ((ParameterRef) rhs).getIndex();
                        rhs_name = body.getParameterLocal(idx).getName();
                    }
                    
                    //Here even scalar params are added.. but ok... removed in the check.
                    if(! lhs_name.equals(rhs_name) ){
                        if( out.get(u).Stack.containsKey(rhs_name) ){
                            out.get(u).Stack.put( lhs_name, new HashSet<>() );
                            out.get(u).Stack.get(lhs_name).addAll( out.get(u).Stack.get(rhs_name) );
                        }
                    }
                }
                else if ( u instanceof JInvokeStmt ){
                    JInvokeStmt stmt = (JInvokeStmt) u;
                    Value expr = stmt.getInvokeExpr();
                    handle_func_call(u, expr, out.get(u));
                }
                // else{
                //     out.put(u, ptog.clone());
                // }
            }
    
            
            changed = false;
            for (Unit u : units) {
                if( out.get(u).different(out_.get(u)) ){
                    changed = true;
                    break;
                }
            }

        }

        String mthd_name = method.getDeclaringClass() + ":" + method.getName();

        PTOG exit_ptog = new PTOG();
        Set<String> rets = new HashSet<>();
        Set<String> ret_objs = new HashSet<>();
        for( Unit u : cfg.getTails() ){
            exit_ptog.union(out.get(u));

            if( u instanceof JReturnStmt ){
                JReturnStmt stmt = (JReturnStmt) u;
                Value ret = stmt.getOp();
                Type rettype = ret.getType();
                if( ret instanceof JimpleLocal && (rettype instanceof RefType || rettype instanceof ArrayType) ){
                    String var = ((JimpleLocal) ret).getName();
                    if( out.get(u).Stack.containsKey(var) ){
                        rets.addAll( out.get(u).Stack.get(var) );
                        ret_objs.addAll( get_reachable_objs(var, out.get(u)) );
                    }
                }
            }

        }

        exit_ptogs.put(mthd_name, exit_ptog);
        returns.put(mthd_name, rets);
        return_objs.put(mthd_name, ret_objs);
        params_list.put(mthd_name, params);

        Set<String> escapes = get_all_escapes(body, exit_ptog);
        // escapes.addAll(ret_objs);
        all_escapes.put(mthd_name, escapes);

    }

}
