import java.util.*;
import soot.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.tagkit.LineNumberTag;
import soot.toolkits.graph.*;
import soot.util.Chain;
import soot.util.EmptyChain;

import soot.jimple.*;
import soot.jimple.internal.*;



public class AnalysisTransformer extends SceneTransformer {
    static CallGraph cg;
    static Map<SootMethod, Body> methodToBody = new HashMap<>();
    static int INLINED_LINES = 9999;

    List<SootMethod> toposort(Set<SootMethod> methods){
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

        return sortedMethods;
    }


    @Override
    protected void internalTransform(String arg0, Map<String, String> arg1) {
        Set<SootMethod> methods = new HashSet <>();
        SootMethod mainMethod = Scene.v().getMainMethod();

        cg = soot.Scene.v().getCallGraph();


        // Get the main method
        // Get the list of methods reachable from the main method
        // Note: This can be done bottom up manner as well. Might be easier to model.
        getlistofMethods(mainMethod, methods);

        for (SootMethod m : methods) {
            if( m.toString().contains("init") ) { continue; }
            methodToBody.put(m, m.getActiveBody());
        }

        for (SootMethod m : methods) {
            if( m.toString().contains("init") ) { continue; }
            processCFG(m);
        }

        PointsToAnalysis pta = new PointsToAnalysis(cg, methods);
        pta.doAnalysis();

        FieldAccAnalysis faa = new FieldAccAnalysis(methods);
        faa.doAnalysis();
        // faa.print();

        DirtyFieldAnalysis dfa = new DirtyFieldAnalysis(methods);
        dfa.doAnalysis();
        // dfa.print();


        FPAnalysis fpa = new FPAnalysis( pta );
        fpa.doAnalysis();
        fpa.print();

        for( SootMethod m : methods ){
            if(m.toString().contains("init")) continue;
            transformFP(m, faa, dfa, fpa);
        }

        for( SootMethod m : methods ){
            if(m.toString().contains("init")) continue;
            m.getActiveBody().validate();
            print(m);
        }

    }

    
    //!!?? @todo : if soot cg is not good enough, then try to use the points to analysis to get the receiver class type and 
    // if it can be solved monomorphically, then inline; Maybe change the return type of this func to SootMethod.

    //!! also do the inlinign in a topologically sorted way....
    //and deal with loops as well.
    //AND DONT INLINE A FUNC INSIDE ITSELF MORE THAN 1 level... take care of all these thiungs.
    //ALSO MULTIPLE INLINES OF SAME METHD...USE SAME LOCALS.

    private Edge checkMonomorphicIterator(Iterator<Edge> receviers) {
        int count = 0;
        Edge ret = null;
        while( receviers.hasNext() ) {
            ret = receviers.next();
            count++;
        }
        return count == 1 ? ret : null;
    }

    private void transformFP(SootMethod m, FieldAccAnalysis faa, DirtyFieldAnalysis dfa, FPAnalysis fpa) {
        Body body = m.getActiveBody();
        Chain<Local> locals = body.getLocals();

        PatchingChain<Unit> units = body.getUnits();
        Iterator<Unit> unitIt = units.snapshotIterator();

        Set<Local> valid = fpa.valid_locals.get(m);
        Map<Local, Set<String>> all_fields = fpa.all_fields.get(m);

        Map<Unit, Map<Local, Set<String>>> in_dfa = dfa.in.get(m);

        Map<Unit, Map<Local, Set<String>>> out_faa = faa.out.get(m);

        Map<Local, Map<String,Local>> new_local_map = new HashMap<>();
        Map<Local, Map<String, SootFieldRef>> field_ref_map = fpa.field_refs.get(m);


        //System.out.println(field_ref_map);

        for(Local l : valid){
            new_local_map.put(l, new HashMap<>());
            for(String field : all_fields.get(l)){
                
                SootFieldRef fieldRef = field_ref_map.get(l).get(field);

                Local newLocal = Jimple.v().newLocal(l.getName() + "__" + field, fieldRef.type());
                locals.add(newLocal);
                new_local_map.get(l).put(field, newLocal);

                // SootClass sc = Scene.v().getSootClass( l.getType().toString() );
                // Type fieldType = sc.getFieldByName(field).getType();
                // SootFieldRef fieldRef = Scene.v().makeFieldRef(sc, field, fieldType, false);
                // field_ref_map.get(l).put(field, fieldRef);

            }
        }

        


        while (unitIt.hasNext()) {
            Unit u = unitIt.next();
            if( u instanceof JAssignStmt){
                JAssignStmt assignStmt = (JAssignStmt) u;
                Value rightOp = assignStmt.getRightOp();
                Value leftOp = assignStmt.getLeftOp();
                
                if(leftOp instanceof Local){
                    if(valid.contains(leftOp)){
                        for(String field : out_faa.get(u).get(leftOp)){
                            Local newLocal = new_local_map.get(leftOp).get(field);
                            SootFieldRef fieldRef = field_ref_map.get(leftOp).get(field);

                            Value rightOpField = Jimple.v().newInstanceFieldRef( (Local) leftOp, fieldRef);
                            AssignStmt assignStmtField = Jimple.v().newAssignStmt(newLocal, rightOpField);

                            units.insertAfter(assignStmtField, u);
                        }
                    }
                }
                else if( leftOp instanceof JInstanceFieldRef ){
                    JInstanceFieldRef fieldRef = (JInstanceFieldRef) leftOp;
                    Local base = (Local) fieldRef.getBase();
                    if(valid.contains(base)){
                        String field = fieldRef.getField().getName();
                        Local newLocal = new_local_map.get(base).get(field);
                        assignStmt.setLeftOp(newLocal);
                    }
                }

                if( rightOp instanceof JInstanceFieldRef ){
                    JInstanceFieldRef fieldRef = (JInstanceFieldRef) rightOp;
                    Local base = (Local) fieldRef.getBase();
                    if(valid.contains(base)){
                        String field = fieldRef.getField().getName();
                        Local newLocal = new_local_map.get(base).get(field);
                        assignStmt.setRightOp(newLocal);
                    }
                }
                else if( rightOp instanceof JVirtualInvokeExpr || rightOp instanceof JStaticInvokeExpr ||
                            rightOp instanceof JInterfaceInvokeExpr || rightOp instanceof JSpecialInvokeExpr ){
                    for(ValueBox vb : rightOp.getUseBoxes()){
                        if(vb.getValue() instanceof Local){
                            Local l = (Local) vb.getValue();
                            if(valid.contains(l)){
                                for(String field : in_dfa.get(u).get(l)){
                                    Local newLocal = new_local_map.get(l).get(field);
                                    SootFieldRef fieldRef = field_ref_map.get(l).get(field);

                                    Value lhs = Jimple.v().newInstanceFieldRef( l, fieldRef);
                                    AssignStmt newassignStmt = Jimple.v().newAssignStmt(lhs, newLocal);

                                    units.insertBefore(newassignStmt, u);
                                }
                            }
                        }
                    }
                }
            }
            else if(u instanceof JInvokeStmt){
                for(ValueBox vb : u.getUseBoxes()){
                    if(vb.getValue() instanceof Local){
                        Local l = (Local) vb.getValue();
                        if(valid.contains(l)){
                            for(String field : in_dfa.get(u).get(l)){
                                Local newLocal = new_local_map.get(l).get(field);
                                SootFieldRef fieldRef = field_ref_map.get(l).get(field);

                                Value leftOp = Jimple.v().newInstanceFieldRef( l, fieldRef);
                                AssignStmt assignStmt = Jimple.v().newAssignStmt(leftOp, newLocal);

                                units.insertBefore(assignStmt, u);
                            }
                        }
                    }
                }

            }
            else if(u instanceof JReturnStmt){
                Value op = ((JReturnStmt) u).getOp();
                if( op instanceof Local && valid.contains(op) ){
                    for(String field : in_dfa.get(u).get(op)){
                        Local newLocal = new_local_map.get(op).get(field);
                        SootFieldRef fieldRef = field_ref_map.get(op).get(field);

                        Value leftOp = Jimple.v().newInstanceFieldRef( op, fieldRef);
                        AssignStmt assignStmt = Jimple.v().newAssignStmt(leftOp, newLocal);

                        units.insertBefore(assignStmt, u);
                    }
                }
            }
        }

    }

    private void tranformInline(SootMethod callerMethod, Unit callsite, InvokeExpr invokeExpr, SootMethod targetMethod){
        Body callerBody = callerMethod.getActiveBody();
        Body targetBody = targetMethod.getActiveBody();
        PatchingChain<Unit> targetUnits = targetBody.getUnits();
        PatchingChain<Unit> callerUnits = callerBody.getUnits();

        Chain<Local> callerLocals = callerBody.getLocals();
        Map<Local, Local> localTranformMap = new HashMap<>();

        //Change the names of all local variables
        String prefix = targetMethod.getDeclaringClass().getName() + "_" + targetMethod.getName() + "_#" + callsite.getJavaSourceStartLineNumber() + "_";
        for (Local local : targetBody.getLocals()) {

            //System.out.println(local.getName() + " " + local.getType());

            Local newLocal = Jimple.v().newLocal(prefix + local.getName(), local.getType());
            callerLocals.add(newLocal);
            //IDEALLY NEED TO CHECK IF THE LOCAL IS ALREADY PRESENT @fix!!!
            // WE CAN COMMONLY USE SAME LOCALS FOR THE SAME INLINED METHOD

            localTranformMap.put(local, newLocal);
        }

        Local returnLocal = null;
        if( !( targetMethod.getReturnType() instanceof VoidType) ){
            returnLocal = Jimple.v().newLocal(prefix + "ret", targetMethod.getReturnType()); //Name change !?
            callerLocals.add(returnLocal);
        }
        Local thisLocal = null;
        if(invokeExpr instanceof VirtualInvokeExpr){
            thisLocal = (Local) ((VirtualInvokeExpr) invokeExpr).getBase();
        }

        List<Local> formalParams = targetBody.getParameterLocals();
        List<Value> args = invokeExpr.getArgs();
        
        //Parameters assignment
        for(int i = 0; i < formalParams.size(); i++){
            Local formalParam = formalParams.get(i);
            Value arg = args.get(i);
            AssignStmt assignStmt = Jimple.v().newAssignStmt( localTranformMap.get(formalParam), arg);
            callerUnits.insertBefore(assignStmt, callsite);
        }


        /*The following changes need to be made:
         *  Change all the locals
         *  Return should be captured and assigned to the returnLocal
         *  Returns should be re routed to the callsite with a goto statement 
         *  Need to add those statements in the beginning of the method that define these library classes etc 
         * This references should be changed to the receiver.<>
         */ 

        //The exit statement after inlining.. need to patch all returns inside the inlined method to this.
        //It the function is a void function or The callsite is just an invokestmt (NOT ASSIGN), then just a nopstmt
        //Else directly an assign statement to the returnLocal
        Unit exitStmt;

        if( callsite instanceof AssignStmt ){
            AssignStmt assignStmt = (AssignStmt) callsite;
            Local leftOp = (Local) assignStmt.getLeftOp();
            exitStmt = Jimple.v().newAssignStmt(leftOp, returnLocal);
        }
        else exitStmt = Jimple.v().newNopStmt();


        //First clone all units.. in order to patch UnitBoxes also
        /*
         * Unit.clone() deep clones the unit, ValueBoxes( Use and Def ) are cloned as well
         * But the Values in the UnitBoxes are not cloned, they are just referenced.
         * Same is true for UnitBoxes in the Unit.
         */
        Map<Unit,Unit> clonedUnits = new HashMap<>();
        for(Unit u : targetUnits){
            clonedUnits.put(u, (Unit)u.clone());
        }

        Iterator<Unit> targetUnitIterator = targetUnits.snapshotIterator();
        while( targetUnitIterator.hasNext() ){
            Unit u = targetUnitIterator.next();
            if(  u instanceof IdentityStmt ){
                if( ((IdentityStmt) u).getRightOp() instanceof ThisRef ){
                    Unit newUnit = Jimple.v().newAssignStmt(localTranformMap.get(((IdentityStmt) u).getLeftOp()), thisLocal);
                    callerUnits.insertBefore(newUnit, callsite);
                }
                continue;
            }

            /*
            * Need a clone of the given unit
            * We just need to transform the locals and this ref.
            * Constants might be re used since they are sort of like primitive objects.
            */

            Unit newUnit = clonedUnits.get(u);
            if(newUnit instanceof JAssignStmt){
                Value rhs = ((JAssignStmt) newUnit).getRightOp();
                if( rhs instanceof JNewExpr || rhs instanceof NewArrayExpr || rhs instanceof NewMultiArrayExpr ){
                    LineNumberTag tag = new LineNumberTag(INLINED_LINES++);
                    newUnit.addTag(tag);
                }
            }

            //Patching Locals, thisRef
            for( ValueBox vb : newUnit.getUseAndDefBoxes() ){
                if( vb.getValue() instanceof Local ){
                    Local local = (Local) vb.getValue();
                    if( localTranformMap.containsKey(local) ){
                        vb.setValue(localTranformMap.get(local));
                    }
                }
                else if( vb.getValue() instanceof ThisRef ){
                    if( thisLocal != null ){
                        vb.setValue(thisLocal);
                    }
                }

            }

            //Patching UnitBoxes
            for( UnitBox ub : newUnit.getUnitBoxes() ){
                Unit unit = ub.getUnit();
                ub.setUnit( clonedUnits.get(unit) );
            }
            //System.out.println();

            //If it is return statement, then assign it to the returnLocal
            if( newUnit instanceof ReturnStmt ){
                Unit assignStmt = Jimple.v().newAssignStmt(returnLocal, ((ReturnStmt) newUnit).getOp());
                callerUnits.insertBefore(assignStmt, callsite);

                List<UnitBox> boxes = new ArrayList<>( newUnit.getBoxesPointingToThis() ); //To avoid concurrent modification exception
                for(UnitBox ub : boxes){
                    ub.setUnit(assignStmt);
                }

                Unit gotoStmt = Jimple.v().newGotoStmt(exitStmt);
                callerUnits.insertBefore(gotoStmt, callsite);
            }
            else if(newUnit instanceof ReturnVoidStmt ){
                Unit gotoStmt = Jimple.v().newGotoStmt(exitStmt);
                
                //Patch the UnitBoxes for Return!!
                List<UnitBox> boxes = new ArrayList<>( newUnit.getBoxesPointingToThis() ); //To avoid concurrent modification exception
                for(UnitBox ub : boxes){
                    ub.setUnit(gotoStmt);
                }

                callerUnits.insertBefore(gotoStmt, callsite);
            }
            else callerUnits.insertBefore(newUnit, callsite);
        }

        //Add the nop statement at the end to patch the return statements
        callerUnits.insertBefore(exitStmt, callsite);
        
        // callerUnits.forEach(u -> System.out.println(u));


        callerUnits.remove(callsite);
        callerBody.validate();
    }
        
    public void processCFG(SootMethod method) {
        Body body = method.getActiveBody();
        UnitGraph cfg = new BriefUnitGraph(body);
        PatchingChain<Unit> units = body.getUnits();

        Iterator<Unit> unitIt = units.snapshotIterator(); // A snapshot iterator is used to avoid concurrent modification exceptions
        while (unitIt.hasNext()) {
            Unit u = unitIt.next();
            InvokeExpr invokeExpr = null;
            if( u instanceof InvokeStmt ){
                invokeExpr = ((InvokeStmt) u).getInvokeExpr();

                //Is this condition required ???/
                if(! (invokeExpr instanceof VirtualInvokeExpr || invokeExpr instanceof StaticInvokeExpr) ){
                    invokeExpr = null;
                }
            }
            else if( u instanceof JAssignStmt ){
                JAssignStmt assignStmt = (JAssignStmt) u;
                Value rightOp = assignStmt.getRightOp();
                if( rightOp instanceof VirtualInvokeExpr || rightOp instanceof StaticInvokeExpr ){
                    invokeExpr = (InvokeExpr) rightOp;
                }
            }

            if( invokeExpr != null ){
                Iterator<Edge> receviers = cg.edgesOutOf(u);
                Edge edge = checkMonomorphicIterator(receviers);
                if(edge != null){
                    SootMethod targetMethod = edge.tgt();

                    //Inlining condition
                    if( targetMethod.isConcrete() && !targetMethod.isJavaLibraryMethod() && !targetMethod.toString().contains("init") ) {
                        //System.out.println("Inlining " + targetMethod);
                        tranformInline(method, u, invokeExpr, targetMethod);
                    }
                }
            }

        }

    }

    private static void getlistofMethods(SootMethod method, Set<SootMethod> reachableMethods) {
        // Avoid revisiting methods
        if (reachableMethods.contains(method)) {
            return;
        }
        // Add the method to the reachable set
        reachableMethods.add(method);

        // Iterate over the edges originating from this method
        Iterator<Edge> edges = Scene.v().getCallGraph().edgesOutOf(method);
        while (edges.hasNext()) {
            Edge edge = edges.next();
            SootMethod targetMethod = edge.tgt();
            // Recursively explore callee methods
            if (!targetMethod.isJavaLibraryMethod()) {
                getlistofMethods(targetMethod, reachableMethods);
            }
        }
    }


    public void print(SootMethod method){
        System.out.println("=====================================================");
        System.out.println("Method: " + method);
        Body body = method.getActiveBody();
        PatchingChain<Unit> units = body.getUnits();
        for(Unit u : units){
            System.out.println(u);
        }
    }
}