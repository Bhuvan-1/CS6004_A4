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
 * 
 * SEE AT THE END OF THE FILE FOR MORE DETAILS
 */



public class FPAnalysis {
    Set<SootMethod> methods;
    public Map<String, Set<String> > all_escapes;
    public Map<SootMethod, Map<Unit, PTOG>> ptsToInfoOut;
    public Map<SootMethod, Set<Local>> valid_locals = new HashMap<>();
    public Map<SootMethod, Map<Local, Set<String>>> all_fields = new HashMap<>();
    public Map<SootMethod, Map<Local, Map<String, SootFieldRef>>> field_refs = new HashMap<>();

    public FPAnalysis( PointsToAnalysis p) {
        this.methods = p.methods;
        this.all_escapes = p.all_escapes;
        this.ptsToInfoOut = p.ptsToInfoOut;
    }

    public boolean alias(Local l1, Local l2, PTOG ptog){
        Set<String> s1 = ptog.Stack.get(l1.getName());
        Set<String> s2 = ptog.Stack.get(l2.getName());
        for(String s : s1){
            if(s2.contains(s)){
                return true;
            }
        }
        return false;
    }

    public boolean local_escape(Local l, String mthd_name, PTOG ptog){
        Set<String> s = ptog.Stack.get(l.getName());
        for(String str : s){
            if(all_escapes.get(mthd_name).contains(str)){
                return true;
            }
        }
        return false;
    }

    public Set<String> get_invalid_objs(Map<String, Map<String, Set<Local> > > field_acc_clashes){
        Set<String> invalid_objs = new HashSet<>();
        for(String obj : field_acc_clashes.keySet()){

            //BASICALLY WE ARE DISALLOWING locals poinitng to PARAM OBJECTS, DUMMY OBJECTS AND O_this.
            if(obj.startsWith("O")){
                invalid_objs.add(obj);
                continue;
            }

            //FOUND A CASE WHERE EVEN IF TWO LOCALS POINT TO DIFF FIELDS.
            //WE GET PROBLEMS IN RECONSTRUCTING... SO LETS JUST DISALLOW THIS CASE.
            Set<Local> s = new HashSet<>();
            for(String field : field_acc_clashes.get(obj).keySet()){
                s.addAll(field_acc_clashes.get(obj).get(field) );
            }
            Set<Integer> levels = new HashSet<>();
            for(Local l : s){
                int len = l.getName().split("#").length;
                if( levels.contains(len) ){
                    System.out.println("Clash in field access : " + obj + " Locals : " + s);
                    invalid_objs.add(obj);
                    break;
                }
                else levels.add(len);
            }
        }
        return invalid_objs;
    }

    public void doAnalysis() {
        for (SootMethod m : methods) {
            if( m.toString().contains("init") ) { continue; }
            processCFG(m);
            m.getActiveBody().validate();
        }

    }

    protected void processCFG(SootMethod method) {
        Body body = method.getActiveBody();
        PatchingChain<Unit> units = body.getUnits();
        String mthd_name = method.getDeclaringClass().getName() + ":" + method.getName();

        all_fields.put(method, new HashMap<>());
        field_refs.put(method, new HashMap<>());
        
        Map<Unit, PTOG> out = ptsToInfoOut.get(method);

        Set<Local> valid = new HashSet<>();
        for(Local l : body.getLocals() ){
            if(l.getType() instanceof RefType){
                valid.add(l);
                all_fields.get(method).put(l, new HashSet<>());
                field_refs.get(method).put(l, new HashMap<>());
            }
        }
        for(Local l : body.getParameterLocals()){
            valid.remove(l);
        }

        Map<String, Map<String, Set<Local> > > field_acc_clashes = new HashMap<>();

        for(Unit u : units){
            if(u instanceof JAssignStmt){
                Value lhs = ((JAssignStmt)u).getLeftOp();
                Value rhs = ((JAssignStmt)u).getRightOp();
                if(lhs instanceof JInstanceFieldRef){
                    JInstanceFieldRef j = (JInstanceFieldRef)lhs;
                    if(j.getBase() instanceof Local){
                        Local l = (Local)j.getBase();
                        String field = j.getField().getName();
                        all_fields.get(method).get(l).add(field);

                        if(!field_refs.get(method).get(l).containsKey(field)){
                            field_refs.get(method).get(l).put(field, j.getFieldRef());
                        }

                        Set<String> objs = out.get(u).Stack.get(l.getName());
                        for(String obj : objs){
                            if(!field_acc_clashes.containsKey(obj)){
                                field_acc_clashes.put(obj, new HashMap<>());
                            }
                            if(!field_acc_clashes.get(obj).containsKey(field)){
                                field_acc_clashes.get(obj).put(field, new HashSet<>());
                            }
                            field_acc_clashes.get(obj).get(field).add(l);
                        }
                    }
                }

                if(rhs instanceof JInstanceFieldRef){
                    JInstanceFieldRef j = (JInstanceFieldRef)rhs;
                    if(j.getBase() instanceof Local){
                        Local l = (Local)j.getBase();
                        String field = j.getField().getName();
                        all_fields.get(method).get(l).add(field);

                        if(!field_refs.get(method).get(l).containsKey(field)){
                            field_refs.get(method).get(l).put(field, j.getFieldRef());
                        }

                        Set<String> objs = out.get(u).Stack.get(l.getName());
                        for(String obj : objs){
                            if(!field_acc_clashes.containsKey(obj)){
                                field_acc_clashes.put(obj, new HashMap<>());
                            }
                            if(!field_acc_clashes.get(obj).containsKey(field)){
                                field_acc_clashes.get(obj).put(field, new HashSet<>());
                            }
                            field_acc_clashes.get(obj).get(field).add(l);
                        }
                    }
                }
            }
        }
        
        Set<String> invalid_objs = get_invalid_objs(field_acc_clashes);

        for(Unit u : units){
            if(u instanceof JAssignStmt){
                Value lhs = ((JAssignStmt)u).getLeftOp();
                Value rhs = ((JAssignStmt)u).getRightOp();
                if(lhs instanceof Local && lhs.getType() instanceof RefType){
                    Local l = (Local)lhs;
                    
                    for(String obj : out.get(u).Stack.get(l.getName())){
                        if(invalid_objs.contains(obj)){
                            valid.remove(l);
                            break;
                        }
                    }

                    if( local_escape(l, mthd_name, out.get(u)) ){
                        valid.remove(l);
                    }
                }
            }
            else if(u instanceof JIdentityStmt){
                Value lhs = ((JIdentityStmt)u).getLeftOp();

                //DISALLOW FIELD PRIVITAZATION OF EXTERNAL OBJECTS.
                if(lhs instanceof Local && lhs.getType() instanceof RefType){
                    valid.remove(lhs);
                }
            
            }
        }
        
        // //REMOVE THE $$ TEMP VARIABLES
        //NEED NOT REMOVE THEM AS ANAYWAY THEY WONT BE USED IN THE FIELD ACCESES.
        // Set<Local> to_remove = new HashSet<>();
        // for(Local l : valid){
        //     if(l.getName().contains("$")) to_remove.add(l);
        // }
        // for(Local l : to_remove){
        //     valid.remove(l);
        // }


        valid_locals.put(method, valid);
    }


    void print(){
        for(SootMethod m : valid_locals.keySet()){
            System.out.println("=====================================================");
            System.out.println("Method : " + m);
            for(Unit u : m.getActiveBody().getUnits()){
                System.out.println("Unit : " + u);
            }
            System.out.println("\tValid Locals : " + valid_locals.get(m));
            System.out.println("All Fields : ");
            for(Local l : all_fields.get(m).keySet()){
                System.out.println("\t Local : " + l + " Fields : " + all_fields.get(m).get(l));
                System.out.println("\t Field Ref : " + field_refs.get(m).get(l));
            }
        }
    }
}


        /*
         *  Only consider the assignment statements
         * Consider a local x, now any assignment to x will be considered as a new object
         * just check at these assignemnt statements, whether x's objects are escaping or not.. if they does.. then mark x as invalid
         * maybe in one branch x obj escpaes and in other it doesnt... but then its a problem to properly update object before the branch megrge.. so we are skipping this
         * also any y  = x or y = rhs where x is there.. if y and x can alias after the call.... then also we ignore this case, x is invalid.
         * 
         * So we only allow x = new() and no y = x....
         * SImle checl would be to see after every assignemtn stmt, it any 2 locals might alias or not.. if they do then both invalid.
         * 
         * This wont work becuase.... even if a local might not be aliasing x, some field of y might be poinitn to same obejct as x.
         * The idea is to go through all units.. and see if any object is being pointed to by any other local / field of other object.
         * 
         * Such objects are not valid.
         * And hence any local that points to such object is also not valid.
         * Also any local , whose value escapes is also not valid.
         * 
         * But here an issue is that these $ variables created after new Node() will point to the stack variable
         * like r1 = $r0. and this $r0 might never be used again.. so I tried to just ignore clashes with $ variables..
         * 
         * But the problem again is..
         * consider after inlining, x is passed as a parameter to a function
         * then in the inlined code there is a line param = x.
         * this clashes param, x and hence x cant be optimized.
         * 
         * 
         * ===== NEW STRAGTEGY =====
         * Go through all units and , for objects that doesnt escape through non return.
         * Say O1... now among all field references, if two locals access O1.f then check for clash bewtween them
         * if one is local, other is inlined ==> no isse
         * local, local ==> issue
         * inlined, inlined ==> issue if the level of inlining is same...
         * I think this can be done by adding a hash # in local name. number of # will tell the level of inlining.
         * so just check of the number of # in the local name.
         * 
         * If a local might point to multipl.. then a clash in ANY object it points to will make it invalid.
         * 
         * I THINK EVEN THOUGH, WE ARE ALLOWING A CLASH BUT IN DIFFERENT FIELD ACCESES. and
         * we are also allowing a alias via a field of another object, for us to have a problem evne that obj needs to be 
         * stored in some local and then do an acces l.f... so we can detect this clash.
         * 
         * 
         * AND FINALLY WE ARE NOT ALLOWING THE SR OF PARAMS OR THIS REF...
         * This can be done by adding all O_p1, O_p2, Odummy*, O_this to the invalid list.
         * COZ IDEALLY THEY CAN BE ACCESED BY THE CALLER FUNCTIONS... bUT EVEN IF WE DONT HAVE MULTI THREADING
         * We would never know if O_p1 and O_p2 and this are pointing to same object  are not.
         * But these optimizations will be enabled once the function is inlined into its caller.
         * 
         */