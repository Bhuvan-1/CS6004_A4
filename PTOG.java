import java.util.*;


// Points to graph class
class PTOG {
    Map<String, Set<String>> Stack;
    Map< String, Map<String, Set<String>> > Heap;

    public PTOG() {
        Stack = new HashMap<>();
        Heap = new HashMap<>();
    }

    public PTOG clone(){
        PTOG ptog = new PTOG();
        ptog.Stack = new HashMap<>();
        for (String var : Stack.keySet()) {
            ptog.Stack.put(var, new HashSet<>(Stack.get(var)));
        }
        ptog.Heap = new HashMap<>();
        for (String obj : Heap.keySet()) {
            ptog.Heap.put(obj, new HashMap<>());
            for (String field : Heap.get(obj).keySet()) {
                ptog.Heap.get(obj).put(field, new HashSet<>(Heap.get(obj).get(field)));
            }
        }
        return ptog;
    }

    public boolean different(PTOG ptog) {
        if (! (Stack.equals(ptog.Stack) && Heap.equals(ptog.Heap)) ) return true;

        for (String var : Stack.keySet()) {
            if (! Stack.get(var).equals(ptog.Stack.get(var))) return true;
        }

        for (String obj : Heap.keySet()) {
            if(! Heap.get(obj).equals(ptog.Heap.get(obj))) return true;
            for (String field : Heap.get(obj).keySet()) {
                if (! Heap.get(obj).get(field).equals(ptog.Heap.get(obj).get(field))) return true;
            }
        }

        return false;
    }
   
    public void union( PTOG ptog ) {

        ptog = ptog.clone();        // To avoid copying references directly from original object

        for (String var : ptog.Stack.keySet()) {
            if (! Stack.containsKey(var)) {
                Stack.put(var, ptog.Stack.get(var));
            } else {
                Stack.get(var).addAll(ptog.Stack.get(var));
            }
        }

        for (String obj : ptog.Heap.keySet()) {
            if (! Heap.containsKey(obj)) {
                Heap.put(obj, ptog.Heap.get(obj));
            } else {
                for (String field : ptog.Heap.get(obj).keySet()) {
                    if (! Heap.get(obj).containsKey(field)) {
                        Heap.get(obj).put(field, ptog.Heap.get(obj).get(field));
                    } else {
                        Heap.get(obj).get(field).addAll(ptog.Heap.get(obj).get(field));
                    }
                }
            }
        }
    }

    public void print() {
        for( String var : Stack.keySet() ) {
            System.out.println(var + " : " + Stack.get(var));
        }

        for( String obj : Heap.keySet() ) {
            System.out.println(obj + " : ");
            for( String field : Heap.get(obj).keySet() ) {
                System.out.println("\t" + field + " : " + Heap.get(obj).get(field));
            }
        }
    }

}