import java.util.*;

/*
 * Example that best demonstrates the use of Field Privatization.
 * The fields of two objects are being accesses continuously in a loop.
 * 
 * The required fields are copied after creation and then used in loop.
 * Also before return the field is copied back to object
 * 
 */

class Node {
    Node f;
    Node g;
    int x;

    Node() {
        this.x = 0;
    }

    Node(int x) {
        this.x = x;
    }
}


public class Test{

    public static void main(String[] args) {
        int ITER = 100;
        for(int i = 0; i <ITER; i++){
            Runner.run();
        }
    }
}


class Runner {
    public static void run(){
        for(int i = 0; i < 100; i++){
            Node x = new Node();
            x = make_special(i);
            System.out.println(x.x);
        }
    }

    static Node make_special(int n){
        Node x = new Node();
        Node y = new Node(n);

        x.x = y.x;
        for(int i = 0;i < n; i++){
            x.x += (poly(i) * y.x);
            x.x %= 1000000007;
        }

        return x;
    }

    static int poly(int x){
        return x*x + 3*x + 7;
    }
}

