class Node {
    int x;
    Node f;
    Node g;
    static int y = 410;

    Node() {
        x = 0;
        f = null;
        g = null;
    }

    void zoo(){
        System.out.println("zoo");
    }
}


public class Test {
    public static void main(String[] args) {
        Node a = new Node();
        Node c;
        c = new Node();
        
        c.x = Node.y;

        c.f = a;
        c.x = 5;
        a.f = c.f;
        a.g = c.g;

        c.zoo();
        c.x = 10;

        c.zoo();
    }
}


// public class Test {
//     public static void main(String[] args) {
//         Helper h = new Helper();

//         int ret = 0;
//         for(int i = 0; i < 100; i++){
//             ret += h.compute(i, 10);
//         }

//         System.out.println(ret);
//         test(test2());
//     }

//     public static void test(int x) {
//         if(x == 0){
//             System.out.println("x is 0");
//         } else {
//             System.out.println("x is not 0");
//         }
//     }

//     public static int test2(){
//         Node a = new Node();
//         Node b = new Node();
//         Node c = new Node();


//         if(b.x == 0){
//             c = new Node();

//             c.f = a;
//             c.x = 5;
//             b.f = c.f;
//             b.g = c.g;

//             c.zoo();
//         }   
//         else{
//             c = new Node();

//             b.f = c.f;
//             b.g = c.g;
//             c.x = 6;
//             c.g = a;

//             c.zoo();
//         }

//         return c.x;
//     }
// }

// class Helper {
//     public int compute(int n, int k){
//         int ret = 0;
//         for(int i = 0; i < n; i++){
//             for(int j = 0; j < k; j++){
//                 ret += i + j;
//             }
//         }
//         return ret;
//     }
// }