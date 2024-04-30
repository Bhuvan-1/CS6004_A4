import java.util.*;

/*
 * A test case to see the improvement due to inlining and FieldPV.
 */


public class Test{

    public static void main(String[] args) {
        int ITER = 1000;
        for(int i = 0; i <ITER; i++){
            Runner.run();
        }
    }
}


class Runner {

    public static void run(){
        //Use a lot of getx getys in a big loopy computation
        A a = new B(3,4);

        int sum = 0;
        for(int i = 0; i < 1000; i++){
            sum += a.getX() + a.getY();
        }

        System.out.println(sum);
    }
}



class A{
    int x;
    int y;

    public A(int x, int y){
        this.x = x;
        this.y = y;
    }

    public int getX(){
        return x;
    }

    public int getY(){
        return y;
    }
}

class B extends A{
    int x;
    int y;

    public B(int x, int y){
        super(x-1,y-1);
        this.x = x;
        this.y = y;
    }

    public int getX() {
        return x;
    }

    public int getY(){
        return y;
    }


}