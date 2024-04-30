import java.util.*;

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
        int N = 1000;
        int[] arr = new int[N];
        for(int i = 0; i < N; i++){
            arr[i] = i;
        }

        A a = new A(5, 10);

        for(int i = 0; i < N; i++){
            arr[i] += a.x  * a.y;
        }

        a.sort(arr, N);
        System.out.println(a.hash(arr, N));

        B b = new B(a.x + 1, a.y + 5);
        b.sort(arr, N);
        System.out.println(b.hash(arr, N));
    }
}


class A{
    public int x;
    public int y;

    A(){
        this.x = 0;
        this.y = 0;
    }

    A(int x, int y){
        this.x = x;
        this.y = y;
    }


    public void sort(int[] arr, int n){
        for(int i = 0; i < n; i++){
            if(i % 2 == 0) arr[i] += x;
        }

        for(int i = 0; i < n; i++){
            for(int j = 0; j < n; j++){
                if(arr[i] < arr[j]){
                    int temp = arr[i];
                    arr[i] = arr[j];
                    arr[j] = temp;
                }
            }
        }

    }

    public int hash(int[] arr, int n){
        int hash = 0;
        int modulo = 100007;
        int fac = 1;
        for(int i = 0; i < n; i++){
            hash += arr[i] * fac;
            hash %= modulo;
            fac *= 31;
            fac %= modulo;
        }
        return hash;
    }
        
}

class B extends A{

    B(){
        super();
    }

    B(int x, int y){
        super(x, y);
    }




    public void sort(int[] arr, int n){

        for(int i = 0; i < n; i++){
            if(i%2 == 1) arr[i] += y;
        }

        for(int i = 0; i < n; i++){
            for(int j = 0; j < n; j++){
                if(arr[i] < arr[j]){
                    int temp = arr[i];
                    arr[i] = arr[j];
                    arr[j] = temp;
                }
            }
        }
    }

    public int hash(int[] arr, int n){
        int hash = 0;
        int modulo = 100007;
        int fac = 1;
        for(int i = 0; i < n; i++){
            hash += arr[i] * fac;
            hash %= modulo;
            fac *= 37;
            fac %= modulo;
        }
        return hash;
    }
}