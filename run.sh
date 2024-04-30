rm -rf testcase/*
rm -rf sootOutput/*


#### unoptimized
cp testcases/$1/Test.java testcase/
mkdir -p testcases/$1/unoptim
rm -rf testcases/$1/unoptim/*
mkdir -p testcases/$1/soot
rm -rf testcases/$1/soot/*
mkdir -p testcases/$1/optim
rm -rf testcases/$1/optim/*

cd testcase
javac Test.java
cp *.class ../testcases/$1/unoptim/

echo "============== UNOPTIMIZED =============="
/usr/bin/time -v java -Xint Test   > ../testcases/$1/unoptim/out.txt 2> ../testcases/$1/unoptim/time.txt
cd ..

#### soot without any optimization

echo "============== SOOT =============="
java -cp soot.jar soot.Main -cp . -pp -w -main-class Test -process-dir testcase -f c Test
cd sootOutput    
cp *.class ../testcases/$1/soot/
/usr/bin/time -v java -Xint Test > ../testcases/$1/soot/out.txt 2> ../testcases/$1/soot/time.txt
rm -rf *
cd ..


echo "============== OPTIMIZED =============="
java -cp .:soot.jar PA4 > testcases/$1/log.txt
cd sootOutput
cp *.class ../testcases/$1/optim/
/usr/bin/time -v java -Xint Test > ../testcases/$1/optim/out.txt 2> ../testcases/$1/optim/time.txt
rm -rf *
cd ..


diff testcases/$1/unoptim/out.txt testcases/$1/optim/out.txt &> /dev/null

if [ $? -eq 0 ]
then
    echo "Test Passed"
else
    echo "Test Failed"
fi
