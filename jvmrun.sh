

echo "================= $1 ================="
echo "optim"
cd testcases/$1/optim
../../../openj9-openjdk-jdk8/build/linux-x86_64-normal-server-release/images/j2sdk-image/bin/java -Xint Test 2> /dev/null > jvm.txt
python3 ../../../analyse.py jvm.txt ../methods.txt > count.txt
rm jvm.txt

echo "soot"
cd ../soot
../../../openj9-openjdk-jdk8/build/linux-x86_64-normal-server-release/images/j2sdk-image/bin/java -Xint Test 2> /dev/null > jvm.txt
python3 ../../../analyse.py jvm.txt ../methods.txt > count.txt
rm jvm.txt

echo "unoptim"
cd ../unoptim
../../../openj9-openjdk-jdk8/build/linux-x86_64-normal-server-release/images/j2sdk-image/bin/java -Xint Test 2> /dev/null > jvm.txt
python3 ../../../analyse.py jvm.txt ../methods.txt > count.txt
rm jvm.txt

cd ../../../
