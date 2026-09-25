find -name "*.c" -o -name "*.h" -o -name "*.cpp" -o -name "*.hpp" > ./cscope.files
echo "cscope data base created in the ./cscope.files \n"
cscope -b -q -k
echo "Databsae built without using GUI and create index for faster lookup and donot look /usr/include \n"
cscope -d
