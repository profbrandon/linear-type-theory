@echo off

cd bin
del *.exe
cd ../obj
del *.o
cd ../src

move *.o ../obj/
move *.exe ../bin/
del *.hi

cd ..
echo "cleaning finished"