@echo off
cd src
ghc LinearTT.hs -L"../obj" 
cd ..

cd bin

LinearTT.exe

cd ..
