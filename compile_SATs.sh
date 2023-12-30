SATHOME=$(pwd)

sudo apt install gcc -y
sudo apt install build-essential -y

echo
echo Compiling sbva_cadical...
cd $SATHOME/1_sbva_cadical/src
make bva

echo
echo Compiling kissat_mab_prop...
cd $SATHOME/2_kissat_mab_prop
./configure && make test

echo
echo Compiling maple_cadical_ppd_500_500...
cd $SATHOME/3_maple_cadical_ppd_500_500
./configure && make

echo $SATHOME
echo
echo Compiling brute_force...
cd $SATHOME/brute_force
make