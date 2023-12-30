#!/bin/bash


file=$1
if [ -z "$file" ]
then
	file="simple.cnf"
fi


echo Running SAT solvers on file \"$file\"...


echo
echo Running sbva_cadical...
read -t 3 -n 1
./bin/cadical $file


echo
echo Running kissat_mab_prop...
read -t 3 -n 1
./2_kissat_mab_prop/sources/build/kissat $file


echo
echo Running maple_cadical_ppd_500_500...
read -t 3 -n 1
./maple_cadical_ppd_500_500/bin/cadical $file


echo
echo Running brute_force...
read -t 3 -n 1
./brute_force/build/solver $file