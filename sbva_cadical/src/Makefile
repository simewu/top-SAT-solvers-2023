
default: all

all: bva

bva: bva.cc
	$(CXX) -I ../archives/eigen-3.4.0/ -std=c++11 -O3 -o bva bva.cc

clean:
	rm bva
