.PHONY: all clean benchmark

all:
	jbuilder build funky.exe

bc:
	jbuilder build funky.bc


clean:
	jbuilder clean

benchmark:
	_build/default/funky.exe pearsons > results/pearsons.out
	_build/default/funky.exe vdc      > results/vdc.out
	_build/default/funky.exe primes   > results/primes.out
