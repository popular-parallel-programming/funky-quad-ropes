.PHONY: all clean benchmark

all:
	jbuilder build funky.exe

bc:
	jbuilder build funky.bc


clean:
	jbuilder clean

benchmark:
	_build/default/funky.exe
