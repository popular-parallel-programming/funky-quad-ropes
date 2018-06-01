.PHONY: all clean benchmark

all:
	jbuilder build funky.exe

clean:
	jbuilder clean

benchmark:
	_build/default/funky.exe
