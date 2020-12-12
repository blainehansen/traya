clean:
	#!/usr/bin/env bash
	pushd core
	make clean
	rm -f *.glob
	rm -f *.vo
	rm -f *.vok
	rm -f *.vos
	rm -f .*.aux
	rm -f .*.d
	rm -f Makefile*
	rm -f .lia.cache
	popd

build:
	#!/usr/bin/env bash
	pushd core
	make
	popd

fullbuild:
	#!/usr/bin/env bash
	pushd core
	coq_makefile -f _CoqProject *.v -o Makefile
	make clean
	make
	popd
