DAFNY_PATH?=~/code/dafny/Binaries
DAFNY_CMD=${DAFNY_PATH}/Dafny verify

SOURCES = $(shell find . -name '*.dfy')

ROOT=Bundle.dfy

.PHONY: all
all: 
	${DAFNY_CMD} ${SOURCES}
