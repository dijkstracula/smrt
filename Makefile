DAFNY_PATH?=~/code/dafny/Binaries
DAFNY_CMD=${DAFNY_PATH}/Dafny verify

SOURCES = $(shell find . -name '*.dfy')

ROOT=Bundle.dfy

.PHONY: all
all: 
	${DAFNY_CMD} ${SOURCES}

.PHONY: report
report: report/report.md report/bibliography.bib
	pushd report; pandoc --csl report/acm.csl report.md --bibliography bibliography.bib -d defaults.yaml && popd
