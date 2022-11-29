DAFNY_PATH?=~/code/dafny/Binaries
DAFNY_CMD=${DAFNY_PATH}/Dafny verify

SOURCES = $(shell find . -name '*.dfy')

ROOT=Bundle.dfy

.PHONY: all
all: 
	${DAFNY_CMD} ${SOURCES}

.PHONY: report
report: report/report.md report/bibliography.bib
	pandoc  --citeproc --csl report/ieee.csl report/report.md --bibliography report/bibliography.bib -d report/defaults.yaml
