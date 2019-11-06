WORKERS := 4

TLA := docker run --rm -it --workdir /mnt -v ${PWD}:/mnt talex5/tla

.PHONY: all check tlaps

all: check pdfs tlaps

# Run the TLC model checker
check:
	${TLA} tlc -workers ${WORKERS} MVDS/mvds.tla -config MVDS/models/SpecOK.cfg

# Run the TLAPS proof checker
tlaps:
	${TLA} tlapm -I /usr/local/lib/tlaps MVDS/mvds.tla
