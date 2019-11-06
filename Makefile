WORKERS := 4

TLA := docker run --rm -it --workdir /mnt -v ${PWD}:/mnt talex5/tla

.PHONY: all check tlaps

all: check tlaps

# Run the TLC model checker
check:
	${TLA} cd MVDS && tlc -workers ${WORKERS} MVDS.tla -config models/SpecOK.cfg

# Run the TLAPS proof checker
tlaps:
	${TLA} cd MVDS && tlapm -I /usr/local/lib/tlaps MVDS.tla
