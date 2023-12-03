#!/bin/sh
ESESC_BIN=${1:-../main/esesc}
export ESESC_ReportFile="t2"
export ESESC_BenchName="/home/cse220/SHA256/sha256"
export ESESC_DL1_core_size="524288"
export ESESC_DL1_core_assoc="8"
export ESESC_DL1_core_bsize="128"
for i in 1
do
    echo "$i"
    if [ -f $ESESC_BIN ]; then
        $ESESC_BIN
    else
        $ESESC_BenchName 
    fi
done
exit 0
