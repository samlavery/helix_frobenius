#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
build() {
  echo "=== $1 (repair) ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
for T in DVPLift525o2 DVPExhaustion525o2 DVPLadder525o2; do build $T; done
echo "RUNG 262.5 REPAIR DONE-v2" >> $LOG
