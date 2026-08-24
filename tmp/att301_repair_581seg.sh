#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
build() {
  echo "=== $1 (repair2) ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
for T in DVPSegment581o2 DVPLift581o2 DVPExhaustion581o2 DVPLadder581o2; do build $T; done
echo "RUNG 290.5 REPAIR2 DONE-v2" >> $LOG
