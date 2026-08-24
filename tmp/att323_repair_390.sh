#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
build() {
  echo "=== $1 (repair7) ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
for T in DVPSegment780o2Core DVPSegment780o2 DVPLift780o2 DVPExhaustion780o2 DVPLadder780o2; do build $T; done
echo "RUNG 390 REPAIR7 DONE-v2" >> $LOG
