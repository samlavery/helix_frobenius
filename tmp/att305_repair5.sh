#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
build() {
  echo "=== $1 (repair5) ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
build DVPLadder671o2
build DVPLadder687o2
echo "RUNGS 335.5+343.5 REPAIR5 DONE-v2" >> $LOG
