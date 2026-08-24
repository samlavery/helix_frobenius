#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
build() {
  echo "=== $1 (repair6) ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
build DVPLadder687o2
build DVPLadder743o2
echo "RUNGS 343.5+371.5 REPAIR6 DONE-v2" >> $LOG
