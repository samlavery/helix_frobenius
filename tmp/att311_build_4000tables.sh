#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
build() {
  echo "=== $1 ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
build DVPLog4000Table
build DVPSqrt4000Table
echo "4000-TABLES DONE-v2" >> $LOG
