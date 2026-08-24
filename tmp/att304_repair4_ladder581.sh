#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
echo "=== DVPLadder581o2 (repair4) ===" >> $LOG
lake build RequestProject.DVPLadder581o2 2>&1 | grep -E "error|axioms" | grep -E "DVPLadder581o2|error" | head -4 >> $LOG
echo "RUNG 290.5 REPAIR4 DONE-v2" >> $LOG
