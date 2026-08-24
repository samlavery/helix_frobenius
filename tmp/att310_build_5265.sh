#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
while ! grep -q "RUNG 508 DONE-v2" $LOG; do sleep 300; done
build() {
  echo "=== $1 ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
for T in DVPStation509 DVPStation511 DVPStation512 DVPStation513 DVPStation515 DVPStation516 DVPStation518 DVPStation519 DVPStation521 DVPStation522 DVPStation523 DVPStation1049o2 DVPStation526 DVPCos1053o2Table DVPCos1053o2Psum DVPSegment1053o2Core DVPSegment1053o2 DVPLift1053o2 DVPExhaustion1053o2 DVPLadder1053o2; do build $T; done
echo "RUNG 526.5 DONE-v2" >> $LOG
