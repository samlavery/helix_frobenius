#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
while ! grep -q "RUNG 571 DONE-v2" $LOG; do sleep 300; done
build() {
  echo "=== $1 ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
for T in DVPStation573 DVPStation574 DVPStation1151o2 DVPStation1153o2 DVPStation578 DVPStation1159o2 DVPStation581 DVPStation1165o2 DVPStation584 DVPStation585 DVPStation1173o2 DVPStation1175o2 DVPStation589 DVPCos1179o2Table DVPCos1179o2Psum DVPSegment1179o2Core DVPSegment1179o2 DVPLift1179o2 DVPExhaustion1179o2 DVPLadder1179o2; do build $T; done
echo "RUNG 589.5 DONE-v2 -- WITNESSED FRONTIER FULLY EMITTED" >> $LOG
