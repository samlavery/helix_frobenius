#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
while ! grep -q "RUNG 526.5 DONE-v2" $LOG; do sleep 300; done
while ! grep -q "4000-TABLES DONE-v2" $LOG; do sleep 300; done
build() {
  echo "=== $1 ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
for T in DVPStation2113o4 DVPStation529 DVPStation1061o2 DVPStation532 DVPStation533 DVPStation535 DVPStation536 DVPStation538 DVPStation539 DVPStation4323o8 DVPStation541 DVPStation543 DVPStation545 DVPStation546 DVPStation1095o2 DVPStation549 DVPStation550 DVPStation1103o2 DVPStation553 DVPStation555 DVPStation556 DVPStation2229o4 DVPStation559 DVPStation560 DVPStation561 DVPStation563 DVPStation4515o8 DVPStation566 DVPStation567 DVPStation568 DVPStation1139o2 DVPStation1141o2 DVPPhaseStationEighth DVPPhaseStationEighthEval DVPCos1142o2Table DVPCos1142o2Psum DVPSegment1142o2Core DVPSegment1142o2 DVPLift1142o2 DVPExhaustion1142o2 DVPLadder1142o2; do build $T; done
echo "RUNG 571 DONE-v2" >> $LOG
