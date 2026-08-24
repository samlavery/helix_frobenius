#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
while ! grep -q "RUNG 290.5 DONE-v2" $LOG; do sleep 300; done
build() {
  echo "=== $1 ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
for T in DVPStation293 DVPStation294 DVPStation1181o4 DVPStation297 DVPStation299 DVPStation301 DVPStation302 DVPStation304 DVPStation1221o4 DVPStation307 DVPStation308 DVPCos618o2Table DVPCos618o2Psum DVPSegment618o2Core DVPSegment618o2 DVPLift618o2 DVPExhaustion618o2 DVPLadder618o2; do build $T; done
echo "RUNG 309 DONE-v2" >> $LOG
