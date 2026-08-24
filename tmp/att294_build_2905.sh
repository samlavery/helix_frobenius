#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
while ! grep -q "ALL RUNGS DONE-v2" $LOG; do sleep 300; done
build() {
  echo "=== $1 ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
for T in DVPStation283 DVPStation284 DVPStation286 DVPStation287 DVPStation289 DVPStation290 DVPWeights581o2 DVPCos581o2Table DVPCos581o2Psum DVPSegment581o2Core DVPSegment581o2 DVPLift581o2 DVPExhaustion581o2 DVPLadder581o2; do build $T; done
echo "RUNG 290.5 DONE-v2" >> $LOG
