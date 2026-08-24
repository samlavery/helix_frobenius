#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
while ! grep -q "RUNG 309 DONE-v2" $LOG; do sleep 300; done
build() {
  echo "=== $1 ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
for T in DVPStation1242o4 DVPStation312 DVPStation313 DVPStation315 DVPStation317 DVPStation318 DVPStation320 DVPStation643o2 DVPStation323 DVPStation324 DVPStation326 DVPStation328 DVPStation659o2 DVPStation331 DVPStation333 DVPStation334 DVPStation335 DVPCos671o2Table DVPCos671o2Psum DVPSegment671o2Core DVPSegment671o2 DVPLift671o2 DVPExhaustion671o2 DVPLadder671o2; do build $T; done
echo "RUNG 335.5 DONE-v2" >> $LOG
