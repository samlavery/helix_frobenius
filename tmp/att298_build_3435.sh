#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
while ! grep -q "RUNG 335.5 DONE-v2" $LOG; do sleep 300; done
build() {
  echo "=== $1 ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
for T in DVPStation338 DVPStation339 DVPStation340 DVPStation342 DVPStation343 DVPCos687o2Table DVPCos687o2Psum DVPSegment687o2Core DVPSegment687o2 DVPLift687o2 DVPExhaustion687o2 DVPLadder687o2; do build $T; done
echo "RUNG 343.5 DONE-v2" >> $LOG
