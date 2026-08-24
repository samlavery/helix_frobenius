#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
while ! grep -q "RUNG 343.5 DONE-v2" $LOG; do sleep 300; done
build() {
  echo "=== $1 ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
for T in DVPStation345 DVPStation347 DVPStation348 DVPStation350 DVPStation351 DVPStation353 DVPStation355 DVPStation713o2 DVPStation715o2 DVPStation359 DVPStation361 DVPStation362 DVPStation364 DVPStation365 DVPStation367 DVPStation737o2 DVPStation739o2 DVPStation371 DVPCos743o2Table DVPCos743o2Psum DVPSegment743o2Core DVPSegment743o2 DVPLift743o2 DVPExhaustion743o2 DVPLadder743o2; do build $T; done
echo "RUNG 371.5 DONE-v2" >> $LOG
