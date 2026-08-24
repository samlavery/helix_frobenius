#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
while ! grep -q "RUNG 371.5 DONE-v2" $LOG; do sleep 300; done
build() {
  echo "=== $1 ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
for T in DVPStation747o2 DVPStation375 DVPStation376 DVPStation378 DVPStation379 DVPStation381 DVPStation382 DVPStation384 DVPStation771o2 DVPStation387 DVPStation388 DVPStation389 DVPCos780o2Table DVPCos780o2Psum DVPSegment780o2Core DVPSegment780o2 DVPLift780o2 DVPExhaustion780o2 DVPLadder780o2; do build $T; done
echo "RUNG 390 DONE-v2" >> $LOG
for T in DVPStation392 DVPStation393 DVPStation394 DVPStation396 DVPStation397 DVPStation399 DVPStation401 DVPStation402 DVPStation404 DVPStation405 DVPStation406 DVPCos813o2Table DVPCos813o2Psum DVPSegment813o2Core DVPSegment813o2 DVPLift813o2 DVPExhaustion813o2 DVPLadder813o2; do build $T; done
echo "RUNG 406.5 DONE-v2" >> $LOG
for T in DVPStation408 DVPStation410 DVPStation411 DVPStation413 DVPStation414 DVPStation1661o4 DVPStation416 DVPCos834o2Table DVPCos834o2Psum DVPSegment834o2Core DVPSegment834o2 DVPLift834o2 DVPExhaustion834o2 DVPLadder834o2; do build $T; done
echo "RUNG 417 DONE-v2" >> $LOG
