#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
while ! grep -q "RUNG 480 DONE-v2" $LOG; do sleep 300; done
build() {
  echo "=== $1 ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
for T in DVPStation482 DVPStation1933o4 DVPStation485 DVPStation486 DVPStation487 DVPStation489 DVPStation491 DVPStation492 DVPStation1975o4 DVPStation495 DVPStation496 DVPStation497 DVPWeights1000col DVPCos995o2Table DVPCos995o2Psum DVPSegment995o2Core DVPSegment995o2 DVPLift995o2 DVPExhaustion995o2 DVPLadder995o2; do build $T; done
echo "RUNG 497.5 DONE-v2" >> $LOG
