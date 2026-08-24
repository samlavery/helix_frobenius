#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
while ! grep -q "RUNG 589.5 DONE-v2" $LOG; do sleep 300; done
build() {
  echo "=== $1 ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
for T in DVPStation591 DVPStation2369o4 DVPStation2373o4 DVPStation595 DVPStation596 DVPStation1195o2 DVPStation599 DVPStation1201o2 DVPStation602 DVPStation603 DVPStation2417o4 DVPStation1211o2 DVPStation2429o4 DVPCos1215o2Table DVPCos1215o2Psum DVPSegment1215o2Core DVPSegment1215o2 DVPLift1215o2 DVPExhaustion1215o2 DVPLadder1215o2; do build $T; done
echo "RUNG 607.5 DONE-v2" >> $LOG
