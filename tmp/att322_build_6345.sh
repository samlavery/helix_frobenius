#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
while ! grep -q "RUNG 607.5 DONE-v2" $LOG; do sleep 300; done
build() {
  echo "=== $1 ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
for T in DVPStation2435o4 DVPStation610 DVPStation2445o4 DVPStation2451o4 DVPStation614 DVPStation2461o4 DVPStation617 DVPStation1237o2 DVPStation2479o4 DVPStation621 DVPStation622 DVPStation1247o2 DVPStation625 DVPStation1253o2 DVPStation2511o4 DVPStation2517o4 DVPStation2527o4 DVPStation633 DVPStation2537o4 DVPCos1269o2Table DVPCos1269o2Psum DVPSegment1269o2Core DVPSegment1269o2 DVPLift1269o2 DVPExhaustion1269o2 DVPLadder1269o2; do build $T; done
echo "RUNG 634.5 DONE-v2" >> $LOG
