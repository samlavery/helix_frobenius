#!/bin/bash
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
while ! grep -q "RUNG 417 DONE-v2" $LOG; do sleep 300; done
build() {
  echo "=== $1 ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
for T in DVPStation419 DVPStation1681o4 DVPStation421 DVPStation423 DVPStation424 DVPStation426 DVPStation428 DVPStation429 DVPStation431 DVPStation1727o4 DVPStation433 DVPStation435 DVPStation437 DVPStation438 DVPStation439 DVPStation441 DVPStation442 DVPStation444 DVPStation445 DVPStation1789o4 DVPStation448 DVPStation899o2 DVPStation451 DVPStation452 DVPCos906o2Table DVPCos906o2Psum DVPSegment906o2Core DVPSegment906o2 DVPLift906o2 DVPExhaustion906o2 DVPLadder906o2; do build $T; done
echo "RUNG 453 DONE-v2" >> $LOG
for T in DVPStation909o2 DVPStation456 DVPStation457 DVPStation459 DVPStation1839o4 DVPStation461 DVPStation463 DVPStation465 DVPStation466 DVPStation467 DVPStation469 DVPStation470 DVPStation472 DVPStation473 DVPStation475 DVPStation476 DVPStation477 DVPStation957o2 DVPStation480 DVPCos960o2Table DVPCos960o2Psum DVPSegment960o2Core DVPSegment960o2 DVPLift960o2 DVPExhaustion960o2 DVPLadder960o2; do build $T; done
echo "RUNG 480 DONE-v2" >> $LOG
