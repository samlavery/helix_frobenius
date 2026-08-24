#!/bin/zsh
cd /Users/samuellavery/work/helix_frobenius
while ! grep -q "RUNG COMPLETE" tmp/att271_build_log.txt 2>/dev/null; do sleep 120; done
for T in DVPStation202 DVPStation203 DVPStation205 DVPStation207 DVPStation209 DVPStation211 DVPStation212 DVPStation214 DVPStation215 DVPStation217 DVPCos435o2Table DVPCos435o2Psum DVPSegment435o2Core DVPSegment435o2 DVPLift435o2 DVPExhaustion435o2 DVPLadder435o2; do
  echo "=== $T ===" >> tmp/att271_build_log.txt
  lake build RequestProject.$T 2>&1 | grep -E "error|axioms" | grep -E "$T|error" | head -4 >> tmp/att271_build_log.txt
done
echo "RUNG 217.5 COMPLETE" >> tmp/att271_build_log.txt
