#!/bin/zsh
cd /Users/samuellavery/work/helix_frobenius
while ! grep -q "RUNG 217.5 COMPLETE" tmp/att271_build_log.txt 2>/dev/null; do sleep 120; done
for T in DVPStation220 DVPStation221 DVPStation223 DVPStation449o2 DVPStation226 DVPStation228 DVPStation230 DVPStation463o2 DVPStation233 DVPStation235 DVPCos471o2Table DVPCos471o2Psum DVPSegment471o2Core DVPSegment471o2 DVPLift471o2 DVPExhaustion471o2 DVPLadder471o2; do
  echo "=== $T ===" >> tmp/att271_build_log.txt
  lake build RequestProject.$T 2>&1 | grep -E "error|axioms" | grep -E "$T|error" | head -4 >> tmp/att271_build_log.txt
done
echo "RUNG 235.5 COMPLETE" >> tmp/att271_build_log.txt
