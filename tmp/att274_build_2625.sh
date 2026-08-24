#!/bin/zsh
cd /Users/samuellavery/work/helix_frobenius
while ! grep -q "RUNG 235.5 COMPLETE" tmp/att271_build_log.txt 2>/dev/null; do sleep 120; done
for T in DVPStation237 DVPStation239 DVPStation240 DVPStation242 DVPStation243 DVPStation246 DVPStation495o2 DVPStation249 DVPStation250 DVPStation252 DVPStation254 DVPStation256 DVPStation257 DVPStation259 DVPStation521o2 DVPStation262 DVPCos525o2Table DVPCos525o2Psum DVPSegment525o2Core DVPSegment525o2 DVPLift525o2 DVPExhaustion525o2 DVPLadder525o2; do
  echo "=== $T ===" >> tmp/att271_build_log.txt
  lake build RequestProject.$T 2>&1 | grep -E "error|axioms" | grep -E "$T|error" | head -4 >> tmp/att271_build_log.txt
done
echo "RUNG 262.5 COMPLETE" >> tmp/att271_build_log.txt
