#!/bin/zsh
cd /Users/samuellavery/work/helix_frobenius
while ! grep -q "RUNG 262.5 COMPLETE" tmp/att271_build_log.txt 2>/dev/null; do sleep 120; done
for T in DVPStation264 DVPStation266 DVPStation267 DVPStation269 DVPStation271 DVPStation272 DVPStation274 DVPStation276 DVPStation277 DVPStation279 DVPStation280 DVPCos561o2Table DVPCos561o2Psum DVPSegment561o2Core DVPSegment561o2 DVPLift561o2 DVPExhaustion561o2 DVPLadder561o2; do
  echo "=== $T ===" >> tmp/att271_build_log.txt
  lake build RequestProject.$T 2>&1 | grep -E "error|axioms" | grep -E "$T|error" | head -4 >> tmp/att271_build_log.txt
done
echo "RUNG 280.5 COMPLETE" >> tmp/att271_build_log.txt
