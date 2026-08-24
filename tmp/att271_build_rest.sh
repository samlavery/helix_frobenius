#!/bin/zsh
cd /Users/samuellavery/work/helix_frobenius
# wait for the station chain
while ! grep -q "ALL DONE" tmp/att271_build_log.txt 2>/dev/null; do sleep 60; done
for T in DVPLog1000Table DVPSqrt1000Table DVPPhaseStationQuarter DVPPhaseStationQuarterEval DVPStation741o4 DVPCos399o2Table DVPCos399o2Psum DVPSegment399o2Core DVPSegment399o2 DVPLift399o2 DVPExhaustion399o2 DVPLadder399o2; do
  echo "=== $T ===" >> tmp/att271_build_log.txt
  lake build RequestProject.$T 2>&1 | grep -E "error|axioms" | grep -E "$T|error" | head -4 >> tmp/att271_build_log.txt
done
echo "RUNG COMPLETE" >> tmp/att271_build_log.txt
