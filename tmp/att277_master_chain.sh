#!/bin/zsh
cd /Users/samuellavery/work/helix_frobenius
LOG=tmp/att271_build_log.txt
build() {
  echo "=== $1 ===" >> $LOG
  lake build RequestProject.$1 2>&1 | grep -E "error|axioms" | grep -E "$1|error" | head -4 >> $LOG
}
# repair 199.5 tail
for T in DVPLift399o2 DVPExhaustion399o2 DVPLadder399o2; do build $T; done
echo "RUNG 199.5 DONE-v2" >> $LOG
# 217.5
for T in DVPStation202 DVPStation203 DVPStation205 DVPStation207 DVPStation209 DVPStation211 DVPStation212 DVPStation214 DVPStation215 DVPStation217 DVPCos435o2Table DVPCos435o2Psum DVPSegment435o2Core DVPSegment435o2 DVPLift435o2 DVPExhaustion435o2 DVPLadder435o2; do build $T; done
echo "RUNG 217.5 DONE-v2" >> $LOG
# 235.5
for T in DVPStation220 DVPStation221 DVPStation223 DVPStation449o2 DVPStation226 DVPStation228 DVPStation230 DVPStation463o2 DVPStation233 DVPStation235 DVPCos471o2Table DVPCos471o2Psum DVPSegment471o2Core DVPSegment471o2 DVPLift471o2 DVPExhaustion471o2 DVPLadder471o2; do build $T; done
echo "RUNG 235.5 DONE-v2" >> $LOG
# 262.5
for T in DVPStation237 DVPStation239 DVPStation240 DVPStation242 DVPStation243 DVPStation246 DVPStation495o2 DVPStation249 DVPStation250 DVPStation252 DVPStation254 DVPStation256 DVPStation257 DVPStation259 DVPStation521o2 DVPStation262 DVPCos525o2Table DVPCos525o2Psum DVPSegment525o2Core DVPSegment525o2 DVPLift525o2 DVPExhaustion525o2 DVPLadder525o2; do build $T; done
echo "RUNG 262.5 DONE-v2" >> $LOG
# 280.5
for T in DVPStation264 DVPStation266 DVPStation267 DVPStation269 DVPStation271 DVPStation272 DVPStation274 DVPStation276 DVPStation277 DVPStation279 DVPStation280 DVPCos561o2Table DVPCos561o2Psum DVPSegment561o2Core DVPSegment561o2 DVPLift561o2 DVPExhaustion561o2 DVPLadder561o2; do build $T; done
echo "ALL RUNGS DONE-v2" >> $LOG
