#!/bin/zsh
# Serial DVP build runner. Detached via nohup so it survives the caller.
# One `lake build` at a time; never two Lean processes concurrently.
cd /Users/samuellavery/work/helix_frobenius || exit 1
LOG=/Users/samuellavery/work/helix_frobenius/tmp/serial_build.log
MEM=/Users/samuellavery/work/helix_frobenius/tmp/serial_build.mem

TARGETS=(
  DVPStation4323o8 DVPStation4515o8
  DVPLift995o2  DVPExhaustion995o2  DVPLadder995o2
  DVPLift1016o2 DVPExhaustion1016o2 DVPLadder1016o2
  DVPLift1053o2 DVPExhaustion1053o2 DVPLadder1053o2
  DVPLift1142o2 DVPExhaustion1142o2 DVPLadder1142o2
  DVPLift1179o2 DVPExhaustion1179o2 DVPLadder1179o2
  DVPLift1215o2 DVPExhaustion1215o2 DVPLadder1215o2
  DVPLift1269o2 DVPExhaustion1269o2 DVPLadder1269o2
)

# RSS sampler: records peak lean memory so an OOM death is visible after the fact.
( while true; do
    r=$(ps -Ao rss,comm | grep -E 'bin/lean$' | sort -rn | head -1 | awk '{print $1}')
    [ -n "$r" ] && echo "$(date +%T) $((r/1024))MB" >> "$MEM"
    sleep 15
  done ) &
SAMPLER=$!
trap "kill $SAMPLER 2>/dev/null" EXIT

for t in $TARGETS; do
  # skip anything already built
  if [ -f ".lake/build/lib/lean/RequestProject/$t.olean" ]; then
    echo "=== $(date +%T) SKIP  $t (already built)" >> "$LOG"
    continue
  fi
  # memory gate
  for i in $(seq 1 60); do
    free_mb=$(vm_stat | awk '/page size of/{ps=$8} /Pages free/{f=$3} /Pages inactive/{i=$3} /Pages speculative/{s=$3} END{gsub("\\.","",f);gsub("\\.","",i);gsub("\\.","",s); print int((f+i+s)*ps/1048576)}')
    [ "$free_mb" -ge 14000 ] && break
    sleep 20
  done
  echo "=== $(date +%T) START $t (free ${free_mb}MB)" >> "$LOG"
  LEAN_NUM_THREADS=1 lake build "RequestProject.$t" >> "$LOG" 2>&1
  rc=$?
  echo "=== $(date +%T) END   $t exit=$rc" >> "$LOG"
done
echo "=== ALL DONE $(date +%T)" >> "$LOG"
kill $SAMPLER 2>/dev/null
