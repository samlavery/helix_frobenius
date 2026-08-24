#!/bin/zsh
cd /Users/samuellavery/work/helix_frobenius
for M in 158 160 162 164 166 168 172 174 176 177 179 181 183 186 188 191 194 196 199 339o2 385o2 395o2; do
  lake build RequestProject.DVPStation$M 2>&1 | grep -E "error|station_${M}_sign.*axioms" | head -2 >> tmp/att271_build_log.txt
done
echo "ALL DONE" >> tmp/att271_build_log.txt
