import RequestProject.RoundTrip
open Lean in
run_cmd do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    if n.toString.endsWith "hilbert_polya_on_critical_line" then
      logInfo n.toString
