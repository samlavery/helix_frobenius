import sys, time
sys.path.insert(0,'tmp')
from davenport_fast import FastG, exact_search, first_element_reps
def name(inv): return "C"+"+C".join(str(n) for n in inv)
# Reachable frontier, ordered to complete as many as possible within budget.
targets = [(2,2,16),(2,2,18),(2,6,6),(2,2,20),(3,6,6),(2,4,12),(6,6,6)]
CAP=250_000_000
TIME_BUDGET=600  # overall seconds
t_start=time.time()
for inv in targets:
    if time.time()-t_start > TIME_BUDGET: 
        print(f"{name(inv)}: SKIPPED (overall time budget hit)",flush=True); continue
    FG=FastG(inv); nreps=len(first_element_reps(FG))
    t0=time.time()
    ml,wit,nodes,to=exact_search(FG,target=FG.M,node_cap=CAP)
    dt=time.time()-t0; D=ml+1
    if to: v=f"TIMEOUT best d>={ml} (D>={D})"
    elif D>FG.M: v=f"*** COUNTEREXAMPLE D={D}>M={FG.M} witness={wit} ***"
    elif D==FG.M: v="EXACT: D=M confirmed"
    else: v=f"ANOMALY D={D}<M"
    print(f"{name(inv):14} |G|={FG.n:4} d*={FG.dstar:3} M={FG.M:3} reps={nreps:3} nodes={nodes:>11} {dt:6.1f}s D={D:3} {v}",flush=True)
