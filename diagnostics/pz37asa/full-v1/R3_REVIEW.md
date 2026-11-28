# ASA R3 (TEST_REQUIRED)

R2 sandbox 46131806944 / job 140938445045, exact source d8242ad09eb7906e435ad4a562e8012b310739dc. R2A 33.203 s exit 1 with two unreachableTactic diagnostics at line 251 columns 21 and 31. R2B 9.281 s exit 1 with one unreachableTactic diagnostic at line 251 column 53. Both runs report all thirteen declarations using only the standard three axioms. No unsolved goal, type mismatch or sorryAx is observed. Real MCP not called.

R3A retains the complete R2B proof except deletion of the redundant final norm_num, after simp [hs,ht,hq]. R3B retains the complete R2A proof except deletion of the redundant final split and norm_num, after simp [hs,ht]. Independent-endpoint lemma and all public statements remain unchanged. Linter remains enabled; no suppression, no heartbeat/pin changes, no weakening or new axiom. Full R2A and R2B difference reread. Append-only candidates and review, old failures preserved. Direct Lean and real MCP GREEN before independent CI.
