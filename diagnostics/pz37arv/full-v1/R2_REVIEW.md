# ARV R2 structural repair (TEST_REQUIRED)

Exact baseline 48ad154d037b9f7b9b4d40114b60d6f88a248346. R1 diagnostic source 3e53af24679fbe1dd5dcfdf10770cc186bb359ce; sandbox 46113463279 / job 140882123816. R1A 123.310 s, R1B 99.331 s; both exit 1; MCP not started. R1A 5 diagnostics, R1B 6. No failed source promoted.

Cardinality: broad simp reduced the 8-coordinate carrier to a concrete lattice-associated numeral expression and left a goal. Prove card J = 8 directly and rewrite only card_sigma and card_pi_const; no unused simp argument.

Product: pinned mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6 Mathlib/Algebra/BigOperators/Ring/Finset.lean Fintype.prod_sum, Mathlib/Data/Fintype/BigOperators.lean card_sigma/card_pi_const signatures inspected. The concrete call at R1 line 202 exceeded whnf heartbeats; generic weighted product expansion isolates the abstract finite index and factor functions. R2A uses native word indices; R2B uses the already locally reindexed Fin factors and a separate function-space cardinality proof. Same seven audited public declarations, all original statements and actual endpoint halfweights retained. No changed heartbeat budget, weakened hypotheses, new axioms, sorry, or canonical modifications. R2 must pass direct Lean and real Lean MCP before independent CI. This is a repair hypothesis, not certification.
