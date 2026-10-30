# PZ37ABR CI diagnostic repair

Source a977c27bf23c03aee488e8fb9504faf17e63fb67, PR #6026, CI #41137629110 failed in Early elaboration of new PZ37O leaves BEFORE the mandatory dependency-aware changed-file Lake check. The log reports originalRot_apply_zero expecting no scalar argument at PZ37O lines 334/353, against restored project oleans. The current workflow had LEAN_FAST_DIRECT_ELAB=false but both optional direct diagnostic steps ignored it.

This repair is an explicit exception to the initial plan's no-workflow-change intention: make both optional direct steps honor the existing flag, preserving them for opt-in diagnostics. The mandatory check_changed_lean.sh/lake build step, its failure propagation, all physical sources, Lean statements, toolchain, dependencies and public roots remain unchanged.

Add a stdlib-only static routing regression test, wired beside the existing dependency-routing tests. Local RED reproduced both missing guards. After the two guard changes, all 3 tests passed. YAML parses; local before-workflow SHA matches a95df3db9678f1a57981eca93bfae02040725fd3, and the repaired blob is 2a1cc9c2e201bee970b8f153fc3295d81dbafe17. These static tests are NOT Lean validation.

The new ABR Lean sources remain kernel-unverified until the actual dependency-aware exact-source CI completes. Do not infer success from optional diagnostics being skipped or from a receipt job completing. No merge before changed-file warning/error 0/0, standard axioms, no sorryAx, and the separate exact-source receipt.
