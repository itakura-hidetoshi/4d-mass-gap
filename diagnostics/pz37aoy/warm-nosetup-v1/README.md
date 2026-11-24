# AOY R4 and compact cache experiment

AOY R3 completed direct elaboration with all three axiom prints standard, but warning-as-error rejected one unused simp argument h3 at line 54. R4 removes only this argument. Old candidate files remain in #6930 and #6932. This is a new candidate, not an authenticated proof.

The inventory from run 45330137137 measured 3,215 project .json files (16,588,098,252 logical bytes). The exact pinned Lake v4.30.0-rc2 Config/Module.lean defines setupFile = irPath "setup.json"; Build/Module.lean passes it to compileLeanModule on builds, while checkArtifactsExsist requires olean, ilean, c and applicable additional module artifacts, not setupFile. This justifies an experiment, not deletion from a trusted cache.

Quarantine only regular .lake/build/ir/**/*.setup.json within the ephemeral runner. Keep full remote caches, all other artifacts, traces and hashes intact. Use exact cache hits, lake build --no-build, identical strict direct Lean and real MCP on R4, original source tree check, and only then measure a separate compressed archive. No shared cache publication, no automatic pruning or merge. Record actual reduction, failure or missing data explicitly. A successful archive creation is not a cold-restore certification; separate revalidation required before adopting a compact cache key.
