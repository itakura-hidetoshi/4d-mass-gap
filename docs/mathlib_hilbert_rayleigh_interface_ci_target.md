# Mathlib Hilbert Rayleigh interface CI target

Branch: main

Target artifacts:
- MGAP4D/MathlibAnalytic/HilbertRayleighInterface.lean
- MGAP4D/MathlibAnalytic.lean

Target surface:
- HilbertRayleighInterface
- singletonHilbertRayleighInterface
- HilbertRayleighInterfaceReviewSurface
- hilbert_rayleigh_interface_review_surface_ready

Expected CI:
- lake update
- lake exe cache get
- lake build

Boundary: interface-level only. Full Hilbert-space Rayleigh quotient theorem remains open. Final theorem release remains closed. Public theorem boundary remains held.
