import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricTimeTranslation
import MGAP4D.MathlibAnalytic.FiniteWilsonOSFiniteOrderPermutationShiftRigidity
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusActualGeometricTimeTranslationNoGo

/-!
# Actual finite even-torus geometric Wilson time translation

This aggregate surface constructs the concrete one-step periodic Euclidean-time
translation on the finite even four-torus and proves the exact finite-order
rigidity of the former positive-configuration permutation interface.

The package deliberately distinguishes:

* the actual periodic geometric translation of vertices, edges, plaquettes, and
  edge configurations;
* the positive OS contraction semigroup;
* the noninvertible layer-transfer kernel required for a nontrivial geometric
  Euclidean-time operator.

A periodic configuration equivalence satisfying symmetry, positivity, and OS
contraction completes to the identity.  Therefore a nontrivial Wilson action
witness cannot be discharged by treating actual time translation as a
positive-configuration permutation.  The next construction boundary is the
one-slab/layer transfer kernel, not another permutation certificate.
-/
