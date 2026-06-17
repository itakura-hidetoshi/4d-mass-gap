import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathVariance

/-!
Compatibility import for the historical Dirichlet module path.

The conditional expectation, conditional variance, averaged variance,
`singleLinkHeatBathDirichletForm`, and exact-gap Poincare predicates are
canonically defined in `FiniteLatticeWilsonSingleLinkHeatBathVariance`.
Keeping this file as an import shim removes the former duplicate declarations
and makes the variance and sweep import lanes composable.
-/
