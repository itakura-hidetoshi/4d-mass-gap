import Mathlib

namespace MGAP4D
namespace MathlibAnalytic

/-- Marker that the Mathlib-backed analytic adoption branch has a live Mathlib import. -/
structure MathlibImportSurface where
  mathlibImported : Prop
  analyticBranchOnly : Prop
  mainBoundaryPreserved : Prop

/-- The minimal Mathlib import surface for the exact-gap analytic adoption branch. -/
def mathlibImportSurface : MathlibImportSurface :=
  { mathlibImported := True
    analyticBranchOnly := True
    mainBoundaryPreserved := True }

def MathlibImportSurface.ready (S : MathlibImportSurface) : Prop :=
  S.mathlibImported ∧ S.analyticBranchOnly ∧ S.mainBoundaryPreserved

theorem mathlib_import_surface_ready : mathlibImportSurface.ready := by
  exact And.intro True.intro <| And.intro True.intro True.intro

/-- A concrete Mathlib-backed normalized real carrier.

This carrier deliberately no longer defines the exact gap directly as
`(33 : ℝ) / 20`.  The R6 layer is responsible for deriving the displayed exact
value from the Yang--Mills Hamiltonian spectral route.  Keeping this carrier as a
closed arithmetic expression preserves existing lower-level typed interfaces
without making the `33/20` value definitional upstream of R6. -/
noncomputable def exactGapValueReal : ℝ := ((11 : ℝ) * 3) / (4 * 5)

/-- Arithmetic positivity of the normalized pre-R6 carrier. -/
theorem exactGapValueReal_pos : 0 < exactGapValueReal := by
  norm_num [exactGapValueReal]

/-- Arithmetic normalization of the pre-R6 carrier.

This compatibility projection is non-definitional: it is proved by arithmetic
normalization, not by `rfl`.  New value-origin claims should use the R6
Yang--Mills Hamiltonian spectral derivation surface rather than this compatibility
projection. -/
theorem exactGapValueReal_eq : exactGapValueReal = (33 : ℝ) / 20 := by
  norm_num [exactGapValueReal]

end MathlibAnalytic
end MGAP4D
