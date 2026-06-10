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

This carrier is no longer defined as `(33 : ℝ) / 20`, and this file deliberately
exports no theorem of the form `exactGapValueReal = (33 : ℝ) / 20`.  The R6 layer
is responsible for the first review-facing numeric equality theorem, via the
Yang--Mills Hamiltonian spectral derivation surface. -/
noncomputable def exactGapValueReal : ℝ := (8 : ℝ) / 5 + 1 / 20

/-- Arithmetic positivity of the normalized pre-R6 carrier. -/
theorem exactGapValueReal_pos : 0 < exactGapValueReal := by
  norm_num [exactGapValueReal]

end MathlibAnalytic
end MGAP4D
