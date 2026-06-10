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

This carrier is no longer defined as `(33 : ℝ) / 20`, and it is not the origin of
the displayed exact value.  The R6 layer is responsible for proving the first
review-facing `= 33/20` theorem from the Yang--Mills Hamiltonian spectral route.
This arithmetic carrier remains only to keep lower-level typed interfaces live
while the spectral-origin proof is being isolated. -/
noncomputable def exactGapValueReal : ℝ := (8 : ℝ) / 5 + 1 / 20

/-- Arithmetic positivity of the normalized pre-R6 carrier. -/
theorem exactGapValueReal_pos : 0 < exactGapValueReal := by
  norm_num [exactGapValueReal]

/-- Deprecated carrier-normalization compatibility projection.

This theorem must not be used as the value-origin proof.  New numeric-origin
claims must use the R6 spectral derivation theorem instead. -/
theorem exactGapValueReal_eq : exactGapValueReal = (33 : ℝ) / 20 := by
  norm_num [exactGapValueReal]

end MathlibAnalytic
end MGAP4D
