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

/-- A concrete Mathlib-backed normalized real seed.

This value is intentionally only the current normalized arithmetic seed used by
legacy and receipt surfaces.  The equality proof below is definitional (`rfl`),
and the positivity proof is arithmetic (`norm_num`).  Therefore these facts must
not be read as a non-definitional derivation of `33/20` from the physical
Yang--Mills Hamiltonian spectrum, nor as a proof of positive spectral weight.
Those obligations are tracked separately by the exact-value derivation boundary. -/
noncomputable def exactGapValueReal : ℝ := (33 : ℝ) / 20

/-- Arithmetic positivity of the normalized seed. -/
theorem exactGapValueReal_pos : 0 < exactGapValueReal := by
  norm_num [exactGapValueReal]

/-- Definitional equality of the normalized seed. -/
theorem exactGapValueReal_eq : exactGapValueReal = (33 : ℝ) / 20 := by
  rfl

end MathlibAnalytic
end MGAP4D
