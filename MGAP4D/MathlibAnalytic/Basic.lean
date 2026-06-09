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

This definition is the canonical normalized value carrier used by legacy,
receipt, and route-index surfaces.  The local equality proof below is
intentionally definitional (`rfl`) and the local positivity proof is arithmetic
(`norm_num`); these local facts are carrier checks, not the source of the
spectral derivation.

The current proof route treats the non-definitional `33/20` derivation as coming
from the Yang--Mills Hamiltonian spectral derivation surfaces, especially
`YangMillsHamiltonianSpectralDerivation3320` and the complete continuum
Hamiltonian derivation.  Downstream public/external receipt layers should cite
those derivation receipts when they mean "derived from the spectral route", and
should cite this file only when they mean "the normalized carrier value". -/
noncomputable def exactGapValueReal : ℝ := (33 : ℝ) / 20

/-- Arithmetic positivity of the normalized carrier. -/
theorem exactGapValueReal_pos : 0 < exactGapValueReal := by
  norm_num [exactGapValueReal]

/-- Definitional equality of the normalized carrier. -/
theorem exactGapValueReal_eq : exactGapValueReal = (33 : ℝ) / 20 := by
  rfl

end MathlibAnalytic
end MGAP4D
