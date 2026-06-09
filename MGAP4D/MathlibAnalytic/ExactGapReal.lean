import MGAP4D.MathlibAnalytic.Basic

namespace MGAP4D
namespace MathlibAnalytic

/-- Mathlib-backed real-valued exact-gap carrier surface.

This is the first analytic replacement surface after the pre-Mathlib boundary:
`33/20` is represented in `ℝ`, is positive, and lies strictly above `1`.
It is a normalized real carrier / witness surface.  It is not the local source of
the non-definitional spectral derivation of the exact value.

The current proof route separates these roles:

* this file checks and exposes the normalized real carrier;
* `YangMillsHamiltonianSpectralDerivation3320` records the spectral route that
  derives the same normalized value from the Hamiltonian/spectral chain;
* the complete continuum-Hamiltonian derivation bundles that spectral route with
  the public/final boundary receipts.

Thus downstream code should not treat `value_eq_3320` here as the derivation
itself; it should treat it as the carrier equality that later derivation receipts
identify with the Hamiltonian spectral value. -/
structure ExactGapRealSurface where
  value : ℝ
  value_eq_3320 : value = (33 : ℝ) / 20
  positive : 0 < value
  above_one : 1 < value
  analyticReplacementBranchOnly : Prop

noncomputable def exactGapRealSurface : ExactGapRealSurface :=
  { value := exactGapValueReal
    value_eq_3320 := exactGapValueReal_eq
    positive := exactGapValueReal_pos
    above_one := by
      norm_num [exactGapValueReal]
    analyticReplacementBranchOnly := True }

def ExactGapRealSurface.ready (S : ExactGapRealSurface) : Prop :=
  S.value = (33 : ℝ) / 20 ∧ 0 < S.value ∧ 1 < S.value ∧ S.analyticReplacementBranchOnly

theorem exact_gap_real_surface_ready : exactGapRealSurface.ready := by
  exact And.intro exactGapRealSurface.value_eq_3320 <|
    And.intro exactGapRealSurface.positive <|
    And.intro exactGapRealSurface.above_one True.intro

/-- Value projection for the normalized carrier surface. -/
theorem exact_gap_real_surface_value :
    exactGapRealSurface.value = (33 : ℝ) / 20 := by
  exact exactGapRealSurface.value_eq_3320

/-- Arithmetic positivity projection for the normalized carrier surface. -/
theorem exact_gap_real_surface_positive :
    0 < exactGapRealSurface.value := by
  exact exactGapRealSurface.positive

/-- Arithmetic above-one projection for the normalized carrier surface. -/
theorem exact_gap_real_surface_above_one :
    1 < exactGapRealSurface.value := by
  exact exactGapRealSurface.above_one

end MathlibAnalytic
end MGAP4D
