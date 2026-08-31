import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventVisibleEnergyInf
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace lp LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

local instance visibleEffectiveEnergySupportComplete
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) : CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe

/-- A nonzero support state has at least one visible logarithmic spectral energy. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_visibleEnergySet_nonempty
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive)
    (v : realHilbertZeroEigenspaceSupport T) (hv : v ≠ 0) :
    let U := realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv T hCompact hPositive
    let energy := fun mu : Eigenvalues (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
      Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
      realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu
    let Y : Set ℝ := {e | ∃ mu, (U v) mu ≠ 0 ∧ energy mu = e}
    Y.Nonempty := by
  dsimp only
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let energy := fun mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
    realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu
  have hUv : U v ≠ 0 := by
    intro hzero
    apply hv
    apply U.injective
    simpa using hzero
  have hmuVisible : ∃ mu, (U v) mu ≠ 0 := by
    by_contra hnone
    have hzero : ∀ mu, (U v) mu = 0 := by
      intro mu
      by_contra hmu
      exact hnone ⟨mu, hmu⟩
    apply hUv
    apply Subtype.ext
    funext mu
    simpa using hzero mu
  rcases hmuVisible with ⟨mu, hmu⟩
  exact ⟨energy mu, mu, hmu, rfl⟩

/-- The infimum of the energies visible in a nonzero state retains every
uniform logarithmic spectral lower bound. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_uniformLower_le_visibleEnergyInf
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive)
    (c : ℝ)
    (hLower : ∀ mu : Eigenvalues (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
      Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
      c ≤ realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)
    (v : realHilbertZeroEigenspaceSupport T) (hv : v ≠ 0) :
    let U := realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv T hCompact hPositive
    let energy := fun mu : Eigenvalues (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
      Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
      realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu
    let Y : Set ℝ := {e | ∃ mu, (U v) mu ≠ 0 ∧ energy mu = e}
    c ≤ sInf Y := by
  dsimp only
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let energy := fun mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
    realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu
  let Y : Set ℝ := {e | ∃ mu, (U v) mu ≠ 0 ∧ energy mu = e}
  have hYne : Y.Nonempty := by
    simpa [U, energy, Y] using
      (realHilbertCompactPositiveZeroSupportLogGenerator_visibleEnergySet_nonempty
        T hCompact hPositive v hv)
  have hcLower : c ∈ lowerBounds Y := by
    rintro e ⟨mu, hmu, rfl⟩
    exact hLower mu
  exact (isGLB_csInf hYne ⟨c, hcLower⟩).2 hcLower

/-- The reciprocal resolvent-moment ratio, shifted back by `lambda`, is an
effective-energy estimator converging exactly to the lowest logarithmic energy
visible in the state. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_ambientResolvent_effectiveEnergy_tendsto_visibleEnergyInf
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive)
    (c : ℝ) (hc : 0 < c)
    (hLower : ∀ mu : Eigenvalues (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
      Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
      c ≤ realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)
    (hNorm : ∀ z : (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain,
      c * ‖(z : realHilbertZeroEigenspaceSupport T)‖ ≤ ‖realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive z‖)
    (hKer : ∀ z : (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain,
      realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive z = 0 → z = 0)
    (hSurj : Function.Surjective (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).toFun)
    (hQuad : ∀ z : (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain,
      c * ‖(z : realHilbertZeroEigenspaceSupport T)‖ ^ 2 ≤ inner ℝ (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive z) (z : realHilbertZeroEigenspaceSupport T))
    (v : realHilbertZeroEigenspaceSupport T) (hv : v ≠ 0) (lambda : ℝ) (hlambda : |lambda| < c) :
    let A := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
    let U := realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv T hCompact hPositive
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound A c hc hNorm hKer hSurj
    let energy := fun mu : Eigenvalues (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
      Module.End ℝ (realHilbertZeroEigenspaceSupport T)) => realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu
    let Y : Set ℝ := {e | ∃ mu, (U v) mu ≠ 0 ∧ energy mu = e}
    Tendsto (fun n : ℕ => lambda +
      inner ℝ (((F lambda) ^ (n + 1)) v) v /
        inner ℝ (((F lambda) ^ (n + 2)) v) v) atTop (𝓝 (sInf Y)) := by
  dsimp only
  have hratio :=
    realHilbertCompactPositiveZeroSupportLogGenerator_ambientResolvent_momentRatio_tendsto_visibleEnergyInf
      T hCompact hPositive c hc hLower hNorm hKer hSurj hQuad v hv lambda hlambda
  have hcInf :=
    realHilbertCompactPositiveZeroSupportLogGenerator_uniformLower_le_visibleEnergyInf
      T hCompact hPositive c hLower v hv
  dsimp only at hratio hcInf
  have hlambda_lt_c : lambda < c :=
    (le_abs_self lambda).trans_lt hlambda
  have hshift : 0 < sInf {e | ∃ mu,
      (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
        T hCompact hPositive v) mu ≠ 0 ∧
      realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu = e} - lambda :=
    sub_pos.mpr (hlambda_lt_c.trans_le hcInf)
  have hinv := hratio.inv₀ (inv_ne_zero hshift.ne')
  simpa [inv_div] using tendsto_const_nhds.add hinv

end

end MathlibAnalytic
end MGAP4D
