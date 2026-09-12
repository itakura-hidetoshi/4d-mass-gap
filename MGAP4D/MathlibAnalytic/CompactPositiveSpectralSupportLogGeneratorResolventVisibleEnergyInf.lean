import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventVisibleSpectralEdge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace lp LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

local instance visibleEnergyInfSupportComplete
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) : CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe

/-- On the positive shifted spectrum, taking reciprocals reverses the visible
energy infimum into the visible reciprocal supremum. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_visibleReciprocalSup_eq_inv_sub_visibleEnergyInf
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive)
    (c : ℝ) (hc : 0 < c)
    (hLower : ∀ mu : Eigenvalues (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
      Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
      c ≤ realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)
    (v : realHilbertZeroEigenspaceSupport T) (hv : v ≠ 0)
    (lambda : ℝ) (hlambda : |lambda| < c) :
    let U := realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv T hCompact hPositive
    let energy := fun mu : Eigenvalues (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
      Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
      realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu
    let x := fun mu => (energy mu - lambda)⁻¹
    let a := fun mu => x mu * ‖(U v) mu‖ ^ 2
    let X : Set ℝ := {y | ∃ mu, 0 < a mu ∧ x mu = y}
    let Y : Set ℝ := {e | ∃ mu, (U v) mu ≠ 0 ∧ energy mu = e}
    sSup X = (sInf Y - lambda)⁻¹ := by
  dsimp only
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let energy := fun mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
    realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu
  let x := fun mu => (energy mu - lambda)⁻¹
  let a := fun mu => x mu * ‖(U v) mu‖ ^ 2
  let X : Set ℝ := {y | ∃ mu, 0 < a mu ∧ x mu = y}
  let Y : Set ℝ := {e | ∃ mu, (U v) mu ≠ 0 ∧ energy mu = e}
  have hlambda_lt_c : lambda < c :=
    (le_abs_self lambda).trans_lt hlambda
  have hxpos : ∀ mu, 0 < x mu := by
    intro mu
    apply inv_pos.mpr
    exact sub_pos.mpr (hlambda_lt_c.trans_le (hLower mu))
  have haPosIff : ∀ mu, 0 < a mu ↔ (U v) mu ≠ 0 := by
    intro mu
    constructor
    · intro ha hzero
      simpa [a, hzero] using ha
    · intro hmu
      exact mul_pos (hxpos mu) (sq_pos_of_pos (norm_pos_iff.mpr hmu))
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
  have hYne : Y.Nonempty := by
    rcases hmuVisible with ⟨mu, hmu⟩
    refine ⟨energy mu, ?_⟩
    exact ⟨mu, hmu, rfl⟩
  have hcLower : c ∈ lowerBounds Y := by
    rintro e ⟨mu, hmu, rfl⟩
    exact hLower mu
  have hYbdd : BddBelow Y := ⟨c, hcLower⟩
  have hYGLB : IsGLB Y (sInf Y) := isGLB_csInf hYne hYbdd
  have hcInf : c ≤ sInf Y := hYGLB.2 hcLower
  have hInfShift : 0 < sInf Y - lambda :=
    sub_pos.mpr (hlambda_lt_c.trans_le hcInf)
  have hXne : X.Nonempty := by
    rcases hYne with ⟨e, mu, hmu, henergy⟩
    refine ⟨x mu, ?_⟩
    exact ⟨mu, (haPosIff mu).2 hmu, rfl⟩
  have hCandidate : IsLUB X ((sInf Y - lambda)⁻¹) := by
    constructor
    · rintro y ⟨mu, ha, rfl⟩
      have hvisible : (U v) mu ≠ 0 := (haPosIff mu).1 ha
      have henergyY : energy mu ∈ Y := ⟨mu, hvisible, rfl⟩
      have hInfLe : sInf Y ≤ energy mu := hYGLB.1 henergyY
      exact inv_anti₀ hInfShift (sub_le_sub_right hInfLe lambda)
    · intro z hz
      rcases hXne with ⟨y, hyX⟩
      have hyUpper : y ≤ z := hz hyX
      rcases hyX with ⟨mu0, ha0, hxy0⟩
      have hypos : 0 < y := by
        rw [← hxy0]
        exact hxpos mu0
      have hzpos : 0 < z := hypos.trans_le hyUpper
      have hlowerZ : lambda + 1 / z ∈ lowerBounds Y := by
        rintro e ⟨mu, hmu, rfl⟩
        have ha : 0 < a mu := (haPosIff mu).2 hmu
        have hxle : x mu ≤ z := hz ⟨mu, ha, rfl⟩
        have hden : 0 < energy mu - lambda :=
          sub_pos.mpr (hlambda_lt_c.trans_le (hLower mu))
        have hzinv : 1 / z ≤ energy mu - lambda := by
          apply (one_div_le hden hzpos).1
          simpa [x, one_div] using hxle
        linarith
      have hzinvInf : 1 / z ≤ sInf Y - lambda := by
        have := hYGLB.2 hlowerZ
        linarith
      simpa [one_div] using (one_div_le hInfShift hzpos).2 hzinvInf
  have hXbdd : BddAbove X := ⟨(sInf Y - lambda)⁻¹, hCandidate.1⟩
  exact (isLUB_csSup hXne hXbdd).unique hCandidate

/-- The successive resolvent-moment ratio converges to the shifted reciprocal
of the lowest logarithmic energy that is visible in the state. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_ambientResolvent_momentRatio_tendsto_visibleEnergyInf
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
    Tendsto (fun n : ℕ => inner ℝ (((F lambda) ^ (n + 2)) v) v /
      inner ℝ (((F lambda) ^ (n + 1)) v) v) atTop (𝓝 ((sInf Y - lambda)⁻¹)) := by
  dsimp only
  have hratio :=
    realHilbertCompactPositiveZeroSupportLogGenerator_ambientResolvent_momentRatio_tendsto_visibleReciprocalSup
      T hCompact hPositive c hc hLower hNorm hKer hSurj hQuad v hv lambda hlambda
  have hedge :=
    realHilbertCompactPositiveZeroSupportLogGenerator_visibleReciprocalSup_eq_inv_sub_visibleEnergyInf
      T hCompact hPositive c hc hLower v hv lambda hlambda
  dsimp only at hratio hedge
  rw [hedge] at hratio
  exact hratio

end

end MathlibAnalytic
end MGAP4D
