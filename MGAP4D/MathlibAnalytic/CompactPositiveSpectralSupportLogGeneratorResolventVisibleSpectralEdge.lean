import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventWeightedMoments
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventTuranHierarchy
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventStrictAbsoluteMonotonicity
import MGAP4D.MathlibAnalytic.PositiveWeightedMomentRatioEndpoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace lp LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

local instance visibleSpectralEdgeSupportComplete
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E) :
    CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe

/-- The successive positive resolvent moments converge to the largest shifted
reciprocal energy that is actually visible in the state.

For `x_mu = (E_mu - lambda)⁻¹` and state weight `w_mu = ‖(U v)_mu‖²`, put

`m_n = ⟪F(lambda)^(n+1) v, v⟫`.

The weighted coordinate formula gives

`m_n = sum_mu x_mu^(n+1) w_mu`.

Thus the endpoint principle applies with positive weights `a_mu = x_mu w_mu`.
The Turan/log-convex hierarchy supplies monotonicity of `m_(n+1)/m_n`; the
same weighted expansion proves that every ratio is at most the supremum of
the visible `x_mu`.  Hence the ratio tends exactly to that state-visible
reciprocal spectral edge. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_ambientResolvent_momentRatio_tendsto_visibleReciprocalSup
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive)
    (c : ℝ) (hc : 0 < c)
    (hLower : ∀ mu : Eigenvalues (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
      Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
      c ≤ realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)
    (hNorm : ∀ z : (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain,
      c * ‖(z : realHilbertZeroEigenspaceSupport T)‖ ≤
        ‖realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive z‖)
    (hKer : ∀ z : (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain,
      realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive z = 0 → z = 0)
    (hSurj : Function.Surjective
      (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).toFun)
    (hQuad : ∀ z : (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain,
      c * ‖(z : realHilbertZeroEigenspaceSupport T)‖ ^ 2 ≤
        inner ℝ (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive z)
          (z : realHilbertZeroEigenspaceSupport T))
    (v : realHilbertZeroEigenspaceSupport T) (hv : v ≠ 0) (lambda : ℝ) (hlambda : |lambda| < c) :
    let A := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
    let U := realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv T hCompact hPositive
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound A c hc hNorm hKer hSurj
    let x := fun mu : Eigenvalues (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
      Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
      (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu - lambda)⁻¹
    let a := fun mu : Eigenvalues (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
      Module.End ℝ (realHilbertZeroEigenspaceSupport T)) => x mu * ‖(U v) mu‖ ^ 2
    let X : Set ℝ := {y | ∃ mu, 0 < a mu ∧ x mu = y}
    Tendsto (fun n : ℕ => inner ℝ (((F lambda) ^ (n + 2)) v) v /
      inner ℝ (((F lambda) ^ (n + 1)) v) v) atTop (𝓝 (sSup X)) := by
  dsimp only
  let A := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  let x := fun mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
    (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu - lambda)⁻¹
  let w := fun mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
    ‖(U v) mu‖ ^ 2
  let a := fun mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
    x mu * w mu
  let m := fun n : ℕ => inner ℝ (((F lambda) ^ (n + 1)) v) v
  let X : Set ℝ := {y | ∃ mu, 0 < a mu ∧ x mu = y}
  have hlambda_lt_c : lambda < c :=
    (le_abs_self lambda).trans_lt hlambda
  have hxpos : ∀ mu, 0 < x mu := by
    intro mu
    apply inv_pos.mpr
    exact sub_pos.mpr (hlambda_lt_c.trans_le (hLower mu))
  have hself : IsSelfAdjoint A := by
    simpa [A] using
      (realHilbertCompactPositiveZeroSupportLogGenerator_isSelfAdjoint
        T hCompact hPositive)
  have hmpos : ∀ n : ℕ, 0 < m n := by
    intro n
    simpa [m, F, A] using
      (realLinearPMapAmbientResolventFamily_pow_inner_pos
        A c hc hNorm hKer hSurj hself hQuad lambda hlambda (n + 1) v hv)
  have hmoment : ∀ k : ℕ,
      inner ℝ (((F lambda) ^ k) v) v =
        ∑' mu,
          x mu ^ k * w mu := by
    intro k
    simpa [A, U, F, x, w] using
      (realHilbertCompactPositiveZeroSupportLogGenerator_ambientResolvent_pow_quadratic_eq_tsum
        T hCompact hPositive c hc hLower hNorm hKer hSurj
        lambda hlambda k v)
  have hsummable : ∀ k : ℕ, Summable (fun mu => x mu ^ k * w mu) := by
    intro k
    have hs := lp.summable_inner
      (U (((F lambda) ^ k) v)) (U v)
    refine hs.congr ?_
    intro mu
    have hcoord :=
      realHilbertCompactPositiveZeroSupportLogGenerator_ambientResolvent_pow_coordinates
        T hCompact hPositive c hc hLower hNorm hKer hSurj
        lambda hlambda k v mu
    rw [show (U (((F lambda) ^ k) v)) mu = x mu ^ k • (U v) mu by
      simpa [A, U, F, x] using hcoord]
    simp [w, real_inner_smul_left]
  have hcoordLower : ∀ mu, 0 < a mu → ∀ n : ℕ, a mu * x mu ^ n ≤ m n := by
    intro mu hmu n
    have hnonneg : ∀ j, 0 ≤ x j ^ (n + 1) * w j := by
      intro j
      exact mul_nonneg (pow_nonneg (hxpos j).le _) (sq_nonneg _)
    have hone := (hsummable (n + 1)).sum_le_tsum {mu} (by
      intro j hj
      exact hnonneg j)
    have hone' : x mu ^ (n + 1) * w mu ≤ ∑' j, x j ^ (n + 1) * w j := by
      simpa using hone
    calc
      a mu * x mu ^ n = x mu ^ (n + 1) * w mu := by
        simp [a, pow_succ]
        ring
      _ ≤ ∑' j, x j ^ (n + 1) * w j := hone'
      _ = m n := by
        simpa [m] using (hmoment (n + 1)).symm
  have hmono : Monotone (fun n : ℕ => m (n + 1) / m n) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [div_le_div_iff₀ (hmpos n) (hmpos (n + 1))]
    have hlog :=
      realLinearPMapAmbientResolventFamily_pow_inner_logConvex
        A c hc hNorm hKer hSurj hself hQuad lambda hlambda (n + 1) v hv
    simpa [m, F, mul_comm] using hlog
  have hUv : U v ≠ 0 := by
    intro hzero
    apply hv
    apply U.injective
    simpa using hzero
  have hmuVisible : ∃ mu, (U v) mu ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hUv
    ext mu
    exact hnone mu
  have hXne : X.Nonempty := by
    rcases hmuVisible with ⟨mu, hmu⟩
    refine ⟨x mu, ?_⟩
    refine ⟨mu, ?_, rfl⟩
    exact mul_pos (hxpos mu) (sq_pos_of_pos (norm_pos_iff.mpr hmu))
  have hclambda : 0 < c - lambda := sub_pos.mpr hlambda_lt_c
  have hXbdd : BddAbove X := by
    refine ⟨(c - lambda)⁻¹, ?_⟩
    rintro y ⟨mu, hmu, rfl⟩
    have hshift : c - lambda ≤
        realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu - lambda :=
      sub_le_sub_right (hLower mu) lambda
    simpa [x] using inv_anti₀ hclambda hshift
  have hXLUB : IsLUB X (sSup X) := isLUB_csSup hXne hXbdd
  have hSpos : 0 < sSup X := by
    rcases hXne with ⟨y, hy⟩
    rcases hy with ⟨mu, hmu, hxy⟩
    have hypos : 0 < y := by
      rw [← hxy]
      exact hxpos mu
    exact hypos.trans_le (hXLUB.1 ⟨mu, hmu, hxy⟩)
  have hupper : ∀ n : ℕ, m (n + 1) / m n ≤ sSup X := by
    intro n
    apply (div_le_iff₀ (hmpos n)).2
    have hterm : ∀ mu,
        x mu ^ (n + 2) * w mu ≤
          sSup X * (x mu ^ (n + 1) * w mu) := by
      intro mu
      by_cases hzero : (U v) mu = 0
      · simp [w, hzero]
      · have ha : 0 < a mu :=
          mul_pos (hxpos mu) (sq_pos_of_pos (norm_pos_iff.mpr hzero))
        have hxS : x mu ≤ sSup X := hXLUB.1 ⟨mu, ha, rfl⟩
        have hnonneg : 0 ≤ x mu ^ (n + 1) * w mu :=
          mul_nonneg (pow_nonneg (hxpos mu).le _) (sq_nonneg _)
        calc
          x mu ^ (n + 2) * w mu =
              x mu * (x mu ^ (n + 1) * w mu) := by
            rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
            ring
          _ ≤ sSup X * (x mu ^ (n + 1) * w mu) :=
            mul_le_mul_of_nonneg_right hxS hnonneg
    have hleft := (hsummable (n + 2)).hasSum
    have hright := ((hsummable (n + 1)).hasSum.const_mul (sSup X))
    have htsum :
        (∑' mu, x mu ^ (n + 2) * w mu) ≤
          sSup X * (∑' mu, x mu ^ (n + 1) * w mu) := by
      exact hasSum_le hterm hleft (by
        simpa only [← tsum_mul_left] using hright)
    rw [hmoment (n + 2), hmoment (n + 1)]
    exact htsum
  have hlimit :=
    positiveWeightedMomentRatio_tendsto_sSup
      m a x hmpos hcoordLower hmono X rfl hXne hXbdd hupper
  simpa [m] using hlimit

end

end MathlibAnalytic
end MGAP4D
