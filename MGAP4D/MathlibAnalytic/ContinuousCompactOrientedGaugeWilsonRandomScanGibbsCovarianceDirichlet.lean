import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathGibbsCovarianceDirichlet
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanVariation
import Mathlib.Tactic

/-!
# Random-scan Gibbs covariance Dirichlet identity

Let `P_e` denote the exact compact Wilson one-link heat-bath projection,
`Q_e = I - P_e`, and let

`R = |E|⁻¹ ∑_e P_e`

be the uniform random-scan operator on bounded continuous observables.  The
one-link Dirichlet identity can then be summed exactly, without introducing any
commutativity between distinct links:

`Cov(F, (I-R)G) = |E|⁻¹ ∑_e Cov(Q_e F, Q_e G)`.

Combining this with the canonical local fluctuation estimate gives the
source-localized defect bound

`|Cov(F, (I-R)G)| ≤ |E|⁻¹ ∑_e δ_e(F) δ_e(G)`.

This is the finite-volume algebraic bridge needed before a truncated
Poisson--Neumann expansion.  No absolute spatial covariance decay, continuum
clustering, or physical mass-gap conclusion is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

private theorem continuous_compact_oriented_bcf_integrable_randomScanCovariance
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable (fun A => O A) C.gibbsMeasure := by
  exact
    O.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Gibbs mean is additive on bounded continuous observables. -/
theorem continuous_compact_oriented_gibbsMeanReal_add_bcf
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F G : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsMeanReal (fun A => (F + G) A) =
      C.gibbsMeanReal (fun A => F A) + C.gibbsMeanReal (fun A => G A) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeanReal
  simpa using
    (integral_add
      (continuous_compact_oriented_bcf_integrable_randomScanCovariance C F)
      (continuous_compact_oriented_bcf_integrable_randomScanCovariance C G))

/-- Gibbs pairing is additive in its right bounded-continuous slot. -/
theorem continuous_compact_oriented_gibbsPairingReal_add_right_bcf
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F G H : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsPairingReal (fun A => F A) (fun A => (G + H) A) =
      C.gibbsPairingReal (fun A => F A) (fun A => G A) +
        C.gibbsPairingReal (fun A => F A) (fun A => H A) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsPairingReal
  simpa [mul_add] using
    (integral_add
      (continuous_compact_oriented_bcf_integrable_randomScanCovariance C (F * G))
      (continuous_compact_oriented_bcf_integrable_randomScanCovariance C (F * H)))

/-- Gibbs covariance is additive in its right bounded-continuous slot. -/
theorem continuous_compact_oriented_gibbsCovarianceReal_add_right_bcf
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F G H : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsCovarianceReal (fun A => F A) (fun A => (G + H) A) =
      C.gibbsCovarianceReal (fun A => F A) (fun A => G A) +
        C.gibbsCovarianceReal (fun A => F A) (fun A => H A) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsCovarianceReal
  rw [continuous_compact_oriented_gibbsPairingReal_add_right_bcf C F G H,
    continuous_compact_oriented_gibbsMeanReal_add_bcf C G H]
  ring

/-- Gibbs mean is real-linear under scalar multiplication on bounded continuous
observables. -/
theorem continuous_compact_oriented_gibbsMeanReal_smul_bcf
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (c : ℝ)
    (G : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsMeanReal (fun A => (c • G) A) =
      c * C.gibbsMeanReal (fun A => G A) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeanReal
  change (∫ A, c * G A ∂C.gibbsMeasure) = c * ∫ A, G A ∂C.gibbsMeasure
  exact integral_const_mul c (fun A => G A)

/-- Gibbs pairing is real-linear under scalar multiplication in its right
bounded-continuous slot. -/
theorem continuous_compact_oriented_gibbsPairingReal_smul_right_bcf
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (c : ℝ)
    (F G : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsPairingReal (fun A => F A) (fun A => (c • G) A) =
      c * C.gibbsPairingReal (fun A => F A) (fun A => G A) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsPairingReal
  change (∫ A, F A * (c * G A) ∂C.gibbsMeasure) =
    c * ∫ A, F A * G A ∂C.gibbsMeasure
  calc
    (∫ A, F A * (c * G A) ∂C.gibbsMeasure) =
        ∫ A, c * (F A * G A) ∂C.gibbsMeasure := by
      apply integral_congr_ae
      filter_upwards [] with A
      ring
    _ = c * ∫ A, F A * G A ∂C.gibbsMeasure := by
      rw [integral_const_mul]

/-- Gibbs covariance is real-linear under scalar multiplication in its right
bounded-continuous slot. -/
theorem continuous_compact_oriented_gibbsCovarianceReal_smul_right_bcf
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (c : ℝ)
    (F G : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsCovarianceReal (fun A => F A) (fun A => (c • G) A) =
      c * C.gibbsCovarianceReal (fun A => F A) (fun A => G A) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsCovarianceReal
  rw [continuous_compact_oriented_gibbsPairingReal_smul_right_bcf C c F G,
    continuous_compact_oriented_gibbsMeanReal_smul_bcf C c G]
  ring

/-- Gibbs covariance commutes with a finite sum in its right
bounded-continuous slot. -/
theorem continuous_compact_oriented_gibbsCovarianceReal_finset_sum_right_bcf
    {α : Type*}
    [DecidableEq α]
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F : BoundedContinuousFunction C.base.Configuration ℝ)
    (G : α → BoundedContinuousFunction C.base.Configuration ℝ)
    (s : Finset α) :
    C.gibbsCovarianceReal (fun A => F A) (fun A => (s.sum G) A) =
      s.sum (fun i => C.gibbsCovarianceReal (fun A => F A) (fun A => G i A)) := by
  induction s using Finset.induction_on with
  | empty =>
      simp [ContinuousCompactOrientedGaugeWilsonSystem.gibbsCovarianceReal,
        ContinuousCompactOrientedGaugeWilsonSystem.gibbsPairingReal,
        ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeanReal]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        continuous_compact_oriented_gibbsCovarianceReal_add_right_bcf]
      exact congrArg
        (fun x => C.gibbsCovarianceReal (fun A => F A) (fun A => G i A) + x)
        ih

/-- Bounded-continuous Feller representative of the uniform random-scan
one-link conditional expectation. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.randomScanConditionalExpectationContinuousBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    BoundedContinuousFunction C.base.Configuration ℝ :=
  (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ •
    ∑ target : C.base.geometry.Edge,
      C.singleLinkConditionalExpectationContinuousBCF target O

/-- The Feller random-scan representative agrees pointwise with the existing
exact random-scan expectation. -/
@[simp] theorem continuous_compact_oriented_randomScanConditionalExpectationContinuousBCF_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    C.randomScanConditionalExpectationContinuousBCF O A =
      C.randomScanConditionalExpectationBCF O A := by
  classical
  simp [ContinuousCompactOrientedGaugeWilsonSystem.randomScanConditionalExpectationContinuousBCF,
    ContinuousCompactOrientedGaugeWilsonSystem.randomScanConditionalExpectationBCF,
    continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_apply,
    smul_eq_mul]

/-- Uniform random-scan fluctuation `I - R` on bounded continuous observables. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.randomScanHeatBathFluctuationContinuousBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    BoundedContinuousFunction C.base.Configuration ℝ :=
  O - C.randomScanConditionalExpectationContinuousBCF O

/-- One-link right fluctuation covariance equals the two-sided fluctuation
pairing. -/
theorem continuous_compact_oriented_gibbsCovarianceReal_singleLinkHeatBathFluctuation_right_eq_fluctuation_pairing
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (F G : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsCovarianceReal (fun A => F A)
        (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target G A) =
      C.gibbsCovarianceReal
        (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target F A)
        (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target G A) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathFluctuationContinuousBCF
  rw [continuous_compact_oriented_gibbsCovarianceReal_sub_right_bcf]
  exact
    continuous_compact_oriented_gibbsCovarianceReal_sub_singleLinkConditionalExpectation_eq_fluctuation_pairing
      C target F G

/-- Exact random-scan Dirichlet covariance identity.  Distinct one-link
projections are never commuted. -/
theorem continuous_compact_oriented_gibbsCovarianceReal_randomScanHeatBathFluctuation_eq_average_singleLinkFluctuation_pairings
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (F G : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsCovarianceReal (fun A => F A)
        (fun A => C.randomScanHeatBathFluctuationContinuousBCF G A) =
      (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
        ∑ target : C.base.geometry.Edge,
          C.gibbsCovarianceReal
            (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target F A)
            (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target G A) := by
  classical
  let n : ℝ := Fintype.card C.base.geometry.Edge
  have hnPos : 0 < n := Nat.cast_pos.mpr hEdge
  have hnNe : n ≠ 0 := ne_of_gt hnPos
  let projections : C.base.geometry.Edge →
      BoundedContinuousFunction C.base.Configuration ℝ :=
    fun target => C.singleLinkConditionalExpectationContinuousBCF target G
  unfold ContinuousCompactOrientedGaugeWilsonSystem.randomScanHeatBathFluctuationContinuousBCF
    ContinuousCompactOrientedGaugeWilsonSystem.randomScanConditionalExpectationContinuousBCF
  rw [continuous_compact_oriented_gibbsCovarianceReal_sub_right_bcf,
    continuous_compact_oriented_gibbsCovarianceReal_smul_right_bcf,
    continuous_compact_oriented_gibbsCovarianceReal_finset_sum_right_bcf]
  change
    C.gibbsCovarianceReal (fun A => F A) (fun A => G A) -
        n⁻¹ *
          (∑ target : C.base.geometry.Edge,
            C.gibbsCovarianceReal (fun A => F A)
              (fun A => projections target A)) =
      n⁻¹ *
        ∑ target : C.base.geometry.Edge,
          C.gibbsCovarianceReal
            (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target F A)
            (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target G A)
  have hConst :
      (∑ _target : C.base.geometry.Edge,
          C.gibbsCovarianceReal (fun A => F A) (fun A => G A)) =
        n * C.gibbsCovarianceReal (fun A => F A) (fun A => G A) := by
    simp [n, nsmul_eq_mul]
  calc
    C.gibbsCovarianceReal (fun A => F A) (fun A => G A) -
        n⁻¹ *
          (∑ target : C.base.geometry.Edge,
            C.gibbsCovarianceReal (fun A => F A)
              (fun A => projections target A)) =
      n⁻¹ *
        (n * C.gibbsCovarianceReal (fun A => F A) (fun A => G A) -
          ∑ target : C.base.geometry.Edge,
            C.gibbsCovarianceReal (fun A => F A)
              (fun A => projections target A)) := by
        field_simp [hnNe]
    _ = n⁻¹ *
        ∑ target : C.base.geometry.Edge,
          (C.gibbsCovarianceReal (fun A => F A) (fun A => G A) -
            C.gibbsCovarianceReal (fun A => F A)
              (fun A => projections target A)) := by
        rw [Finset.sum_sub_distrib, hConst]
    _ = n⁻¹ *
        ∑ target : C.base.geometry.Edge,
          C.gibbsCovarianceReal
            (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target F A)
            (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target G A) := by
        congr 1
        apply Finset.sum_congr rfl
        intro target _
        exact
          continuous_compact_oriented_gibbsCovarianceReal_sub_singleLinkConditionalExpectation_eq_fluctuation_pairing
            C target F G

/-- Two-sided localized random-scan covariance comparison for one random-scan
defect.  The source observable appears only through its physical-link variation
profile. -/
theorem continuous_compact_oriented_gibbsCovarianceReal_randomScanHeatBathFluctuation_abs_le_average_variation_products
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (F G : BoundedContinuousFunction C.base.Configuration ℝ)
    (PF : ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
      (fun A => F A))
    (PG : ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
      (fun A => G A)) :
    |C.gibbsCovarianceReal (fun A => F A)
        (fun A => C.randomScanHeatBathFluctuationContinuousBCF G A)| ≤
      (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
        ∑ target : C.base.geometry.Edge,
          PF.variation target * PG.variation target := by
  classical
  let n : ℝ := Fintype.card C.base.geometry.Edge
  have hnPos : 0 < n := Nat.cast_pos.mpr hEdge
  have hnInvNonneg : 0 ≤ n⁻¹ := inv_nonneg.mpr hnPos.le
  rw [continuous_compact_oriented_gibbsCovarianceReal_randomScanHeatBathFluctuation_eq_average_singleLinkFluctuation_pairings
    C hEdge F G]
  change
    |n⁻¹ *
      ∑ target : C.base.geometry.Edge,
        C.gibbsCovarianceReal
          (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target F A)
          (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target G A)| ≤
      n⁻¹ *
        ∑ target : C.base.geometry.Edge,
          PF.variation target * PG.variation target
  rw [abs_mul, abs_of_nonneg hnInvNonneg]
  apply mul_le_mul_of_nonneg_left _ hnInvNonneg
  calc
    |∑ target : C.base.geometry.Edge,
        C.gibbsCovarianceReal
          (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target F A)
          (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target G A)| ≤
      ∑ target : C.base.geometry.Edge,
        |C.gibbsCovarianceReal
          (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target F A)
          (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target G A)| := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ target : C.base.geometry.Edge,
        PF.variation target * PG.variation target := by
      apply Finset.sum_le_sum
      intro target _
      exact
        continuous_compact_oriented_gibbsCovarianceReal_singleLinkHeatBathFluctuations_abs_le_variation_mul_variation
          C target F G PF PG

end

end MathlibAnalytic
end MGAP4D
