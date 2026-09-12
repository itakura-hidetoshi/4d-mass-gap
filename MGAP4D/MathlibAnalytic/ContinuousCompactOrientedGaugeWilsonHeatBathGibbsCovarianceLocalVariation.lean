import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathGibbsCovarianceFluctuation
import Mathlib.Tactic

/-!
# Local variation control for one-link Gibbs fluctuations

For the current compact Wilson one-link heat bath, write `Q_e = I - P_e`.
The canonical covariance carrier already proves that `Q_e` has zero Gibbs mean
and is self-adjoint for finite-volume Gibbs covariance.

This file adds the missing local quantitative input.  A proof-relevant
link-variation bound at the same physical link controls the fluctuation
pointwise,

`|Q_e F(A)| ≤ δ_e(F)`,

and therefore two such fluctuations satisfy the genuinely two-sided local
covariance estimate

`|Cov(Q_e F, Q_e G)| ≤ δ_e(F) * δ_e(G)`.

Unlike a global oscillation or total-link variation estimate, the right-hand
side retains the source-link variation of the left observable.  This is the
local algebraic carrier needed before a random-scan/Poisson--Neumann expansion
can produce a Dobrushin covariance comparison with two-sided localization.

No covariance decay, continuum clustering, positive physical mass, OS
Hamiltonian gap, or uniform factorial-continuum Dobrushin threshold is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A one-link heat-bath fluctuation is pointwise bounded by any valid
variation bound on that same physical link. -/
theorem continuous_compact_oriented_singleLinkHeatBathFluctuationContinuousBCF_abs_le_variation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (F : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
      (fun A => F A))
    (A : C.base.Configuration) :
    |C.singleLinkHeatBathFluctuationContinuousBCF target F A| ≤
      P.variation target := by
  let μ := C.singleLinkConditionalMeasure A target
  letI : IsProbabilityMeasure μ :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  have hFInt :
      Integrable
        (fun g : C.base.Gauge => F (C.base.replaceLink A target g)) μ := by
    exact
      (F.continuous.comp
        (continuous_compact_oriented_replaceLink C A target)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  have hConstInt : Integrable (fun _g : C.base.Gauge => F A) μ :=
    integrable_const (F A)
  have hDiffInt :
      Integrable
        (fun g : C.base.Gauge => F A - F (C.base.replaceLink A target g)) μ :=
    hConstInt.sub' hFInt
  have hAbsDiffInt :
      Integrable
        (fun g : C.base.Gauge => |F A - F (C.base.replaceLink A target g)|) μ := by
    simpa [Real.norm_eq_abs] using hDiffInt.norm
  have hVariationInt :
      Integrable (fun _g : C.base.Gauge => P.variation target) μ :=
    integrable_const (P.variation target)
  have hVariation : ∀ g : C.base.Gauge,
      |F A - F (C.base.replaceLink A target g)| ≤ P.variation target := by
    intro g
    apply P.variation_bound target A (C.base.replaceLink A target g)
    intro source hsource
    simp [CompactOrientedGaugeWilsonSystem.replaceLink, hsource]
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationContinuousBCF_apply,
    continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_apply]
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectationBCF
  change
    |F A - ∫ g : C.base.Gauge,
      F (C.base.replaceLink A target g) ∂μ| ≤ P.variation target
  calc
    |F A - ∫ g : C.base.Gauge,
        F (C.base.replaceLink A target g) ∂μ| =
        |(∫ _g : C.base.Gauge, F A ∂μ) -
          ∫ g : C.base.Gauge, F (C.base.replaceLink A target g) ∂μ| := by
      simp
    _ = |∫ g : C.base.Gauge,
        F A - F (C.base.replaceLink A target g) ∂μ| := by
      rw [integral_sub hConstInt hFInt]
    _ ≤ ∫ g : C.base.Gauge,
        |F A - F (C.base.replaceLink A target g)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _g : C.base.Gauge, P.variation target ∂μ := by
      apply integral_mono hAbsDiffInt hVariationInt
      intro g
      exact hVariation g
    _ = P.variation target := by simp

/-- Local two-sided covariance pairing for one-link heat-bath fluctuations.
The estimate retains the variation of the left observable at the source link;
there is no global norm or total-link variation on either side. -/
theorem continuous_compact_oriented_gibbsCovarianceReal_singleLinkHeatBathFluctuations_abs_le_variation_mul_variation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (F G : BoundedContinuousFunction C.base.Configuration ℝ)
    (PF : ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
      (fun A => F A))
    (PG : ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
      (fun A => G A)) :
    |C.gibbsCovarianceReal
        (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target F A)
        (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target G A)| ≤
      PF.variation target * PG.variation target := by
  let μ := C.gibbsMeasure
  let QF := C.singleLinkHeatBathFluctuationContinuousBCF target F
  let QG := C.singleLinkHeatBathFluctuationContinuousBCF target G
  have hQFZero : C.gibbsMeanReal (fun A => QF A) = 0 := by
    simpa [QF] using
      continuous_compact_oriented_gibbsMeanReal_singleLinkHeatBathFluctuationContinuousBCF_eq_zero
        C target F
  have hQGZero : C.gibbsMeanReal (fun A => QG A) = 0 := by
    simpa [QG] using
      continuous_compact_oriented_gibbsMeanReal_singleLinkHeatBathFluctuationContinuousBCF_eq_zero
        C target G
  have hProductInt :
      Integrable (fun A : C.base.Configuration => QF A * QG A) μ := by
    exact
      (QF.continuous.mul QG.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hAbsProductInt :
      Integrable (fun A : C.base.Configuration => |QF A * QG A|) μ := by
    simpa [Real.norm_eq_abs] using hProductInt.norm
  have hConstInt :
      Integrable
        (fun _A : C.base.Configuration =>
          PF.variation target * PG.variation target) μ :=
    integrable_const (PF.variation target * PG.variation target)
  have hPointwise : ∀ A : C.base.Configuration,
      |QF A * QG A| ≤ PF.variation target * PG.variation target := by
    intro A
    rw [abs_mul]
    exact mul_le_mul
      (by
        simpa [QF] using
          continuous_compact_oriented_singleLinkHeatBathFluctuationContinuousBCF_abs_le_variation
            C target F PF A)
      (by
        simpa [QG] using
          continuous_compact_oriented_singleLinkHeatBathFluctuationContinuousBCF_abs_le_variation
            C target G PG A)
      (abs_nonneg _)
      (PF.variation_nonneg target)
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsCovarianceReal
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsPairingReal
  change
    |(∫ A : C.base.Configuration, QF A * QG A ∂μ) -
      C.gibbsMeanReal (fun A => QF A) * C.gibbsMeanReal (fun A => QG A)| ≤
        PF.variation target * PG.variation target
  rw [hQFZero, hQGZero]
  simp only [zero_mul, sub_zero]
  calc
    |∫ A : C.base.Configuration, QF A * QG A ∂μ| ≤
        ∫ A : C.base.Configuration, |QF A * QG A| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _A : C.base.Configuration,
        PF.variation target * PG.variation target ∂μ := by
      apply integral_mono hAbsProductInt hConstInt
      intro A
      exact hPointwise A
    _ = PF.variation target * PG.variation target := by simp

end

end MathlibAnalytic
end MGAP4D
