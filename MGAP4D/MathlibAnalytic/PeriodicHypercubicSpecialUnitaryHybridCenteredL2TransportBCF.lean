import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridCenteredStepBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Pre-step native heat-bath fluctuation along the canonical independent-pair
hybrid path. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreCenteredBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : ℝ :=
  C.singleLinkHeatBathFluctuation target O
    (C.independentPairHybridConfiguration z.1 z.2
      (C.canonicalEdgeOrder target).val)

/-- Post-step native heat-bath fluctuation along the canonical independent-pair
hybrid path. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostCenteredBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : ℝ :=
  C.singleLinkHeatBathFluctuation target O
    (C.independentPairHybridConfiguration z.1 z.2
      ((C.canonicalEdgeOrder target).val + 1))

/-- The pre-step centered hybrid observable is strongly measurable on the
independent Gibbs-pair carrier. -/
theorem continuous_compact_oriented_independentPairHybridPreCenteredBCF_stronglyMeasurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    StronglyMeasurable (C.independentPairHybridPreCenteredBCF target O) := by
  have hFluctuation :=
    continuous_compact_oriented_singleLinkHeatBathFluctuation_stronglyMeasurable
      C target O O.continuous.stronglyMeasurable
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreCenteredBCF]
    using hFluctuation.comp_measurable
      (continuous_compact_oriented_independentPairHybridConfiguration
        C (C.canonicalEdgeOrder target).val).measurable

/-- The post-step centered hybrid observable is strongly measurable on the
independent Gibbs-pair carrier. -/
theorem continuous_compact_oriented_independentPairHybridPostCenteredBCF_stronglyMeasurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    StronglyMeasurable (C.independentPairHybridPostCenteredBCF target O) := by
  have hFluctuation :=
    continuous_compact_oriented_singleLinkHeatBathFluctuation_stronglyMeasurable
      C target O O.continuous.stronglyMeasurable
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostCenteredBCF]
    using hFluctuation.comp_measurable
      (continuous_compact_oriented_independentPairHybridConfiguration
        C ((C.canonicalEdgeOrder target).val + 1)).measurable

/-- Squared pre-step centered hybrid fluctuations are integrable under the
independent Gibbs-pair law. -/
theorem continuous_compact_oriented_independentPairHybridPreCenteredBCF_sq_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable
      (fun z => (C.independentPairHybridPreCenteredBCF target O z) ^ 2)
      (C.gibbsMeasure.prod C.gibbsMeasure) := by
  let M : ℝ := (2 * ‖O‖) ^ 2
  apply continuous_compact_oriented_integrable_of_uniform_bound
    (C.gibbsMeasure.prod C.gibbsMeasure)
    (fun z => (C.independentPairHybridPreCenteredBCF target O z) ^ 2)
    (by
      have hStrong :=
        continuous_compact_oriented_independentPairHybridPreCenteredBCF_stronglyMeasurable
          C target O
      simpa [pow_two] using hStrong.mul hStrong)
    M
  intro z
  have hAbs :=
    continuous_compact_oriented_singleLinkHeatBathFluctuation_abs_le
      C target O O.continuous.stronglyMeasurable ‖O‖ (norm_nonneg _)
      (fun A => by simpa [Real.norm_eq_abs] using O.norm_coe_le_norm A)
      (C.independentPairHybridConfiguration z.1 z.2
        (C.canonicalEdgeOrder target).val)
  rw [abs_of_nonneg (sq_nonneg _)]
  dsimp
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreCenteredBCF,
      M]
  nlinarith [norm_nonneg O]

/-- Squared post-step centered hybrid fluctuations are integrable under the
independent Gibbs-pair law. -/
theorem continuous_compact_oriented_independentPairHybridPostCenteredBCF_sq_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable
      (fun z => (C.independentPairHybridPostCenteredBCF target O z) ^ 2)
      (C.gibbsMeasure.prod C.gibbsMeasure) := by
  let M : ℝ := (2 * ‖O‖) ^ 2
  apply continuous_compact_oriented_integrable_of_uniform_bound
    (C.gibbsMeasure.prod C.gibbsMeasure)
    (fun z => (C.independentPairHybridPostCenteredBCF target O z) ^ 2)
    (by
      have hStrong :=
        continuous_compact_oriented_independentPairHybridPostCenteredBCF_stronglyMeasurable
          C target O
      simpa [pow_two] using hStrong.mul hStrong)
    M
  intro z
  have hAbs :=
    continuous_compact_oriented_singleLinkHeatBathFluctuation_abs_le
      C target O O.continuous.stronglyMeasurable ‖O‖ (norm_nonneg _)
      (fun A => by simpa [Real.norm_eq_abs] using O.norm_coe_le_norm A)
      (C.independentPairHybridConfiguration z.1 z.2
        ((C.canonicalEdgeOrder target).val + 1))
  rw [abs_of_nonneg (sq_nonneg _)]
  dsimp
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostCenteredBCF,
      M]
  nlinarith [norm_nonneg O]

/-- Mean-square pre-step centered endpoint energy under two independent Gibbs
configurations. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreCenteredEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ∫ z, (C.independentPairHybridPreCenteredBCF target O z) ^ 2
    ∂(C.gibbsMeasure.prod C.gibbsMeasure)

/-- Mean-square post-step centered endpoint energy under two independent Gibbs
configurations. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostCenteredEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ∫ z, (C.independentPairHybridPostCenteredBCF target O z) ^ 2
    ∂(C.gibbsMeasure.prod C.gibbsMeasure)

/-- Pre-step centered endpoint energy is nonnegative. -/
theorem continuous_compact_oriented_independentPairHybridPreCenteredEnergyBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ C.independentPairHybridPreCenteredEnergyBCF target O := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreCenteredEnergyBCF
  exact integral_nonneg fun _ => sq_nonneg _

/-- Post-step centered endpoint energy is nonnegative. -/
theorem continuous_compact_oriented_independentPairHybridPostCenteredEnergyBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ C.independentPairHybridPostCenteredEnergyBCF target O := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostCenteredEnergyBCF
  exact integral_nonneg fun _ => sq_nonneg _

/-- The integrated hybrid increment energy is controlled by the two explicit
centered endpoint energies. This step makes no claim that either hybrid endpoint
law is the Gibbs law. -/
theorem continuous_compact_oriented_independentPairHybridIncrementEnergyBCF_le_two_centered
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridIncrementEnergyBCF target O ≤
      2 * C.independentPairHybridPostCenteredEnergyBCF target O +
      2 * C.independentPairHybridPreCenteredEnergyBCF target O := by
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  have hIncrement : Integrable
      (fun z => (C.independentPairHybridIncrementBCF target O z) ^ 2) μ := by
    simpa [μ] using
      continuous_compact_oriented_independentPairHybridIncrementBCF_sq_integrable
        C target O
  have hPost : Integrable
      (fun z => (C.independentPairHybridPostCenteredBCF target O z) ^ 2) μ := by
    simpa [μ] using
      continuous_compact_oriented_independentPairHybridPostCenteredBCF_sq_integrable
        C target O
  have hPre : Integrable
      (fun z => (C.independentPairHybridPreCenteredBCF target O z) ^ 2) μ := by
    simpa [μ] using
      continuous_compact_oriented_independentPairHybridPreCenteredBCF_sq_integrable
        C target O
  have hRight : Integrable
      (fun z =>
        2 * (C.independentPairHybridPostCenteredBCF target O z) ^ 2 +
        2 * (C.independentPairHybridPreCenteredBCF target O z) ^ 2) μ :=
    (hPost.const_mul 2).add (hPre.const_mul 2)
  have hIntegrated := integral_mono hIncrement hRight fun z =>
    continuous_compact_oriented_independentPairHybridIncrementBCF_sq_le_two_centered_sq
      C target O z.1 z.2
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridIncrementEnergyBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostCenteredEnergyBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreCenteredEnergyBCF
  change
    (∫ z, (C.independentPairHybridIncrementBCF target O z) ^ 2 ∂μ) ≤
      2 * (∫ z, (C.independentPairHybridPostCenteredBCF target O z) ^ 2 ∂μ) +
      2 * (∫ z, (C.independentPairHybridPreCenteredBCF target O z) ^ 2 ∂μ)
  calc
    (∫ z, (C.independentPairHybridIncrementBCF target O z) ^ 2 ∂μ) ≤
        ∫ z,
          2 * (C.independentPairHybridPostCenteredBCF target O z) ^ 2 +
          2 * (C.independentPairHybridPreCenteredBCF target O z) ^ 2 ∂μ :=
      hIntegrated
    _ = 2 * (∫ z, (C.independentPairHybridPostCenteredBCF target O z) ^ 2 ∂μ) +
        2 * (∫ z, (C.independentPairHybridPreCenteredBCF target O z) ^ 2 ∂μ) := by
      rw [integral_add (hPost.const_mul 2) (hPre.const_mul 2),
        integral_const_mul, integral_const_mul]

/-- Edge-cardinality-scaled pre-step centered endpoint profile. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreCenteredProfileBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  Real.sqrt
    (2 * (Fintype.card C.base.geometry.Edge : ℝ) *
      C.independentPairHybridPreCenteredEnergyBCF target O)

/-- Edge-cardinality-scaled post-step centered endpoint profile. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostCenteredProfileBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  Real.sqrt
    (2 * (Fintype.card C.base.geometry.Edge : ℝ) *
      C.independentPairHybridPostCenteredEnergyBCF target O)

/-- The pre-step centered endpoint profile has the expected exact square. -/
theorem continuous_compact_oriented_independentPairHybridPreCenteredProfileBCF_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (C.independentPairHybridPreCenteredProfileBCF target O) ^ 2 =
      2 * (Fintype.card C.base.geometry.Edge : ℝ) *
        C.independentPairHybridPreCenteredEnergyBCF target O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreCenteredProfileBCF
  exact Real.sq_sqrt <|
    mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (continuous_compact_oriented_independentPairHybridPreCenteredEnergyBCF_nonneg
        C target O)

/-- The post-step centered endpoint profile has the expected exact square. -/
theorem continuous_compact_oriented_independentPairHybridPostCenteredProfileBCF_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (C.independentPairHybridPostCenteredProfileBCF target O) ^ 2 =
      2 * (Fintype.card C.base.geometry.Edge : ℝ) *
        C.independentPairHybridPostCenteredEnergyBCF target O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostCenteredProfileBCF
  exact Real.sq_sqrt <|
    mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (continuous_compact_oriented_independentPairHybridPostCenteredEnergyBCF_nonneg
        C target O)

/-- The canonical hybrid profile is bounded by the two explicit centered
endpoint profiles. All remaining measure transport is now isolated in those two
endpoint terms. -/
theorem continuous_compact_oriented_independentPairHybridProfileBCF_le_centeredProfiles
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridProfileBCF target O ≤
      C.independentPairHybridPostCenteredProfileBCF target O +
      C.independentPairHybridPreCenteredProfileBCF target O := by
  let u := C.independentPairHybridProfileBCF target O
  let p := C.independentPairHybridPostCenteredProfileBCF target O
  let q := C.independentPairHybridPreCenteredProfileBCF target O
  have hEnergy :=
    continuous_compact_oriented_independentPairHybridIncrementEnergyBCF_le_two_centered
      C target O
  have hCard : 0 ≤ (Fintype.card C.base.geometry.Edge : ℝ) := Nat.cast_nonneg _
  have hScaled := mul_le_mul_of_nonneg_left hEnergy hCard
  have huSq :=
    continuous_compact_oriented_independentPairHybridProfileBCF_sq C target O
  have hpSq :=
    continuous_compact_oriented_independentPairHybridPostCenteredProfileBCF_sq C target O
  have hqSq :=
    continuous_compact_oriented_independentPairHybridPreCenteredProfileBCF_sq C target O
  have hu0 : 0 ≤ u := by
    dsimp [u, ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridProfileBCF]
    exact Real.sqrt_nonneg _
  have hp0 : 0 ≤ p := by
    dsimp [p, ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostCenteredProfileBCF]
    exact Real.sqrt_nonneg _
  have hq0 : 0 ≤ q := by
    dsimp [q, ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreCenteredProfileBCF]
    exact Real.sqrt_nonneg _
  have hpq0 : 0 ≤ p * q := mul_nonneg hp0 hq0
  have hSq : u ^ 2 ≤ (p + q) ^ 2 := by
    dsimp [u, p, q] at huSq hpSq hqSq ⊢
    nlinarith
  dsimp [u, p, q] at hu0 hp0 hq0 hSq ⊢
  nlinarith

end

end MathlibAnalytic
end MGAP4D
