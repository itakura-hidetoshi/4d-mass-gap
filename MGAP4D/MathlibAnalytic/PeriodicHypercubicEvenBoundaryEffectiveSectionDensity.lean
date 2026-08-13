import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundarySectionWeightContinuity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalL2Density
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveDensityFourEdgeWilsonTransformNonzero
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

private theorem boundaryEffectiveSectionDensityTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance boundaryEffectiveSectionDensityNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryEffectiveSectionDensityTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryEffectiveSectionDensityCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryEffectiveSectionDensitySecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryEffectiveSectionDensityMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryEffectiveSectionDensityBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryEffectiveSectionDensitySU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance boundaryEffectiveSectionDensityBoundaryHaarFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  unfold periodicHypercubicEvenBoundaryHaarMeasure
  unfold FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure
  infer_instance

local instance boundaryEffectiveSectionDensityMarginalFinite
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsFiniteMeasure
      (periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 boundaryEffectiveSectionDensityTwoRankPositive beta hbeta) := by
  rw [← periodicHypercubicEvenSpecialUnitary_map_boundaryRestriction_gibbsMeasure
    H 2 boundaryEffectiveSectionDensityTwoRankPositive beta hbeta]
  infer_instance

noncomputable def periodicHypercubicEvenBoundaryEffectiveSectionRealWeight
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) : ℝ :=
  periodicHypercubicEvenBoundaryVacuumMoment
      H 2 boundaryEffectiveSectionDensityTwoRankPositive beta hbeta b *
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionBoundaryPrefactor
      H beta hbeta b

noncomputable def periodicHypercubicEvenBoundaryEffectiveSectionDensity
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 → ℝ≥0∞ :=
  fun b => ENNReal.ofReal
    (periodicHypercubicEvenBoundaryEffectiveSectionRealWeight H beta hbeta b)

theorem periodicHypercubicEvenBoundaryEffectiveSectionRealWeight_measurable
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measurable
      (periodicHypercubicEvenBoundaryEffectiveSectionRealWeight H beta hbeta) := by
  unfold periodicHypercubicEvenBoundaryEffectiveSectionRealWeight
  exact
    (periodicHypercubicEvenBoundaryVacuumMoment_measurable
      H 2 boundaryEffectiveSectionDensityTwoRankPositive beta hbeta).mul
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionBoundaryPrefactor_continuous
      H beta hbeta).measurable

theorem periodicHypercubicEvenBoundaryEffectiveSectionRealWeight_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    0 < periodicHypercubicEvenBoundaryEffectiveSectionRealWeight H beta hbeta b := by
  unfold periodicHypercubicEvenBoundaryEffectiveSectionRealWeight
  exact mul_pos
    (periodicHypercubicEvenBoundaryVacuumMoment_pos
      H 2 boundaryEffectiveSectionDensityTwoRankPositive beta hbeta b)
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionBoundaryPrefactor_pos
      H beta hbeta b)

theorem periodicHypercubicEvenBoundaryEffectiveSectionDensity_measurable
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measurable
      (periodicHypercubicEvenBoundaryEffectiveSectionDensity H beta hbeta) := by
  unfold periodicHypercubicEvenBoundaryEffectiveSectionDensity
  exact ENNReal.measurable_ofReal.comp
    (periodicHypercubicEvenBoundaryEffectiveSectionRealWeight_measurable H beta hbeta)

theorem periodicHypercubicEvenBoundaryEffectiveSectionDensity_ne_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    periodicHypercubicEvenBoundaryEffectiveSectionDensity H beta hbeta b ≠ 0 := by
  unfold periodicHypercubicEvenBoundaryEffectiveSectionDensity
  rw [ENNReal.ofReal_ne_zero_iff]
  exact periodicHypercubicEvenBoundaryEffectiveSectionRealWeight_pos H beta hbeta b

theorem periodicHypercubicEvenBoundaryEffectiveSectionDensity_ae_ne_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∀ᵐ b ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2),
      periodicHypercubicEvenBoundaryEffectiveSectionDensity H beta hbeta b ≠ 0 :=
  Filter.Eventually.of_forall fun b =>
    periodicHypercubicEvenBoundaryEffectiveSectionDensity_ne_zero H beta hbeta b

private theorem periodicHypercubicEvenBoundaryVacuumMoment_integrable_boundaryHaar
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Integrable
      (periodicHypercubicEvenBoundaryVacuumMoment
        H 2 boundaryEffectiveSectionDensityTwoRankPositive beta hbeta)
      (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  have hOne :
      Integrable
        (fun _ : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 => (1 : ℝ))
        (periodicHypercubicEvenBoundaryMarginalMeasure
          H 2 boundaryEffectiveSectionDensityTwoRankPositive beta hbeta) :=
    integrable_const 1
  rw [periodicHypercubicEvenBoundaryMarginalMeasure_eq_withDensity_nnreal
    H 2 boundaryEffectiveSectionDensityTwoRankPositive beta hbeta] at hOne
  rw [integrable_withDensity_iff_integrable_smul
    (periodicHypercubicEvenBoundaryMarginalDensityNNReal_measurable
      H 2 boundaryEffectiveSectionDensityTwoRankPositive beta hbeta)] at hOne
  have hSq :
      Integrable
        (fun b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 =>
          periodicHypercubicEvenBoundaryVacuumMoment
            H 2 boundaryEffectiveSectionDensityTwoRankPositive beta hbeta b ^ 2)
        (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
    apply hOne.congr
    filter_upwards with b
    change
      (periodicHypercubicEvenBoundaryMarginalDensityNNReal
        H 2 boundaryEffectiveSectionDensityTwoRankPositive beta hbeta b : ℝ) * 1 =
        periodicHypercubicEvenBoundaryVacuumMoment
          H 2 boundaryEffectiveSectionDensityTwoRankPositive beta hbeta b ^ 2
    rw [mul_one]
    unfold periodicHypercubicEvenBoundaryMarginalDensityNNReal
    rw [Real.coe_toNNReal]
    exact sq_nonneg _
  have hL2 :
      MemLp
        (periodicHypercubicEvenBoundaryVacuumMoment
          H 2 boundaryEffectiveSectionDensityTwoRankPositive beta hbeta)
        2 (periodicHypercubicEvenBoundaryHaarMeasure H 2) :=
    (memLp_two_iff_integrable_sq
      (periodicHypercubicEvenBoundaryVacuumMoment_measurable
        H 2 boundaryEffectiveSectionDensityTwoRankPositive beta hbeta).aestronglyMeasurable).2 hSq
  exact hL2.integrable (by norm_num)

theorem periodicHypercubicEvenBoundaryEffectiveSectionRealWeight_integrable
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Integrable
      (periodicHypercubicEvenBoundaryEffectiveSectionRealWeight H beta hbeta)
      (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  let rho : C(PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2, ℝ) :=
    ⟨periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionBoundaryPrefactor
        H beta hbeta,
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionBoundaryPrefactor_continuous
        H beta hbeta⟩
  have hVac := periodicHypercubicEvenBoundaryVacuumMoment_integrable_boundaryHaar H beta hbeta
  have hRhoMeas :
      AEStronglyMeasurable
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionBoundaryPrefactor
          H beta hbeta)
        (periodicHypercubicEvenBoundaryHaarMeasure H 2) :=
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionBoundaryPrefactor_continuous
      H beta hbeta).measurable.aestronglyMeasurable
  unfold periodicHypercubicEvenBoundaryEffectiveSectionRealWeight
  refine hVac.mul_bdd hRhoMeas ?_
  filter_upwards with b
  simpa [rho] using rho.norm_coe_le_norm b

theorem periodicHypercubicEvenBoundaryEffectiveSection_withDensity_isFiniteMeasure
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsFiniteMeasure
      ((periodicHypercubicEvenBoundaryHaarMeasure H 2).withDensity
        (periodicHypercubicEvenBoundaryEffectiveSectionDensity H beta hbeta)) := by
  apply isFiniteMeasure_withDensity
  have hInt := periodicHypercubicEvenBoundaryEffectiveSectionRealWeight_integrable H beta hbeta
  have hLt :
      (∫⁻ b, periodicHypercubicEvenBoundaryEffectiveSectionDensity H beta hbeta b
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2)) < ∞ := by
    calc
      (∫⁻ b, periodicHypercubicEvenBoundaryEffectiveSectionDensity H beta hbeta b
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2)) =
          ∫⁻ b, ‖periodicHypercubicEvenBoundaryEffectiveSectionRealWeight H beta hbeta b‖ₑ
            ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
        apply lintegral_congr
        intro b
        unfold periodicHypercubicEvenBoundaryEffectiveSectionDensity
        exact (Real.enorm_of_nonneg
          (periodicHypercubicEvenBoundaryEffectiveSectionRealWeight_pos H beta hbeta b).le).symm
      _ < ∞ := hInt.hasFiniteIntegral
  exact hLt.ne

theorem
    periodicHypercubicEvenNormalizedTracePolynomial_effectiveSectionDensity_exists_positiveDegree_exactFourEdgeWilsonTransform_ne_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (k : ℕ) (c : Fin (k + 1) → ℝ) (hc : c ≠ 0) :
    ∃ i : Fin (k + 2),
      0 < (i : ℕ) + 1 ∧
      ∃ d : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2,
        (∫ b,
          periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b *
            specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d)
          ∂((periodicHypercubicEvenBoundaryHaarMeasure H 2).withDensity
            (periodicHypercubicEvenBoundaryEffectiveSectionDensity H beta hbeta.le))) ≠ 0 := by
  letI : IsFiniteMeasure
      ((periodicHypercubicEvenBoundaryHaarMeasure H 2).withDensity
        (periodicHypercubicEvenBoundaryEffectiveSectionDensity H beta hbeta.le)) :=
    periodicHypercubicEvenBoundaryEffectiveSection_withDensity_isFiniteMeasure H beta hbeta.le
  exact
    periodicHypercubicEvenNormalizedTracePolynomial_withDensity_exists_positiveDegree_exactFourEdgeWilsonTransform_ne_zero
      H beta hbeta k c hc
      (periodicHypercubicEvenBoundaryEffectiveSectionDensity H beta hbeta.le)
      (periodicHypercubicEvenBoundaryEffectiveSectionDensity_measurable H beta hbeta.le).aemeasurable
      (periodicHypercubicEvenBoundaryEffectiveSectionDensity_ae_ne_zero H beta hbeta.le)

end

end MathlibAnalytic
end MGAP4D
