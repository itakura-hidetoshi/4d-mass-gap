import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeatureOpenHalfContinuity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryEffectiveSectionAnalysisValue
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryOpenHalfProductL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

private theorem boundaryRawActualAnalysisContinuityTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance boundaryRawActualAnalysisContinuityNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryRawActualAnalysisContinuityTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryRawActualAnalysisContinuityCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryRawActualAnalysisContinuitySecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryRawActualAnalysisContinuityMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryRawActualAnalysisContinuityBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryRawActualAnalysisContinuitySU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance boundaryRawActualAnalysisContinuityBoundaryHaarFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  unfold periodicHypercubicEvenBoundaryHaarMeasure
  unfold FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure
  infer_instance

local instance boundaryRawActualAnalysisContinuityMarginalFinite
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsFiniteMeasure
      (periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta) := by
  rw [← periodicHypercubicEvenSpecialUnitary_map_boundaryRestriction_gibbsMeasure
    H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta]
  let mu :=
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) 2
      boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta).gibbsMeasure
  change IsFiniteMeasure
    (Measure.map (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction mu)
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    exact periodicHypercubicSpecialUnitaryWilsonSystem_gibbsMeasure_probability
      (PeriodicHypercubicEvenSideLength H) 2
      boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta
  letI : IsFiniteMeasure mu := ⟨by simp⟩
  exact Measure.isFiniteMeasure_map mu
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction

/-- The actual finite Wilson OS boundary vacuum wavefunction is integrable with
respect to boundary Haar measure.  This public receipt is the `L¹` domination
input needed for continuity of the raw boundary-to-open-half analysis integral. -/
theorem periodicHypercubicEvenBoundaryVacuumMoment_integrable_boundaryHaar_actualAnalysis
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Integrable
      (periodicHypercubicEvenBoundaryVacuumMoment
        H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta)
      (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  have hOne :
      Integrable
        (fun _ : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 => (1 : ℝ))
        (periodicHypercubicEvenBoundaryMarginalMeasure
          H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta) :=
    integrable_const 1
  rw [periodicHypercubicEvenBoundaryMarginalMeasure_eq_withDensity_nnreal
    H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta] at hOne
  rw [integrable_withDensity_iff_integrable_smul
    (periodicHypercubicEvenBoundaryMarginalDensityNNReal_measurable
      H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta)] at hOne
  have hSq :
      Integrable
        (fun b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 =>
          periodicHypercubicEvenBoundaryVacuumMoment
            H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta b ^ 2)
        (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
    apply hOne.congr
    filter_upwards with b
    change
      (periodicHypercubicEvenBoundaryMarginalDensityNNReal
        H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta b : ℝ) * 1 =
        periodicHypercubicEvenBoundaryVacuumMoment
          H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta b ^ 2
    rw [mul_one]
    unfold periodicHypercubicEvenBoundaryMarginalDensityNNReal
    rw [Real.coe_toNNReal]
    exact sq_nonneg _
  have hL2 :
      MemLp
        (periodicHypercubicEvenBoundaryVacuumMoment
          H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta)
        2 (periodicHypercubicEvenBoundaryHaarMeasure H 2) :=
    (memLp_two_iff_integrable_sq
      (periodicHypercubicEvenBoundaryVacuumMoment_measurable
        H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta).aestronglyMeasurable).2 hSq
  exact hL2.integrable (by norm_num)

/-- The explicit raw actual Wilson analysis representative is continuous on the
positive open-half configuration space.  The proof uses dominated continuity:
the normalized-trace polynomial is bounded on compact boundary space, the
actual completed-positive Gram feature is uniformly bounded by the reciprocal
partition function, and the OS boundary vacuum wavefunction is `L¹`. -/
theorem periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysis_continuous
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    Continuous
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysis
        H beta hbeta k c) := by
  let μ := periodicHypercubicEvenBoundaryHaarMeasure H 2
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  let psi := periodicHypercubicEvenBoundaryVacuumMoment
    H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta
  let K := periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
    H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) 2
    boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta
  let zbound : ℝ := Real.sqrt (C.base.partitionFunction⁻¹)
  let F :
      (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) →
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 → ℝ :=
    fun x b => (p b * psi b) * K b x
  let bound : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 → ℝ :=
    fun b => (‖p‖ * zbound) * psi b
  have hFMeas : ∀ x, AEStronglyMeasurable (F x) μ := by
    intro x
    have hp : Measurable (fun b => p b) := p.continuous.measurable
    have hpsi : Measurable psi := by
      simpa [psi] using
        periodicHypercubicEvenBoundaryVacuumMoment_measurable
          H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta
    have hKjoint :=
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_jointMeasurable
        H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta
    have hKx : Measurable (fun b => K b x) := by
      simpa [K] using
        hKjoint.comp (measurable_id.prodMk measurable_const)
    exact ((hp.mul hpsi).mul hKx).aestronglyMeasurable
  have hBound : ∀ x, ∀ᵐ b ∂μ, ‖F x b‖ ≤ bound b := by
    intro x
    filter_upwards [] with b
    have hpB : ‖p b‖ ≤ ‖p‖ := p.norm_coe_le_norm b
    have hpsi0 : 0 ≤ psi b := by
      simpa [psi] using
        periodicHypercubicEvenBoundaryVacuumMoment_nonneg
          H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta b
    have hK0 : 0 ≤ K b x := by
      simpa [K] using
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg
          H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta b x
    have hKle : K b x ≤ zbound := by
      simpa [K, zbound, C] using
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_le_sqrt_inv_partitionFunction
          H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta b x
    change ‖(p b * psi b) * K b x‖ ≤ (‖p‖ * zbound) * psi b
    rw [norm_mul, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg hpsi0, Real.norm_eq_abs, abs_of_nonneg hK0]
    calc
      ‖p b‖ * psi b * K b x ≤ ‖p‖ * psi b * K b x :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpB hpsi0) hK0
      _ ≤ ‖p‖ * psi b * zbound :=
        mul_le_mul_of_nonneg_left hKle
          (mul_nonneg (norm_nonneg p) hpsi0)
      _ = (‖p‖ * zbound) * psi b := by ring
  have hBoundIntegrable : Integrable bound μ := by
    have hpsi :=
      periodicHypercubicEvenBoundaryVacuumMoment_integrable_boundaryHaar_actualAnalysis
        H beta hbeta
    simpa [bound, psi, μ] using hpsi.const_mul (‖p‖ * zbound)
  have hCont : ∀ᵐ b ∂μ, Continuous (fun x => F x b) := by
    filter_upwards [] with b
    dsimp [F]
    exact continuous_const.mul
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_continuous_openHalf
        H 2 boundaryRawActualAnalysisContinuityTwoRankPositive beta hbeta b)
  have hIntegral : Continuous (fun x => ∫ b, F x b ∂μ) :=
    MeasureTheory.continuous_of_dominated hFMeas hBound hBoundIntegrable hCont
  simpa [periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysis,
    F, μ, p, psi, K] using hIntegral

end

end MathlibAnalytic
end MGAP4D
