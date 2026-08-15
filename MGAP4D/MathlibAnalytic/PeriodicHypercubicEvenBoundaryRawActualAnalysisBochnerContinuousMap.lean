import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeatureJointContinuity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryRawActualAnalysisContinuity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2RawActualAnalysisContinuousPullbackClosure
import Mathlib.MeasureTheory.SpecificCodomains.ContinuousMap
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology

noncomputable section

private theorem boundaryRawActualAnalysisBochnerTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance boundaryRawActualAnalysisBochnerNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryRawActualAnalysisBochnerTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryRawActualAnalysisBochnerCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryRawActualAnalysisBochnerSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryRawActualAnalysisBochnerMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryRawActualAnalysisBochnerBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryRawActualAnalysisBochnerSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance boundaryRawActualAnalysisBochnerBoundaryHaarFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  unfold periodicHypercubicEvenBoundaryHaarMeasure
  unfold FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure
  infer_instance

/-- The scalar raw-analysis boundary integrand, bundled as one continuous
function of the positive open-half variable.  The boundary variable is now the
Bochner-integration variable in the Banach space `C(X, ℝ)`. -/
noncomputable def
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMapIntegrand
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    C(PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2, ℝ) :=
  (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b *
      periodicHypercubicEvenBoundaryVacuumMoment
        H 2 boundaryRawActualAnalysisBochnerTwoRankPositive beta hbeta b) •
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMapSU2
      H beta hbeta b

@[simp] theorem
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMapIntegrand_apply
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMapIntegrand
        H beta hbeta k c b x =
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b *
        periodicHypercubicEvenBoundaryVacuumMoment
          H 2 boundaryRawActualAnalysisBochnerTwoRankPositive beta hbeta b) *
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H 2 boundaryRawActualAnalysisBochnerTwoRankPositive beta hbeta b x := by
  rfl

/-- The `C(X,ℝ)`-valued boundary integrand is Bochner integrable with respect
to boundary Haar measure.  The proof reuses exactly the scalar dominated bound:
compactness bounds the normalized-trace polynomial, the Gram feature is bounded
by the reciprocal partition function, and the actual OS boundary vacuum moment
is already `L¹`. -/
theorem
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMapIntegrand_integrable
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    Integrable
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMapIntegrand
        H beta hbeta k c)
      (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  let μ := periodicHypercubicEvenBoundaryHaarMeasure H 2
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  let psi := periodicHypercubicEvenBoundaryVacuumMoment
    H 2 boundaryRawActualAnalysisBochnerTwoRankPositive beta hbeta
  let Kmap := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMapSU2
    H beta hbeta
  let Phi :=
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMapIntegrand
      H beta hbeta k c
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) 2
    boundaryRawActualAnalysisBochnerTwoRankPositive beta hbeta
  let zbound : ℝ := Real.sqrt (C.base.partitionFunction⁻¹)
  let bound : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 → ℝ :=
    fun b => (‖p‖ * zbound) * psi b
  have hp : Measurable (fun b => p b) := p.continuous.measurable
  have hpsi : Measurable psi := by
    simpa [psi] using
      periodicHypercubicEvenBoundaryVacuumMoment_measurable
        H 2 boundaryRawActualAnalysisBochnerTwoRankPositive beta hbeta
  have hKmap : Measurable Kmap := by
    exact
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMapSU2_continuous
        H beta hbeta).measurable
  have hPhiMeas : Measurable Phi := by
    simpa [Phi,
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMapIntegrand,
      p, psi, Kmap] using (hp.mul hpsi).smul hKmap
  have hPhiStrong : AEStronglyMeasurable Phi μ :=
    hPhiMeas.aestronglyMeasurable
  have hBound : ∀ᵐ b ∂μ, ∀ x, ‖Phi b x‖ ≤ bound b := by
    filter_upwards [] with b
    intro x
    have hpB : ‖p b‖ ≤ ‖p‖ := p.norm_coe_le_norm b
    have hpsi0 : 0 ≤ psi b := by
      simpa [psi] using
        periodicHypercubicEvenBoundaryVacuumMoment_nonneg
          H 2 boundaryRawActualAnalysisBochnerTwoRankPositive beta hbeta b
    have hK0 : 0 ≤
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H 2 boundaryRawActualAnalysisBochnerTwoRankPositive beta hbeta b x := by
      exact
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg
          H 2 boundaryRawActualAnalysisBochnerTwoRankPositive beta hbeta b x
    have hKle :
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H 2 boundaryRawActualAnalysisBochnerTwoRankPositive beta hbeta b x ≤
          zbound := by
      simpa [zbound, C] using
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_le_sqrt_inv_partitionFunction
          H 2 boundaryRawActualAnalysisBochnerTwoRankPositive beta hbeta b x
    have hpsiNorm : ‖psi b‖ = psi b := by
      rw [Real.norm_eq_abs, abs_of_nonneg hpsi0]
    have hKNorm :
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H 2 boundaryRawActualAnalysisBochnerTwoRankPositive beta hbeta b x‖ =
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H 2 boundaryRawActualAnalysisBochnerTwoRankPositive beta hbeta b x := by
      rw [Real.norm_eq_abs, abs_of_nonneg hK0]
    change
      ‖(p b * psi b) *
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H 2 boundaryRawActualAnalysisBochnerTwoRankPositive beta hbeta b x‖ ≤
        (‖p‖ * zbound) * psi b
    rw [norm_mul, norm_mul, hpsiNorm, hKNorm]
    calc
      ‖p b‖ * psi b *
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H 2 boundaryRawActualAnalysisBochnerTwoRankPositive beta hbeta b x ≤
        ‖p‖ * psi b *
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H 2 boundaryRawActualAnalysisBochnerTwoRankPositive beta hbeta b x :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpB hpsi0) hK0
      _ ≤ ‖p‖ * psi b * zbound :=
        mul_le_mul_of_nonneg_left hKle
          (mul_nonneg (norm_nonneg p) hpsi0)
      _ = (‖p‖ * zbound) * psi b := by ring
  have hBoundIntegrable : Integrable bound μ := by
    have hpsiInt :=
      periodicHypercubicEvenBoundaryVacuumMoment_integrable_boundaryHaar_actualAnalysis
        H beta hbeta
    simpa [bound, psi, μ] using hpsiInt.const_mul (‖p‖ * zbound)
  have hFinite : HasFiniteIntegral Phi μ :=
    ContinuousMap.hasFiniteIntegral_of_bound
      Phi bound hBoundIntegrable.hasFiniteIntegral hBound
  exact ⟨hPhiStrong, hFinite⟩

/-- The raw actual-analysis `ContinuousMap` obtained by Bochner integration in
`C(X,ℝ)`. -/
noncomputable def
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBochnerContinuousMap
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    C(PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2, ℝ) :=
  ∫ b,
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMapIntegrand
      H beta hbeta k c b
    ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2)

/-- Evaluation of the Banach-space-valued Bochner integral is exactly the
original pointwise scalar boundary integral. -/
@[simp] theorem
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBochnerContinuousMap_apply
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBochnerContinuousMap
        H beta hbeta k c x =
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysis
        H beta hbeta k c x := by
  rw [periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBochnerContinuousMap]
  rw [ContinuousMap.integral_apply
    (periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMapIntegrand_integrable
      H beta hbeta k c) x]
  rfl

/-- Hence the Bochner-integral construction is not a new raw observable: it is
exactly the already-used theorem-generated raw actual-analysis continuous map. -/
theorem
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBochnerContinuousMap_eq_existing
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBochnerContinuousMap
        H beta hbeta k c =
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMap
        H beta hbeta k c := by
  ext x
  simp

end

end MathlibAnalytic
end MGAP4D
