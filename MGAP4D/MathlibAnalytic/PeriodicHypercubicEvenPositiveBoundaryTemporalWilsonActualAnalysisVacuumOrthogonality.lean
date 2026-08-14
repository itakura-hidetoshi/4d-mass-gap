import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonActualAnalysisTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonBoundaryAnalysisNonzero
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFockProbeWilsonAnalysisFubini
import Mathlib.MeasureTheory.Integral.Prod

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

private theorem positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalitySecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalitySU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityBoundaryFinite
    (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityOpenHalfFinite
    (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- The actual open-half constant-one vector has the expected pointwise
representative. -/
theorem periodicHypercubicEvenOpenHalfConstantOneL2_coeFn
    (H : ℕ) :
    periodicHypercubicEvenOpenHalfConstantOneL2 H 2 =ᵐ[
      periodicHypercubicEvenOpenHalfHaarMeasure H 2]
      (fun _ => (1 : ℝ)) := by
  simpa [periodicHypercubicEvenOpenHalfConstantOneL2,
    periodicHypercubicEvenOpenHalfConstantOneContinuous] using
    (ContinuousMap.coeFn_toLp
      (p := (2 : ENNReal)) (𝕜 := ℝ)
      (periodicHypercubicEvenOpenHalfHaarMeasure H 2)
      (periodicHypercubicEvenOpenHalfConstantOneContinuous H 2))

/-- The Haar image of the interacting constant boundary vacuum is pointwise the
finite Wilson OS boundary vacuum moment `ψ`.  Thus the density isometry sends
`1` exactly to the square-root marginal density, not merely to an abstract
isometric copy. -/
theorem periodicHypercubicEvenBoundaryVacuumHaarL2_coeFn
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenBoundaryVacuumHaarL2 H beta hbeta =ᵐ[
      periodicHypercubicEvenBoundaryHaarMeasure H 2]
      periodicHypercubicEvenBoundaryVacuumMoment
        H 2 positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTwoRankPositive
        beta hbeta := by
  let marginalMeasure :=
    periodicHypercubicEvenBoundaryMarginalMeasure
      H 2 positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTwoRankPositive
      beta hbeta
  have hvacuumMarginal :
      periodicHypercubicEvenBoundaryMarginalVacuumL2 H beta hbeta =ᵐ[
        marginalMeasure] (fun _ => (1 : ℝ)) := by
    simpa [marginalMeasure,
      periodicHypercubicEvenBoundaryMarginalVacuumL2] using
      (ContinuousMap.coeFn_toLp
        (p := (2 : ENNReal)) (𝕜 := ℝ) marginalMeasure
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
          (0 : ℕ)))
  have hvacuumHaar :=
    periodicHypercubicEven_ae_marginal_to_boundaryHaar
      H 2 positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTwoRankPositive
      beta hbeta hvacuumMarginal
  have htransport :=
    periodicHypercubicEvenBoundaryMarginalToHaarL2_coeFn
      H 2 positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTwoRankPositive
      beta hbeta
      (periodicHypercubicEvenBoundaryMarginalVacuumL2 H beta hbeta)
  unfold periodicHypercubicEvenBoundaryVacuumHaarL2
  filter_upwards [htransport, hvacuumHaar] with b htransport_b hvacuum_b
  rw [htransport_b]
  unfold periodicHypercubicEvenBoundaryMarginalToHaarL2Function
  rw [hvacuum_b]
  simp

/-- The actual completed-positive Wilson kernel times an arbitrary boundary
Haar `L²` input is integrable on boundary × positive-open-half Haar.  This is
exactly the `L² × L² → L¹` Hilbert-Schmidt mechanism with the right tensor
factor specialized to the physical open-half vacuum. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_boundaryInput_weightedPair_integrable
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2)) :
    Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H 2 positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTwoRankPositive
            beta hbeta p.1 p.2 * f p.1)
      ((periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H 2)) := by
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H 2
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H 2
  let K := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
    H 2 positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTwoRankPositive
    beta hbeta
  let g := periodicHypercubicEvenOpenHalfConstantOneL2 H 2
  let E := realL2ExternalTensor f g
  have hinner : Integrable
      (fun p => inner ℝ (K p) (E p))
      (boundaryMeasure.prod halfMeasure) :=
    MeasureTheory.L2.integrable_inner K E
  apply hinner.congr
  filter_upwards [
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_cyclicFockPairing_coeFn
      H beta hbeta,
    realL2ExternalTensor_coeFn
      (μ := boundaryMeasure) (ν := halfMeasure) f g,
    (Measure.quasiMeasurePreserving_snd
      (μ := boundaryMeasure) (ν := halfMeasure)).ae_eq
      (periodicHypercubicEvenOpenHalfConstantOneL2_coeFn H)] with p hK hE hg
  rw [show K p =
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H 2 positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTwoRankPositive
        beta hbeta p.1 p.2 by exact hK]
  rw [show E p = f p.1 * g p.2 by exact hE]
  have hg' : g p.2 = (1 : ℝ) := by
    simpa [Function.comp_apply, g] using hg
  rw [hg']
  simp [periodicHypercubicEven_real_inner_eq_mul]

/-- The open-half vacuum matrix coefficient of the actual Wilson analysis is
exactly the boundary Haar pairing with the finite Wilson OS vacuum moment.
This is the concrete Fubini form of `A† 1 = ψ`. -/
theorem periodicHypercubicEvenOpenHalfConstantOneL2_inner_analysis_eq_boundaryVacuumMoment_integral
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2)) :
    inner ℝ
        (periodicHypercubicEvenOpenHalfConstantOneL2 H 2)
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTwoRankPositive
          beta hbeta f) =
      ∫ b,
        periodicHypercubicEvenBoundaryVacuumMoment
            H 2 positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTwoRankPositive
            beta hbeta b * f b
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H 2
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H 2
  let K := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
    H 2 positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTwoRankPositive
    beta hbeta
  let g := periodicHypercubicEvenOpenHalfConstantOneL2 H 2
  let raw := fun p :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H 2 positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTwoRankPositive
        beta hbeta p.1 p.2 * f p.1
  have hraw : Integrable raw (boundaryMeasure.prod halfMeasure) := by
    simpa [raw, boundaryMeasure, halfMeasure] using
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_boundaryInput_weightedPair_integrable
        H beta hbeta f
  calc
    inner ℝ
        (periodicHypercubicEvenOpenHalfConstantOneL2 H 2)
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTwoRankPositive
          beta hbeta f) =
      realL2HilbertSchmidtKernelPairing K f g := by
        rw [real_inner_comm]
        simpa [K, g] using
          periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_inner
            H 2 positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTwoRankPositive
            beta hbeta f g
    _ = ∫ p, raw p ∂(boundaryMeasure.prod halfMeasure) := by
      rw [realL2HilbertSchmidtKernelPairing, MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_cyclicFockPairing_coeFn
          H beta hbeta,
        realL2ExternalTensor_coeFn
          (μ := boundaryMeasure) (ν := halfMeasure) f g,
        (Measure.quasiMeasurePreserving_snd
          (μ := boundaryMeasure) (ν := halfMeasure)).ae_eq
          (periodicHypercubicEvenOpenHalfConstantOneL2_coeFn H)] with p hK hE hg
      rw [show K p =
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H 2 positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTwoRankPositive
            beta hbeta p.1 p.2 by exact hK]
      rw [show realL2ExternalTensor f g p = f p.1 * g p.2 by exact hE]
      have hg' : g p.2 = (1 : ℝ) := by
        simpa [Function.comp_apply, g] using hg
      rw [hg']
      simp [raw, periodicHypercubicEven_real_inner_eq_mul]
    _ = ∫ b, ∫ x, raw (b, x) ∂halfMeasure ∂boundaryMeasure := by
      exact MeasureTheory.integral_prod raw hraw
    _ = ∫ b,
        periodicHypercubicEvenBoundaryVacuumMoment
            H 2 positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTwoRankPositive
            beta hbeta b * f b
        ∂boundaryMeasure := by
      apply integral_congr_ae
      filter_upwards with b
      simp only [raw]
      rw [integral_mul_const]
      rfl

/-- Exact actual-operator vacuum adjoint identity in Hilbert form.  The
square-root-density transport of the interacting constant boundary vector is
the adjoint image of the actual open-half vacuum. -/
theorem periodicHypercubicEvenOpenHalfConstantOneL2_inner_analysis_eq_boundaryVacuumHaarL2_inner
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2)) :
    inner ℝ
        (periodicHypercubicEvenOpenHalfConstantOneL2 H 2)
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTwoRankPositive
          beta hbeta f) =
      inner ℝ
        (periodicHypercubicEvenBoundaryVacuumHaarL2 H beta hbeta)
        f := by
  rw [periodicHypercubicEvenOpenHalfConstantOneL2_inner_analysis_eq_boundaryVacuumMoment_integral]
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [periodicHypercubicEvenBoundaryVacuumHaarL2_coeFn
    H beta hbeta] with b hvac
  rw [hvac]
  exact periodicHypercubicEven_real_inner_eq_mul _ _

/-- A centered interacting-boundary polynomial remains orthogonal to the
physical open-half vacuum after the **actual** Wilson analysis operator.  This
is not an abstract density-change statement: the preceding theorem identifies
the adjoint vacuum with the finite Wilson OS vacuum moment pointwise. -/
theorem periodicHypercubicEvenBoundaryNormalizedTracePolynomial_actualAnalysisOutput_centered
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hzero :
      inner ℝ
        (periodicHypercubicEvenBoundaryMarginalVacuumL2 H beta hbeta)
        (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
          H beta hbeta k c) = 0) :
    inner ℝ
        (periodicHypercubicEvenOpenHalfConstantOneL2 H 2)
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 positiveBoundaryTemporalWilsonActualAnalysisVacuumOrthogonalityTwoRankPositive
          beta hbeta
          (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
            H beta hbeta k c)) = 0 := by
  rw [periodicHypercubicEvenOpenHalfConstantOneL2_inner_analysis_eq_boundaryVacuumHaarL2_inner]
  exact periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2_centered
    H beta hbeta k c hzero

end

end MathlibAnalytic
end MGAP4D
