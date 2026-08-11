import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtSeparableKernelOperator
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramDeterminant
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance betaZeroAnalysisSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance betaZeroAnalysisTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance betaZeroAnalysisCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance betaZeroAnalysisSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance betaZeroAnalysisMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance betaZeroAnalysisBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance betaZeroAnalysisSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance betaZeroAnalysisBoundaryHaarFinite (H N : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance betaZeroAnalysisOpenHalfHaarFinite (H N : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- At zero coupling the completed positive Wilson Gram feature is independent
of both boundary and open-half variables.  We deliberately leave the finite
partition function unevaluated: only separability, not its numerical value, is
needed for the rank-one obstruction. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN 0 (by norm_num) b x =
      Real.sqrt
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)).base.partitionFunction⁻¹) := by
  simp [periodicHypercubicEvenBoundaryCompletedPositiveGramFeature,
    periodicHypercubicEvenBoundaryGramCoefficient,
    periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight,
    periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight,
    periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude,
    periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude,
    periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude,
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight,
    one_div]

/-- Constant boundary `L²` factor of the zero-coupling Wilson Gram kernel. -/
noncomputable def periodicHypercubicEvenWilsonBoundaryBetaZeroLeftFactorL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) :=
  (MeasureTheory.Lp.const 2 (periodicHypercubicEvenBoundaryHaarMeasure H N))
    (Real.sqrt
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)).base.partitionFunction⁻¹))

/-- Constant-one open-half `L²` factor of the zero-coupling Wilson Gram
kernel. -/
noncomputable def periodicHypercubicEvenWilsonBoundaryBetaZeroRightFactorL2
    (H N : ℕ) :
    Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N) :=
  (MeasureTheory.Lp.const 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N)) (1 : ℝ)

/-- The actual zero-coupling boundary/open-half Wilson Gram feature is exactly
a separable external tensor. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2_zero_eq_externalTensor
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2
        H N hN 0 (by norm_num) =
      realL2ExternalTensor
        (periodicHypercubicEvenWilsonBoundaryBetaZeroLeftFactorL2 H N hN)
        (periodicHypercubicEvenWilsonBoundaryBetaZeroRightFactorL2 H N) := by
  let μ := periodicHypercubicEvenBoundaryHaarMeasure H N
  let ν := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let c : ℝ := Real.sqrt
    ((periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)).base.partitionFunction⁻¹)
  let u : Lp ℝ 2 μ :=
    (MeasureTheory.Lp.const 2 μ) c
  let v : Lp ℝ 2 ν :=
    (MeasureTheory.Lp.const 2 ν) (1 : ℝ)
  change periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2
      H N hN 0 (by norm_num) = realL2ExternalTensor u v
  have hu : (fun z :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
      u z.1) =ᵐ[μ.prod ν] (fun _ => c) := by
    simpa [u, μ, ν, Function.comp_def] using
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq
        (MeasureTheory.Lp.coeFn_const 2 μ c)
  have hv : (fun z :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
      v z.2) =ᵐ[μ.prod ν] (fun _ => (1 : ℝ)) := by
    simpa [v, μ, ν, Function.comp_def] using
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq
        (MeasureTheory.Lp.coeFn_const 2 ν (1 : ℝ))
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2
  apply Lp.ext
  filter_upwards
    [(periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_memLp_two
        H N hN 0 (by norm_num)).coeFn_toLp,
      realL2ExternalTensor_coeFn u v,
      hu, hv] with z hz hTensor huz hvz
  rw [hz, hTensor, huz, hvz]
  change periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H N hN 0 (by norm_num) z.1 z.2 = c * 1
  rw [periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_zero]
  rfl

/-- Product-measure form of the same zero-coupling separable-kernel identity. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_zero_eq_externalTensor
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
        H N hN 0 (by norm_num) =
      realL2ExternalTensor
        (periodicHypercubicEvenWilsonBoundaryBetaZeroLeftFactorL2 H N hN)
        (periodicHypercubicEvenWilsonBoundaryBetaZeroRightFactorL2 H N) := by
  simpa [periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2,
    periodicHypercubicEvenBoundaryOpenHalfHaarMeasure] using
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2_zero_eq_externalTensor
      H N hN

/-- Exact zero-coupling formula for the actual Wilson boundary analysis
operator.  Its range is contained in the span of one constant open-half mode. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_zero_apply
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H N hN 0 (by norm_num) f =
      (inner ℝ
        (periodicHypercubicEvenWilsonBoundaryBetaZeroLeftFactorL2 H N hN) f) •
        periodicHypercubicEvenWilsonBoundaryBetaZeroRightFactorL2 H N := by
  unfold periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
  rw [periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_zero_eq_externalTensor]
  exact realL2HilbertSchmidtRectangularKernelOperator_externalTensor_apply _ _ _

/-- Every actual zero-coupling Wilson analysis output lies in a fixed
one-dimensional subspace. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_zero_mem_span_singleton
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H N hN 0 (by norm_num) f ∈
      Submodule.span ℝ
        ({periodicHypercubicEvenWilsonBoundaryBetaZeroRightFactorL2 H N} :
          Set (Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N))) := by
  rw [periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_zero_apply]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span
      (Set.mem_singleton
        (periodicHypercubicEvenWilsonBoundaryBetaZeroRightFactorL2 H N)))

/-- At zero coupling every concrete SU(2) primary-plaquette analysis image is a
scalar multiple of the same constant open-half `L²` mode. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage_zero_eq_smul
    (H k : ℕ) (j : Fin (k + 1)) :
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
        H 0 (by norm_num) k j =
      (inner ℝ
        (periodicHypercubicEvenWilsonBoundaryBetaZeroLeftFactorL2 H 2 (by norm_num))
        (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode
          H k j)) •
      periodicHypercubicEvenWilsonBoundaryBetaZeroRightFactorL2 H 2 := by
  unfold periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
  exact periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_zero_apply
    H 2 (by norm_num) _

/-- The first two actual SU(2) primary-plaquette analysis images have singular
Gram matrix at zero coupling.  Consequently the determinant-nondegeneracy
frontier from #1638/#1639 cannot be proved under the bare assumption
`0 ≤ beta`: the endpoint `beta = 0` is a genuine rank-one obstruction. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_zero_twoMode_det
    (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
        H 0 (by norm_num) 1).det = 0 := by
  rw [Matrix.det_fin_two]
  simp only [periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix,
    Matrix.gram_apply]
  rw [periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage_zero_eq_smul
      H 1 (0 : Fin 2),
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage_zero_eq_smul
      H 1 (1 : Fin 2)]
  simp only [real_inner_smul_left, real_inner_smul_right]
  ring

/-- In particular, the finite determinant hypothesis used by the normal-output
route is false at `beta = 0` already for `k = 1`. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_zero_twoMode_not_det_ne_zero
    (H : ℕ) :
    ¬ (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
        H 0 (by norm_num) 1).det ≠ 0 := by
  intro hdet
  exact hdet
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_zero_twoMode_det H)

end

end MathlibAnalytic
end MGAP4D
