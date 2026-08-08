import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryOpenHalfAnalysisOperator
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2TransferGap
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtRectangularKernelAdjoint
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance boundaryMomentAdjointSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryMomentAdjointSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryMomentAdjointSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryMomentAdjointSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryMomentAdjointSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryMomentAdjointSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance boundaryMomentAdjointBoundaryHaarProbability (H N : ℕ) :
    IsProbabilityMeasure (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance boundaryMomentAdjointOpenHalfHaarProbability (H N : ℕ) :
    IsProbabilityMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- A bounded continuous positive-half observable regarded canonically as an
open-half Haar `L²` vector. -/
noncomputable def periodicHypercubicEvenWilsonOpenHalfObservableL2
    (H N : ℕ)
    (u : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ) :
    Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N) :=
  BoundedContinuousFunction.toLp
    (E := ℝ) 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N) ℝ u

/-- The canonical open-half `L²` vector has the original bounded continuous
observable as representative almost everywhere. -/
theorem periodicHypercubicEvenWilsonOpenHalfObservableL2_coeFn
    (H N : ℕ)
    (u : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ) :
    (fun x => periodicHypercubicEvenWilsonOpenHalfObservableL2 H N u x) =ᵐ[
      periodicHypercubicEvenOpenHalfHaarMeasure H N]
      (fun x => u x) := by
  exact BoundedContinuousFunction.coeFn_toLp
    (E := ℝ) 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N) ℝ u

/-- The scalar real inner product is ordinary multiplication. -/
private theorem realScalar_inner_eq_mul (x y : ℝ) :
    inner ℝ x y = x * y := by
  calc
    inner ℝ x y = inner ℝ (x • (1 : ℝ)) (y • (1 : ℝ)) := by simp
    _ = x * (y * inner ℝ (1 : ℝ) (1 : ℝ)) := by
      rw [real_inner_smul_left, real_inner_smul_right]
    _ = x * y := by simp

/-- The physical rectangular feature kernel has the completed-positive-Gram
representative almost everywhere.  This local bridge keeps the boundary-moment
module independent of the heavier static Gram-operator factorization chain. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_adjointBridge_coeFn
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (fun p =>
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
        H N hN beta hbeta p) =ᵐ[
      (periodicHypercubicEvenBoundaryHaarMeasure H N).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H N)]
      (fun p => periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta p.1 p.2) := by
  let hmem :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_memLp_two
      H N hN beta hbeta
  simpa [periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2,
    periodicHypercubicEvenBoundaryOpenHalfHaarMeasure] using
      hmem.coeFn_toLp

/-- The raw completed-positive-Gram feature times an arbitrary boundary/open-half
`L²` tensor is integrable.  This is just `L² × L² → L¹`, exposed directly via
Mathlib's `L2.integrable_inner`. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeature_adjointBridge_weightedPair_integrable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N))
    (g : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N)) :
    Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2 * (f p.1 * g p.2))
      ((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H N)) := by
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H N
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let K := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
    H N hN beta hbeta
  let E := realL2ExternalTensor f g
  have hinner : Integrable
      (fun p => inner ℝ (K p) (E p))
      (boundaryMeasure.prod halfMeasure) :=
    MeasureTheory.L2.integrable_inner K E
  apply hinner.congr
  filter_upwards [
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_adjointBridge_coeFn
      H N hN beta hbeta,
    realL2ExternalTensor_coeFn
      (μ := boundaryMeasure) (ν := halfMeasure) f g] with p hK hE
  rw [show K p = periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H N hN beta hbeta p.1 p.2 by exact hK]
  rw [show E p = f p.1 * g p.2 by exact hE]
  exact realScalar_inner_eq_mul _ _

/-- The boundary moment of a bounded continuous positive-half observable is
a.e.-strongly measurable in the shared-boundary variable. -/
theorem periodicHypercubicEvenBoundaryObservableMoment_aestronglyMeasurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (u : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ) :
    AEStronglyMeasurable
      (fun b => periodicHypercubicEvenBoundaryObservableMoment
        H N hN beta hbeta u b)
      (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H N
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H N
  have hphi :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_jointMeasurable
      H N hN beta hbeta
  have hu : Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        u p.2) :=
    u.continuous.measurable.comp measurable_snd
  have hpsi : AEStronglyMeasurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2 * u p.2)
      (boundaryMeasure.prod halfMeasure) :=
    (hphi.mul hu).aestronglyMeasurable
  simpa [periodicHypercubicEvenBoundaryObservableMoment,
    periodicHypercubicEvenBoundaryObservableGramFeature,
    boundaryMeasure, halfMeasure] using
      hpsi.integral_prod_right'

/-- Uniform norm bound for the scalar boundary moment generated by a bounded
continuous positive-half observable. -/
theorem periodicHypercubicEvenBoundaryObservableMoment_norm_le
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (u : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    ‖periodicHypercubicEvenBoundaryObservableMoment
        H N hN beta hbeta u b‖ ≤
      Real.sqrt
          (((periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹) *
        ‖u‖ := by
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let bound : ℝ :=
    Real.sqrt
          (((periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹) *
        ‖u‖
  have h := norm_integral_le_of_norm_le_const
    (μ := halfMeasure)
    (f := periodicHypercubicEvenBoundaryObservableGramFeature
      H N hN beta hbeta u b)
    (C := bound)
    (Filter.Eventually.of_forall fun x =>
      periodicHypercubicEvenBoundaryObservableGramFeature_norm_le_of_boundedContinuous
        H N hN beta hbeta u b x)
  simpa [periodicHypercubicEvenBoundaryObservableMoment, halfMeasure, bound] using h

/-- Every actual bounded-continuous Wilson boundary moment belongs to complete
boundary Haar `L²`.  This removes `boundaryMoment_memLp` as a model-specific
analytic assumption for the finite Wilson observables used by the physical OS
spine. -/
theorem periodicHypercubicEvenBoundaryObservableMoment_memLp_two
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (u : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ) :
    MemLp
      (fun b => periodicHypercubicEvenBoundaryObservableMoment
        H N hN beta hbeta u b)
      2
      (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  let bound : ℝ :=
    Real.sqrt
          (((periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹) *
        ‖u‖
  exact MemLp.of_bound
    (periodicHypercubicEvenBoundaryObservableMoment_aestronglyMeasurable
      H N hN beta hbeta u)
    bound
    (Filter.Eventually.of_forall fun b =>
      periodicHypercubicEvenBoundaryObservableMoment_norm_le
        H N hN beta hbeta u b)

/-- Canonical boundary-Haar `L²` vector represented by the Wilson boundary
moment of one bounded continuous positive-half observable. -/
noncomputable def periodicHypercubicEvenBoundaryObservableMomentL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (u : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ) :
    Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) :=
  (periodicHypercubicEvenBoundaryObservableMoment_memLp_two
    H N hN beta hbeta u).toLp
      (fun b => periodicHypercubicEvenBoundaryObservableMoment
        H N hN beta hbeta u b)

/-- The canonical boundary-moment `L²` vector has the expected scalar moment
representative. -/
theorem periodicHypercubicEvenBoundaryObservableMomentL2_coeFn
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (u : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ) :
    (fun b => periodicHypercubicEvenBoundaryObservableMomentL2
      H N hN beta hbeta u b) =ᵐ[
      periodicHypercubicEvenBoundaryHaarMeasure H N]
      (fun b => periodicHypercubicEvenBoundaryObservableMoment
        H N hN beta hbeta u b) := by
  exact
    (periodicHypercubicEvenBoundaryObservableMoment_memLp_two
      H N hN beta hbeta u).coeFn_toLp

/-- Matrix coefficients of the canonical boundary-moment `L²` vector are
exactly the rectangular Wilson feature pairings. -/
theorem periodicHypercubicEvenBoundaryObservableMomentL2_inner
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (u : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenBoundaryObservableMomentL2
          H N hN beta hbeta u) f =
      realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
          H N hN beta hbeta)
        f
        (periodicHypercubicEvenWilsonOpenHalfObservableL2 H N u) := by
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H N
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let g := periodicHypercubicEvenWilsonOpenHalfObservableL2 H N u
  let m := periodicHypercubicEvenBoundaryObservableMomentL2
    H N hN beta hbeta u
  let raw := fun p :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H N hN beta hbeta p.1 p.2 * (f p.1 * g p.2)
  have hraw : Integrable raw (boundaryMeasure.prod halfMeasure) := by
    simpa [raw, boundaryMeasure, halfMeasure, g] using
      periodicHypercubicEvenWilsonBoundaryGramFeature_adjointBridge_weightedPair_integrable
        H N hN beta hbeta f g
  calc
    inner ℝ m f = ∫ b, inner ℝ (m b) (f b) ∂boundaryMeasure :=
      MeasureTheory.L2.inner_def m f
    _ = ∫ b,
        periodicHypercubicEvenBoundaryObservableMoment
          H N hN beta hbeta u b * f b ∂boundaryMeasure := by
      apply integral_congr_ae
      filter_upwards [
        periodicHypercubicEvenBoundaryObservableMomentL2_coeFn
          H N hN beta hbeta u] with b hb
      rw [show m b = periodicHypercubicEvenBoundaryObservableMoment
          H N hN beta hbeta u b by exact hb]
      exact realScalar_inner_eq_mul _ _
    _ = ∫ b, ∫ x, raw (b, x) ∂halfMeasure ∂boundaryMeasure := by
      apply integral_congr_ae
      filter_upwards with b
      rw [show periodicHypercubicEvenBoundaryObservableMoment
          H N hN beta hbeta u b =
          ∫ x,
            periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H N hN beta hbeta b x * u x ∂halfMeasure by
        rfl]
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [periodicHypercubicEvenWilsonOpenHalfObservableL2_coeFn
        H N u] with x hx
      simp only [raw]
      rw [show g x = u x by exact hx]
      ring
    _ = ∫ p, raw p ∂(boundaryMeasure.prod halfMeasure) := by
      exact (MeasureTheory.integral_prod raw hraw).symm
    _ = realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
          H N hN beta hbeta) f g := by
      rw [realL2HilbertSchmidtKernelPairing, MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_adjointBridge_coeFn
          H N hN beta hbeta,
        realL2ExternalTensor_coeFn
          (μ := boundaryMeasure) (ν := halfMeasure) f g] with p hK hfg
      rw [hK, hfg, realScalar_inner_eq_mul]
      rfl

/-- Exact finite Wilson identification of the scalar boundary moment with
adjoint feature synthesis:

`m_u = A_φ† u` in complete boundary Haar `L²`. -/
theorem periodicHypercubicEvenBoundaryObservableMomentL2_eq_synthesisOperator
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (u : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ) :
    periodicHypercubicEvenBoundaryObservableMomentL2
        H N hN beta hbeta u =
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
        H N hN beta hbeta
        (periodicHypercubicEvenWilsonOpenHalfObservableL2 H N u) := by
  let K := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
    H N hN beta hbeta
  let g := periodicHypercubicEvenWilsonOpenHalfObservableL2 H N u
  let v := periodicHypercubicEvenBoundaryObservableMomentL2
    H N hN beta hbeta u
  have hv :
      v = realL2HilbertSchmidtRectangularKernelSynthesisOperator K g :=
    realL2HilbertSchmidtRectangularKernel_eq_synthesisOperator_of_inner_eq
      K g v (periodicHypercubicEvenBoundaryObservableMomentL2_inner
        H N hN beta hbeta u)
  simpa [K, g, v,
    realL2HilbertSchmidtRectangularKernelSynthesisOperator,
    periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator,
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator] using hv

/-- The actual physical positive-half observable at scale `n`, represented in
the same open-half Haar `L²` feature space used by the Wilson analysis operator. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N) :=
  periodicHypercubicEvenWilsonOpenHalfObservableL2
    (halfExtent n) N
    (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
      S D halfExtent N hN beta hbeta B hInvariant n F)

/-- The physical finite-Wilson boundary moment is automatically in boundary
Haar `L²`; no extra `boundaryMoment_memLp` hypothesis is needed for these
actual approximating observables. -/
theorem physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_memLp_two
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    MemLp
      (fun b => physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
        S D halfExtent N hN beta hbeta B hInvariant n F b)
      2
      (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) := by
  simpa [physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment] using
    periodicHypercubicEvenBoundaryObservableMoment_memLp_two
      (halfExtent n) N hN (beta n) (hbeta n)
      (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S D halfExtent N hN beta hbeta B hInvariant n F)

/-- The existing physical boundary-moment `L²` vector, for any proof of its
`MemLp` property, is exactly adjoint synthesis of the actual positive-half
observable. -/
theorem physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2_eq_synthesisOperator
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (hF : MemLp
      (fun b => physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
        S D halfExtent N hN beta hbeta B hInvariant n F b)
      2
      (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) :
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F hF =
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
        (halfExtent n) N hN (beta n) (hbeta n)
        (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
          S D halfExtent N hN beta hbeta B hInvariant n F) := by
  let u := physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
    S D halfExtent N hN beta hbeta B hInvariant n F
  let v := physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
    S D halfExtent N hN beta hbeta B hInvariant n F hF
  let m := periodicHypercubicEvenBoundaryObservableMomentL2
    (halfExtent n) N hN (beta n) (hbeta n) u
  have hvm : v = m := by
    apply MeasureTheory.Lp.ext
    filter_upwards [hF.coeFn_toLp,
      periodicHypercubicEvenBoundaryObservableMomentL2_coeFn
        (halfExtent n) N hN (beta n) (hbeta n) u] with b hvb hmb
    rw [show v b = physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
        S D halfExtent N hN beta hbeta B hInvariant n F b by exact hvb]
    rw [show m b = periodicHypercubicEvenBoundaryObservableMoment
        (halfExtent n) N hN (beta n) (hbeta n) u b by exact hmb]
    rfl
  have hm :
      m = periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
        (halfExtent n) N hN (beta n) (hbeta n)
        (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
          S D halfExtent N hN beta hbeta B hInvariant n F) := by
    simpa [u, m,
      physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2] using
      periodicHypercubicEvenBoundaryObservableMomentL2_eq_synthesisOperator
        (halfExtent n) N hN (beta n) (hbeta n) u
  simpa [v] using hvm.trans hm

/-- Audit-visible actual finite-Wilson boundary moment / adjoint-synthesis
package. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentAdjointSynthesisPackage
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) : Prop where
  boundaryMomentMemLp :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier),
      MemLp
        (fun b => physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b)
        2
        (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)
  boundaryMomentSynthesis :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
      (hF : MemLp
        (fun b => physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b)
        2
        (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)),
      physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n F hF =
        periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
          (halfExtent n) N hN (beta n) (hbeta n)
          (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
            S D halfExtent N hN beta hbeta B hInvariant n F)

/-- Construct the physical boundary-moment / adjoint-synthesis receipt. -/
theorem physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentAdjointSynthesisPackage
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentAdjointSynthesisPackage
      S D halfExtent N hN beta hbeta B hInvariant :=
  { boundaryMomentMemLp :=
      physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_memLp_two
        S D halfExtent N hN beta hbeta B hInvariant
    boundaryMomentSynthesis :=
      physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2_eq_synthesisOperator
        S D halfExtent N hN beta hbeta B hInvariant }

end

end MathlibAnalytic
end MGAP4D