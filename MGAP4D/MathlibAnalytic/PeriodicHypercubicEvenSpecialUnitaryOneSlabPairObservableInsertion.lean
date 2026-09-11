import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfTransferSliceObservableInsertion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2Transfer
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000

local instance pairObservableInsertionSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance pairObservableInsertionSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance pairObservableInsertionSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance pairObservableInsertionSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance pairObservableInsertionSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance pairObservableInsertionSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance pairObservableInsertionSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A bounded continuous observable depending on both adjacent spatial
boundaries of one actual temporal-gauge slab. -/
abbrev PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable
    (H N : ℕ) : Type :=
  BoundedContinuousFunction
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ

/-- Simultaneous lattice-gauge invariance for a bounded observable of two
adjacent spatial boundaries. -/
def periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N) : Prop :=
  ∀ (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N),
    b
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A,
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ B) =
      b (A, B)

/-- Literal one-slab Wilson kernel weighted by a bounded observable of its two
spatial boundaries. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernel
    (H N : ℕ)
    (beta : ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  b p *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta p.1 p.2

/-- The weighted one-slab kernel belongs to product-Haar `L²`.  This is a
bounded-multiplier consequence of the already established `L²` one-slab
Wilson kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernel_memLp_two
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernel
        H N beta b)
      2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  apply
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pair_memLp_two
      H N hN beta hbeta).of_le_mul
  · exact b.continuous.aestronglyMeasurable.mul
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        H N beta).aestronglyMeasurable
  · filter_upwards with p
    unfold periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernel
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (b.norm_coe_le_norm p)
      (norm_nonneg
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2))

/-- Product-Haar `L²` vector of the observable-weighted one-slab kernel. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) :=
  (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernel_memLp_two
    H N hN beta hbeta b).toLp
      (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernel
        H N beta b)

/-- The weighted `L²` kernel vector has the literal pointwise representative. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2_coeFn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N) :
    (fun p =>
      periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2
        H N hN beta hbeta b p) =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernel
        H N beta b :=
  (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernel_memLp_two
    H N hN beta hbeta b).coeFn_toLp

/-- Hilbert--Schmidt operator obtained from the actual one-slab Wilson kernel
after inserting a bounded observable of the adjacent spatial boundaries. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →L[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  realL2HilbertSchmidtKernelOperator
    (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
    (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2
      H N hN beta hbeta b)

/-- Abstract Hilbert--Schmidt pairing formula for the pair-observable
insertion operator. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_inner
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b f) g =
      realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2
          H N hN beta hbeta b) f g := by
  exact realL2HilbertSchmidtKernelOperator_inner
    (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2
      H N hN beta hbeta b) f g

/-- Exact literal matrix coefficient: inserting `b(A,B)` into one actual slab
is the product-Haar integral of `f(A) K(A,B) b(A,B) g(B)`. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_inner_eq_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b f) g =
      ∫ p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        f p.1 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 *
          b p * g p.2
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  rw [periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_inner]
  unfold realL2HilbertSchmidtKernelPairing
  let Kb :=
    periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2
      H N hN beta hbeta b
  let tensor := realL2ExternalTensor
    (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
    (ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) f g
  calc
    inner ℝ Kb tensor =
        ∫ p,
          inner ℝ (Kb p) (tensor p)
          ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
      MeasureTheory.L2.inner_def Kb tensor
    _ = _ := by
      have hKb :=
        periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2_coeFn
          H N hN beta hbeta b
      have hfg := realL2ExternalTensor_coeFn
        (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        (ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) f g
      apply integral_congr_ae
      filter_upwards [hKb, hfg] with p hpKb hpfg
      rw [show Kb p =
          periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernel
            H N beta b p by simpa [Kb] using hpKb]
      rw [show tensor p = f p.1 * g p.2 by
        simpa [tensor, realL2ExternalTensorFunction] using hpfg]
      rw [realL2Scalar_inner_eq_mul]
      unfold periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernel
      ring

/-- Hilbert--Schmidt control of the pair-observable insertion operator. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N) :
    ‖periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
        H N hN beta hbeta b‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2
        H N hN beta hbeta b‖ := by
  exact realL2HilbertSchmidtKernelOperator_norm_le
    (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2
      H N hN beta hbeta b)

/-- Simultaneous gauge invariance of the observable and of the actual one-slab
Wilson kernel gives simultaneous gauge invariance of the weighted kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernel_gaugeInvariant
    (H N : ℕ)
    (beta : ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernel H N beta b
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A,
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ B) =
      periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernel
        H N beta b (A, B) := by
  unfold periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernel
  rw [hb γ A B]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_gaugeInvariant]

/-- The temporal-gauge crossing Wilson action is jointly continuous in the two
adjacent spatial boundaries. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_continuous
    (H N : ℕ) :
    Continuous
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
          H N p.1 p.2) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
  generalize periodicHypercubicEvenSpatialSliceLinkList H = es
  induction es with
  | nil =>
      simpa using
        (continuous_const : Continuous
          (fun _ :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            (0 : ℝ)))
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons]
      have hleft : Continuous
          (fun p :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => p.1 e) :=
        (continuous_apply e).comp continuous_fst
      have hright : Continuous
          (fun p :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => p.2 e) :=
        (continuous_apply e).comp continuous_snd
      have hrelative : Continuous
          (fun p :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            (p.1 e)⁻¹ * p.2 e) := by
        fun_prop
      exact ((continuous_specialUnitaryWilsonPlaquetteEnergy N).comp hrelative).add ih

/-- The actual temporal crossing Wilson action as a bounded continuous
observable of the adjacent spatial boundaries. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun p =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N p.1 p.2,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_continuous H N⟩

@[simp] theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable_apply
    (H N : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable
        H N (A, B) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A B :=
  rfl

/-- The bounded pair-observable realization retains the exact simultaneous
lattice-gauge invariance of the temporal crossing Wilson action. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable_gaugeInvariant
    (H N : ℕ) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable
        H N) := by
  intro γ A B
  exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_gaugeInvariant
    H N γ A B

/-- Concrete one-slab insertion operator for the actual temporal crossing
Wilson action. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSlabTemporalCrossingActionOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →L[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
    H N hN beta hbeta
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable H N)

/-- Exact time-like Wilson-generator insertion on one slab: its matrix
coefficient is literally the actual product-Haar integral with the temporal
crossing action inserted into the one-slab Wilson kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabTemporalCrossingActionOperator_inner_eq_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryOneSlabTemporalCrossingActionOperator
          H N hN beta hbeta f) g =
      ∫ p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        f p.1 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
            H N p.1 p.2 *
          g p.2
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  simpa [periodicHypercubicEvenSpecialUnitaryOneSlabTemporalCrossingActionOperator] using
    (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_inner_eq_integral
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable H N)
      f g)

/-- Audit-visible receipt for the concrete one-slab temporal-crossing Wilson
insertion.  No physical-subspace descent or continuum identification is
asserted here. -/
structure PeriodicHypercubicEvenSpecialUnitaryOneSlabTemporalCrossingActionInsertionPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  pairing :
    ∀ f g : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryOneSlabTemporalCrossingActionOperator
            H N hN beta hbeta f) g =
        ∫ p :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          f p.1 *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta p.1 p.2 *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
              H N p.1 p.2 *
            g p.2
          ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- Construct the concrete time-like Wilson-generator insertion package. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabTemporalCrossingActionInsertionPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryOneSlabTemporalCrossingActionInsertionPackage
      H N hN beta hbeta :=
  { pairing :=
      periodicHypercubicEvenSpecialUnitaryOneSlabTemporalCrossingActionOperator_inner_eq_integral
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
