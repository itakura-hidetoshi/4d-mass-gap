import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000

local instance positiveHalfPrimaryInsertionSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance positiveHalfPrimaryInsertionSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance positiveHalfPrimaryInsertionSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfPrimaryInsertionSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfPrimaryInsertionSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfPrimaryInsertionSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfPrimaryInsertionSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A bounded continuous observable on one actual spatial slice. -/
abbrev PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable
    (H N : ℕ) : Type :=
  BoundedContinuousFunction
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ

/-- Pointwise lattice-gauge invariance for a bounded one-slice observable. -/
def periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant
    (H N : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N) : Prop :=
  ∀ (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N),
    a (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A) = a A

/-- Multiplication by a bounded one-slice observable preserves Haar `L²`. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable_mul_memLp
    (H N : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    MemLp (fun A => a A * f A) 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  apply (Lp.memLp f).of_le_mul
  · exact a.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  · filter_upwards with A
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (a.norm_coe_le_norm A) (norm_nonneg (f A))

/-- The literal pointwise product, represented in one-slice Haar `L²`. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2
    (H N : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable_mul_memLp
    H N a f).toLp (fun A => a A * f A)

/-- The multiplication vector has the expected pointwise representative. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2_coeFn
    (H N : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2 H N a f =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      fun A => a A * f A :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable_mul_memLp
    H N a f).coeFn_toLp

/-- Pointwise multiplication by one fixed bounded observable is real-linear on
one-slice Haar `L²`. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulLinearMap
    (H N : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →ₗ[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) where
  toFun := periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2 H N a
  map_add' f g := by
    apply Lp.ext
    filter_upwards [
      periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2_coeFn
        H N a (f + g),
      Lp.coeFn_add f g,
      periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2_coeFn H N a f,
      periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2_coeFn H N a g,
      Lp.coeFn_add
        (periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2 H N a f)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2 H N a g)]
      with A hleft hfg hf hg hright
    rw [hleft, hright, hfg, hf, hg]
    ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [
      periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2_coeFn
        H N a (c • f),
      Lp.coeFn_smul c f,
      periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2_coeFn H N a f,
      Lp.coeFn_smul c
        (periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2 H N a f)]
      with A hleft hf hmul hright
    rw [hleft, hright, hf, hmul]
    simp [mul_comm, mul_left_comm, mul_assoc]

/-- The multiplication map satisfies the sharp generic sup-norm bound. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2_norm_le
    (H N : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    ‖periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2 H N a f‖ ≤
      ‖a‖ * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2_coeFn H N a f]
    with A hA
  rw [hA, norm_mul]
  exact mul_le_mul_of_nonneg_right (a.norm_coe_le_norm A) (norm_nonneg (f A))

/-- Bounded multiplication by a one-slice observable as an actual operator on
Haar `L²`. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator
    (H N : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →L[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  LinearMap.mkContinuous
    (periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulLinearMap H N a)
    ‖a‖
    (periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2_norm_le H N a)

@[simp] theorem periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator_apply
    (H N : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator H N a f =
      periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2 H N a f :=
  rfl

/-- Operator norm of bounded multiplication is controlled by the observable
sup norm. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator_norm_le
    (H N : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N) :
    ‖periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator H N a‖ ≤ ‖a‖ := by
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

/-- Gauge-invariant bounded observables preserve the actual finite-volume
Gauss-law Hilbert sector under pointwise multiplication. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMul_mem_physical
    (H N : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator H N a
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) ∈
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N := by
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_mem]
  intro γ
  apply Lp.ext
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let G := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ
  let M := periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator H N a
  have hPullM :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_coeFn
      H N γ (M (f : Lp ℝ 2 μ))
  have hM :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2_coeFn
      H N a (f : Lp ℝ 2 μ)
  have hMG :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H N γ).quasiMeasurePreserving.ae_eq_comp
      hM
  have hfPull :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_coeFn
      H N γ (f : Lp ℝ 2 μ)
  have hfFixed :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
        H N γ (f : Lp ℝ 2 μ) = (f : Lp ℝ 2 μ) := f.property γ
  rw [hfFixed] at hfPull
  filter_upwards [hPullM, hMG, hM, hfPull] with A hpull hmulG hmul hf
  calc
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
        H N γ (M (f : Lp ℝ 2 μ)) A =
      M (f : Lp ℝ 2 μ) (G A) := by simpa [G, M] using hpull
    _ = a (G A) * (f : Lp ℝ 2 μ) (G A) := by
      simpa [Function.comp_def, G, M] using hmulG
    _ = a A * (f : Lp ℝ 2 μ) A := by
      rw [ha γ A]
      rw [← hf]
    _ = M (f : Lp ℝ 2 μ) A := by
      simpa [M] using hmul.symm

/-- Physical bounded multiplication operator on the closed Gauss-law Hilbert
carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator
    (H N : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  LinearMap.mkContinuous
    { toFun := fun f =>
        ⟨periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator H N a
            (f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)),
          periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMul_mem_physical
            H N a ha f⟩
      map_add' := by
        intro f g
        apply Subtype.ext
        exact map_add _ _ _
      map_smul' := by
        intro c f
        apply Subtype.ext
        exact map_smul _ _ _ }
    ‖a‖
    (by
      intro f
      change
        ‖periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator H N a
            (f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖ ≤
          ‖a‖ * ‖(f : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖
      exact
        periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2_norm_le
          H N a (f : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator_coe
    (H N : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator
        H N a ha f :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator H N a
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
  rfl

/-- Physical multiplication retains the same sup-norm operator bound. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator_norm_le
    (H N : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator H N a ha‖ ≤
      ‖a‖ := by
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

/-- Public Haar transport for the primary endpoint of the actual positive-half
closure.  This is the coordinate fact needed to pull almost-everywhere one-slice
identities back to the full closure integral. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosurePrimaryEndpoint_measurePreserving
    (H N : ℕ) :
    MeasurePreserving
      (fun z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
          (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv H N z).1 0)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let temporalMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure H N
  have hTransfer :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv_measurePreserving_explicitHaar
      H N
  have hFst : MeasurePreserving
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ×
          PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N => p.1)
      (pathMu.prod temporalMu) pathMu :=
    MeasureTheory.measurePreserving_fst
  have hEval : MeasurePreserving
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N => path 0)
      pathMu
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
    simpa [pathMu, periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) =>
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        (0 : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1)))
  have hTransfer' : MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv H N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)
      (pathMu.prod temporalMu) := by
    simpa [pathMu, temporalMu,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfExplicitNestedHaarMeasure] using hTransfer
  simpa [Function.comp_def] using hEval.comp (hFst.comp hTransfer')

section PrimaryInsertion

variable
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a)

/-- The actual positive-half endpoint operator with a bounded gauge-invariant
observable inserted on the primary fixed spatial slice. -/
noncomputable def periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservableOperator :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
    H N hN beta hbeta).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator H N a ha)

/-- Exact matrix coefficient of the primary-slice insertion operator.  The
inserted factor is literally the bounded one-slice observable evaluated on the
primary endpoint of the actual positive closure. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservableOperator_inner_eq_integral
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ
        (periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservableOperator
          H N hN beta hbeta a ha f) g =
      ∫ z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
          (Matrix.specialUnitaryGroup (Fin N) ℂ),
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta z.1 z.2 *
          a ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
            H N z).1 0) *
          (f : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
              H N z).1 0) *
          (g : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
              H N z).1
              (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N) := by
  rw [periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservableOperator]
  rw [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator_inner_eq_integral]
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let M := periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator H N a
  have hM :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2_coeFn
      H N a (f : Lp ℝ 2 μ)
  have hPull :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosurePrimaryEndpoint_measurePreserving
      H N).quasiMeasurePreserving.ae_eq_comp hM
  apply integral_congr_ae
  filter_upwards [hPull] with z hz
  have hz' :
      M (f : Lp ℝ 2 μ)
          ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
            H N z).1 0) =
        a ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
          H N z).1 0) *
          (f : Lp ℝ 2 μ)
            ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
              H N z).1 0) := by
    simpa [Function.comp_def, M] using hz
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator_coe]
  rw [hz']
  ring

/-- The inserted endpoint operator inherits the product of the endpoint norm
and the observable sup norm. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservableOperator_norm_le :
    ‖periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservableOperator
        H N hN beta hbeta a ha‖ ≤
      ‖periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
        H N hN beta hbeta‖ * ‖a‖ := by
  calc
    ‖periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservableOperator
        H N hN beta hbeta a ha‖ ≤
      ‖periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
          H N hN beta hbeta‖ *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator
          H N a ha‖ := by
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
          H N hN beta hbeta‖ * ‖a‖ := by
      gcongr
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator_norm_le
          H N a ha

/-- Audit-visible package for the first concrete one-slice observable insertion
bridge into the positive-half endpoint operator carrier. -/
structure PeriodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservablePackage : Prop where
  pairing :
    ∀ f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
      inner ℝ
          (periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservableOperator
            H N hN beta hbeta a ha f) g =
        ∫ z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
            (Matrix.specialUnitaryGroup (Fin N) ℂ),
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H N hN beta hbeta z.1 z.2 *
            a ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
              H N z).1 0) *
            (f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                H N z).1 0) *
            (g : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                H N z).1
                (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)
  normLe :
    ‖periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservableOperator
        H N hN beta hbeta a ha‖ ≤
      ‖periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
        H N hN beta hbeta‖ * ‖a‖

/-- Construct the complete primary-slice observable insertion package. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservablePackage :
    PeriodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservablePackage
      H N hN beta hbeta a ha :=
  { pairing :=
      periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservableOperator_inner_eq_integral
        H N hN beta hbeta a ha
    normLe :=
      periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservableOperator_norm_le
        H N hN beta hbeta a ha }

end PrimaryInsertion

end

end MathlibAnalytic
end MGAP4D