import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairObservableInsertion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryGaussLawTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000

local instance pairObservablePhysicalDescentSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance pairObservablePhysicalDescentSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance pairObservablePhysicalDescentSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance pairObservablePhysicalDescentSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance pairObservablePhysicalDescentSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance pairObservablePhysicalDescentSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance pairObservablePhysicalDescentSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A simultaneously gauge-invariant bounded pair observable makes the actual
observable-weighted one-slab `L²` kernel fixed by simultaneous gauge pullback
on its two boundary variables. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2_gaugeFixed
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugePullbackLinearIsometry H N γ
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2
          H N hN beta hbeta b) =
      periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2
        H N hN beta hbeta b := by
  apply Lp.ext
  let Kb :=
    periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2
      H N hN beta hbeta b
  have hPull :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugePullbackLinearIsometry_coeFn
      H N γ Kb
  have hKb :=
    periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2_coeFn
      H N hN beta hbeta b
  have hKbPull :=
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaar_measurePreserving
      H N γ).quasiMeasurePreserving.ae_eq hKb
  filter_upwards [hPull, hKbPull, hKb] with p hpull hkpull hkp
  rw [hpull]
  change
    Kb (periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugeTransform H N γ p) =
      Kb p
  calc
    _ = periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernel
          H N beta b
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugeTransform H N γ p) := by
      simpa [Kb, Function.comp_def] using hkpull
    _ = periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernel
          H N beta b p := by
      simpa using
        periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernel_gaugeInvariant
          H N beta b hb γ p.1 p.2
    _ = Kb p := by
      simpa [Kb] using hkp.symm

/-- The Hilbert--Schmidt pairing defined by a simultaneously gauge-invariant
pair insertion is invariant when both one-slice test vectors are pulled back
by the same spatial gauge transformation. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableKernelPairing_gaugeInvariant
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2
          H N hN beta hbeta b)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N γ f)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N γ g) =
      realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2
          H N hN beta hbeta b) f g := by
  let Kb :=
    periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2
      H N hN beta hbeta b
  let U :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ
  let Upair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugePullbackLinearIsometry H N γ
  change inner ℝ Kb (realL2ExternalTensor (U f) (U g)) =
    inner ℝ Kb (realL2ExternalTensor f g)
  rw [periodicHypercubicEvenSpecialUnitaryRealL2ExternalTensor_gaugePullback H N γ f g]
  have hKbFixed : Upair Kb = Kb := by
    exact
      periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2_gaugeFixed
        H N hN beta hbeta b hb γ
  calc
    inner ℝ Kb (Upair (realL2ExternalTensor f g)) =
        inner ℝ (Upair Kb) (Upair (realL2ExternalTensor f g)) := by
      rw [hKbFixed]
    _ = inner ℝ Kb (realL2ExternalTensor f g) :=
      Upair.inner_map_map Kb (realL2ExternalTensor f g)

/-- The observable-weighted one-slab integral operator commutes with every
finite-volume spatial lattice gauge pullback whenever the inserted pair
observable is simultaneously gauge invariant. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_gauge_commute_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
        H N hN beta hbeta b
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ f) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b f) := by
  apply ext_inner_right ℝ
  intro g
  let U :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ
  let Uinv :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ⁻¹
  have hg : U (Uinv g) = g := by
    exact periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullback_apply_inv H N γ g
  calc
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b (U f)) g =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b (U f)) (U (Uinv g)) := by rw [hg]
    _ = realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2
          H N hN beta hbeta b) (U f) (U (Uinv g)) :=
      periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_inner
        H N hN beta hbeta b (U f) (U (Uinv g))
    _ = realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedKernelPairL2
          H N hN beta hbeta b) f (Uinv g) :=
      periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableKernelPairing_gaugeInvariant
        H N hN beta hbeta b hb γ f (Uinv g)
    _ = inner ℝ
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b f) (Uinv g) :=
      (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_inner
        H N hN beta hbeta b f (Uinv g)).symm
    _ = inner ℝ
        (U (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b f)) (U (Uinv g)) := by
      symm
      exact U.inner_map_map
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b f) (Uinv g)
    _ = inner ℝ
        (U (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b f)) g := by rw [hg]

/-- Operator-level gauge commutation for a simultaneously gauge-invariant pair
insertion. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_gauge_commute
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
        H N hN beta hbeta b).comp
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
        H N γ).toContinuousLinearMap =
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
        H N γ).toContinuousLinearMap.comp
      (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
        H N hN beta hbeta b) := by
  apply ContinuousLinearMap.ext
  intro f
  exact
    periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_gauge_commute_apply
      H N hN beta hbeta b hb γ f

/-- A simultaneously gauge-invariant one-slab pair insertion preserves the
finite-volume Gauss-law physical subspace. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_preserves_GaussLaw
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b)
    {f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)}
    (hf : f ∈ periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
        H N hN beta hbeta b f ∈
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N := by
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_mem] at hf ⊢
  intro γ
  rw [← periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_gauge_commute_apply
    H N hN beta hbeta b hb γ f]
  rw [hf γ]

/-- Genuine physical pair-insertion operator obtained by restricting the
observable-weighted one-slab integral operator to the Gauss-law fixed Hilbert
sector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairObservableOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  ((periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
      H N hN beta hbeta b).comp
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).subtypeL).codRestrict
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
      (fun f =>
        periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_preserves_GaussLaw
          H N hN beta hbeta b hb f.property)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairObservableOperator_coe
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairObservableOperator
        H N hN beta hbeta b hb f :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
      periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
        H N hN beta hbeta b
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  rfl

/-- Physical Gauss-law matrix coefficients retain the exact literal one-slab
Haar integral with the adjacent-slice observable inserted. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairObservableOperator_inner_eq_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairObservableOperator
          H N hN beta hbeta b hb f) g =
      ∫ p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) p.1 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 *
          b p *
          (g : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) p.2
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  change inner ℝ
      (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
        H N hN beta hbeta b
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
      (g : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) = _
  exact
    periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_inner_eq_integral
      H N hN beta hbeta b
      (f : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
      (g : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- Physical one-slab insertion operator for the actual temporal crossing
Wilson action. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTemporalCrossingActionOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairObservableOperator
    H N hN beta hbeta
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable H N)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable_gaugeInvariant
      H N)

/-- Exact physical time-like Wilson-generator insertion: its Gauss-law matrix
coefficient is literally the actual product-Haar one-slab integral with the
temporal crossing action inserted. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTemporalCrossingActionOperator_inner_eq_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTemporalCrossingActionOperator
          H N hN beta hbeta f) g =
      ∫ p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) p.1 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
            H N p.1 p.2 *
          (g : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) p.2
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTemporalCrossingActionOperator]
    using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairObservableOperator_inner_eq_integral
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable H N)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable_gaugeInvariant
          H N) f g)

/-- Audit-visible receipt for the physical descent of adjacent-slice Wilson
insertions.  Only gauge invariance is used; no symmetry or positivity of the
inserted operator is asserted. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTemporalCrossingActionInsertionPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  preservesPhysical :
    ∀ {f : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)},
      f ∈ periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →
      periodicHypercubicEvenSpecialUnitaryOneSlabTemporalCrossingActionOperator
          H N hN beta hbeta f ∈
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
  pairing :
    ∀ f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTemporalCrossingActionOperator
            H N hN beta hbeta f) g =
        ∫ p :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          (f : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) p.1 *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta p.1 p.2 *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
              H N p.1 p.2 *
            (g : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) p.2
          ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- Construct the physical time-like Wilson insertion package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTemporalCrossingActionInsertionPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTemporalCrossingActionInsertionPackage
      H N hN beta hbeta :=
  { preservesPhysical := by
      intro f hf
      exact
        periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_preserves_GaussLaw
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable H N)
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable_gaugeInvariant
            H N) hf
    pairing :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTemporalCrossingActionOperator_inner_eq_integral
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
