import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedPairIndependentGaugeFixed
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCarrierFourBlockDecomposition
import Mathlib.Tactic

/-!
# Independent endpoint Gauss-law fixed sector for the physical pair carrier

The one-slice physical Hilbert space is the common fixed space of all spatial
lattice gauge pullbacks.  The two-endpoint physical pair carrier is, by
definition, the Hilbert closure of external tensors of two such one-slice
physical vectors.

This file places that definition inside the intrinsic common fixed space for
the *independent* primary/antipodal endpoint gauge action constructed in
`PhysicalYangMillsWilsonVacuumNormalizedPairIndependentGaugeFixed`.

The key points are:

* independent endpoint pullback intertwines exactly with the external tensor of
  the two one-slice pullbacks;
* therefore every decomposable physical pair is independently gauge fixed;
* the independent fixed space is a closed submodule;
* hence the entire completed physical pair carrier lies in that fixed space.

No reverse inclusion is asserted here.  That converse is the remaining
Hilbert-tensor/fixed-space direction of H1-D4.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance physicalPairIndependentFixedTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairIndependentFixedCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairIndependentFixedSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairIndependentFixedMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairIndependentFixedBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairIndependentFixedSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairIndependentFixedSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- External tensors intertwine the two independent one-slice gauge pullbacks
with the independent endpoint pair pullback. -/
theorem periodicHypercubicEvenSpecialUnitaryRealL2ExternalTensor_independentGaugePullback
    (H N : ℕ)
    (gammaPrimary gammaAntipodal :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    realL2ExternalTensor
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N gammaPrimary f)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N gammaAntipodal g) =
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
        H N gammaPrimary gammaAntipodal (realL2ExternalTensor f g) := by
  apply Lp.ext
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let UPrimary :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
      H N gammaPrimary
  let UAntipodal :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
      H N gammaAntipodal
  let GPrimary :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N gammaPrimary
  let GAntipodal :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N gammaAntipodal
  let GPair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeTransform
      H N gammaPrimary gammaAntipodal
  have hLeft :=
    realL2ExternalTensor_coeFn
      (μ := mu) (ν := mu) (UPrimary f) (UAntipodal g)
  have hf :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_coeFn
      H N gammaPrimary f
  have hg :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_coeFn
      H N gammaAntipodal g
  have hfPair :
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        UPrimary f p.1) =ᵐ[mu.prod mu]
        fun p => f (GPrimary p.1) := by
    simpa [mu, UPrimary, GPrimary, Function.comp_def] using
      (Measure.quasiMeasurePreserving_fst (μ := mu) (ν := mu)).ae_eq hf
  have hgPair :
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        UAntipodal g p.2) =ᵐ[mu.prod mu]
        fun p => g (GAntipodal p.2) := by
    simpa [mu, UAntipodal, GAntipodal, Function.comp_def] using
      (Measure.quasiMeasurePreserving_snd (μ := mu) (ν := mu)).ae_eq hg
  have hRight :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry_coeFn
      H N gammaPrimary gammaAntipodal (realL2ExternalTensor f g)
  have hTensor :=
    realL2ExternalTensor_coeFn (μ := mu) (ν := mu) f g
  have hTensorPull :=
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeTransform_measurePreserving
      H N gammaPrimary gammaAntipodal).quasiMeasurePreserving.ae_eq hTensor
  filter_upwards [hLeft, hfPair, hgPair, hRight, hTensorPull]
      with p hleft hfp hgp hright htensor
  calc
    realL2ExternalTensor (UPrimary f) (UAntipodal g) p =
        realL2ExternalTensorFunction (UPrimary f) (UAntipodal g) p := hleft
    _ = f (GPrimary p.1) * g (GAntipodal p.2) := by
      simp only [realL2ExternalTensorFunction]
      rw [hfp, hgp]
    _ = realL2ExternalTensorFunction f g (GPair p) := by
      rfl
    _ = realL2ExternalTensor f g (GPair p) := by
      simpa [GPair, Function.comp_def] using htensor.symm
    _ =
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
          H N gammaPrimary gammaAntipodal (realL2ExternalTensor f g) p :=
      hright.symm

/-- Closed common fixed subspace of all independent primary/antipodal endpoint
gauge pullbacks on pair Haar `L²`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule
    (H N : ℕ) :
    ClosedSubmodule ℝ
      (PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :=
  ⨅ gammaPrimary :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
    ⨅ gammaAntipodal :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
      (⊥ : ClosedSubmodule ℝ
        (PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)).comap
        ((periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
            H N gammaPrimary gammaAntipodal).toContinuousLinearMap -
          ContinuousLinearMap.id ℝ
            (PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N))

/-- Membership in the closed independent-gauge sector is exactly common
fixedness under all independent endpoint pullbacks. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule_mem
    (H N : ℕ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    F ∈
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule
          H N ↔
      ∀ gammaPrimary gammaAntipodal :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
            H N gammaPrimary gammaAntipodal F =
          F := by
  simp [
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule,
    sub_eq_zero]

/-- Every decomposable pair of one-slice Gauss-law physical vectors is fixed by
arbitrary independent endpoint gauge transformations. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2_independentGaugeFixed
    (H N : ℕ)
    (x y :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (gammaPrimary gammaAntipodal :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
        H N gammaPrimary gammaAntipodal
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2 H N x y) =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2 H N x y := by
  have hx :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N gammaPrimary
          (x : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
        (x : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_mem
      H N (x : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))).1
      x.property gammaPrimary
  have hy :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N gammaAntipodal
          (y : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
        (y : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_mem
      H N (y : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))).1
      y.property gammaAntipodal
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2]
  rw [← periodicHypercubicEvenSpecialUnitaryRealL2ExternalTensor_independentGaugePullback]
  rw [hx, hy]

/-- The algebraic physical-pair span lies in the common fixed space of the
independent endpoint gauge action. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan_le_independentGaugeInvariantL2ClosedSubmodule
    (H N : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H N ≤
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule
        H N).toSubmodule := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan]
  refine Submodule.span_le.2 ?_
  rintro z ⟨⟨x, y⟩, rfl⟩
  rw [
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule_mem]
  intro gammaPrimary gammaAntipodal
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2_independentGaugeFixed
      H N x y gammaPrimary gammaAntipodal

/-- The completed physical pair carrier is contained in the intrinsic common
fixed sector for arbitrary independent endpoint gauge transformations.

This is the forward inclusion in H1-D4.  It is obtained without any Wilson
dynamics: algebraic physical tensors are fixed factorwise, and Mathlib's
closed-submodule/topological-closure API propagates fixedness to the Hilbert
completion. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_le_independentGaugeInvariantL2ClosedSubmodule
    (H N : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N ≤
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule
        H N).toSubmodule := by
  change
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H N).topologicalClosure ≤
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule
        H N).toSubmodule
  apply
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H N).topologicalClosure_minimal
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan_le_independentGaugeInvariantL2ClosedSubmodule
        H N
  · exact
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule
        H N).isClosed

/-- Every vector in the completed physical pair carrier is therefore fixed by
all independent endpoint gauge pullbacks. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_independentGaugeFixed
    (H N : ℕ)
    {F : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N}
    (hF : F ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N)
    (gammaPrimary gammaAntipodal :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
        H N gammaPrimary gammaAntipodal F =
      F := by
  have hFixed :
      F ∈
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule
          H N :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_le_independentGaugeInvariantL2ClosedSubmodule
      H N hF
  exact
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule_mem
      H N F).1 hFixed gammaPrimary gammaAntipodal

/-- Audit-visible receipt for the forward fixed-space inclusion of H1-D4. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalPairIndependentGaugeFixedSectorPackage
    (H N : ℕ) : Prop where
  decomposableFixed :
    ∀ (x y :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
      (gammaPrimary gammaAntipodal :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N),
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
          H N gammaPrimary gammaAntipodal
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2 H N x y) =
        periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2 H N x y
  carrierLeFixed :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N ≤
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugeInvariantL2ClosedSubmodule
        H N).toSubmodule

/-- Construct the forward H1-D4 independent-gauge fixed-sector package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairIndependentGaugeFixedSectorPackage
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairIndependentGaugeFixedSectorPackage
      H N :=
  { decomposableFixed :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2_independentGaugeFixed
        H N
    carrierLeFixed :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_le_independentGaugeInvariantL2ClosedSubmodule
        H N }

end

end MathlibAnalytic
end MGAP4D
