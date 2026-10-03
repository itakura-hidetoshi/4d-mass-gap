import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSUNTwoModeFiniteOSUncenteredPairPhysical
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyGramSchmidtBoundaryRepresentative
import Mathlib.Tactic

/-!
# SU(2) Wilson Gram--Schmidt boundary modes are physical endpoint-pair modes

The post-H1-D5 route no longer needs to remain inside the first two Wilson
modes.  SU(2) already has the theorem-generated infinite orthonormal
Wilson-energy Gram--Schmidt family.

This file proves the finite pair-side geometry for every mode k:

* define the corresponding gauge-invariant primary-slice physical L2 vector;
* identify the actual boundary-Haar Gram--Schmidt mode, in ordered endpoint
  coordinates, with the decomposable pair f_k tensor 1;
* conclude physical-pair carrier membership;
* preserve the already-proved orthonormality under the exact boundary/pair
  linear isometry.

This is purely kinematic.  No transfer, top-mode, gap, vacuum alignment,
H1-D5 compatibility, or continuum dynamics is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section

local instance su2GramSchmidtPairPhysicalTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2GramSchmidtPairPhysicalCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2GramSchmidtPairPhysicalSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2GramSchmidtPairPhysicalMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2GramSchmidtPairPhysicalBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2GramSchmidtPairPhysicalSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2GramSchmidtPairPhysicalSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Continuous bounded observable on one spatial slice obtained from the
k-th SU(2) Wilson-energy Gram--Schmidt class function. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
    (H k : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H 2 :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun A =>
        specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
            (periodicHypercubicEvenPrimarySpatialSlicePlaquette H)),
      by
        apply
          (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k).continuous.comp
        unfold periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
        fun_prop⟩

/-- The arbitrary Gram--Schmidt primary-plaquette slice observable is gauge
invariant because its SU(2) class function is conjugation invariant. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable_gaugeInvariant
    (H k : ℕ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant
      H 2
      (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
        H k) := by
  intro γ A
  change
    specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
            H 2 γ A)
          (periodicHypercubicEvenPrimarySpatialSlicePlaquette H)) =
      specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialSlicePlaquette H))
  rw [periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_gaugeTransform]
  exact
    specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode_conjInvariant k
      (γ (periodicHypercubicEvenPrimarySpatialSlicePlaquette H).1)
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
        (periodicHypercubicEvenPrimarySpatialSlicePlaquette H))

/-- The corresponding vector in the finite one-slice Gauss-law Hilbert
carrier. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
    (H k : ℕ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
  periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator
      H 2
      (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
        H k)
      (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable_gaugeInvariant
        H k)
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)

/-- The one-slice physical vector has the intended pointwise continuous
Gram--Schmidt representative. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2_coeFn
    (H k : ℕ) :
    (fun A =>
      (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
        H k :
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) A) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2]
      fun A =>
        periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
          H k A := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let a :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
      H k
  change
    (fun A =>
      periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2
        H 2 a (Lp.const 2 μ (1 : ℝ)) A) =ᵐ[μ]
      fun A => a A
  have hmul :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2_coeFn
      H 2 a (Lp.const 2 μ (1 : ℝ))
  have hone :
      (Lp.const 2 μ (1 : ℝ)) =ᵐ[μ] fun _ => (1 : ℝ) := by
    simpa using
      (Lp.coeFn_const (μ := μ) (p := (2 : ENNReal)) (c := (1 : ℝ)))
  filter_upwards [hmul, hone] with A hmulA honeA
  rw [hmulA, honeA]
  simp

/-- In ordered primary/antipodal slice coordinates, the boundary observable is
the primary-slice Gram--Schmidt observable and is independent of the antipodal
slice. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryObservable_pairCoordinates
    (H k : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryObservable
        H k
        ((periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
          (Matrix.specialUnitaryGroup (Fin 2) ℂ)).symm (A, B)) =
      periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
        H k A := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryObservable
  unfold periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
  have hedges :
      (fun j =>
        (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
          (Matrix.specialUnitaryGroup (Fin 2) ℂ)).symm (A, B)
          (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H j)) =
        (fun j => A
          (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H j)) := by
    funext j
    exact
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_symm_apply_primaryPlaquetteEdge
        H 2 A B j
  rw [hedges]
  change
    specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
        (haarFinFourCyclicPlaquetteWord
          (fun j => A
            (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H j))) =
      specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialSlicePlaquette H))
  rw [
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomy_eq_orientedFourEdge
      H 2 A,
    orientedFourEdgePlaquetteWord_eq_conj_haarFinFourCyclicPlaquetteWord]
  symm
  exact
    specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode_conjInvariant k
      (A (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H 0) *
        A (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H 1))
      (haarFinFourCyclicPlaquetteWord
        (fun j => A
          (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H j)))

/-- The k-th theorem-generated boundary Gram--Schmidt vector transported to the
ordered pair carrier. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2
    (H k : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H 2 :=
  periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H 2
    (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
      H k)

/-- Exact factorization of every SU(2) Gram--Schmidt pair mode as the
decomposable physical pair f_k tensor 1. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2_eq_physicalDecomposable
    (H k : ℕ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2
        H k =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
        H 2
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
          H k)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let e :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  let f :=
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
      H k
  apply Lp.ext
  have hforward :=
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry_coeFn
      H 2 f
  have hboundary :=
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2_coeFn
      H k
  have he :
      MeasurePreserving e.symm
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)
        (periodicHypercubicEvenBoundaryHaarMeasure H 2) :=
    MeasurePreserving.symm e
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_specialUnitaryHaar
        H 2)
  have hboundaryPair :=
    he.quasiMeasurePreserving.ae_eq hboundary
  have hboundaryPair' :
      (fun z => f (e.symm z)) =ᵐ[
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2]
        fun z =>
          periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryObservable
            H k (e.symm z) := by
    simpa [f, e, Function.comp_def] using hboundaryPair
  have hmode :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2_coeFn
      H k
  have hmodeFst :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq hmode
  have hone :
      (Lp.const 2 μ (1 : ℝ)) =ᵐ[μ] fun _ => (1 : ℝ) := by
    simpa using
      (Lp.coeFn_const (μ := μ) (p := (2 : ENNReal)) (c := (1 : ℝ)))
  have honeSnd :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq hone
  have htensor :=
    realL2ExternalTensor_coeFn
      (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
        H k :
        Lp ℝ 2 μ)
      (Lp.const 2 μ (1 : ℝ))
  filter_upwards [hforward, hboundaryPair', hmodeFst, honeSnd, htensor]
      with z hfor hbd hmodez honez hten
  change
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H 2 f z =
      realL2ExternalTensor
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
          H k :
          Lp ℝ 2 μ)
        (Lp.const 2 μ (1 : ℝ)) z
  rw [hfor]
  change
    f (e.symm z) =
      realL2ExternalTensor
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
          H k :
          Lp ℝ 2 μ)
        (Lp.const 2 μ (1 : ℝ)) z
  rw [hbd, hten]
  have hmodez' :
      (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
        H k :
        Lp ℝ 2 μ) z.1 =
      periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
        H k z.1 := by
    simpa [Function.comp_def] using hmodez
  have honez' : (Lp.const 2 μ (1 : ℝ)) z.2 = 1 := by
    simpa [Function.comp_def] using honez
  rw [hmodez', honez']
  rw [
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryObservable_pairCoordinates
      H k z.1 z.2]
  simp [realL2ExternalTensorFunction]

/-- Every SU(2) Wilson Gram--Schmidt pair mode belongs to the completed physical
pair carrier. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2_mem_physicalPairCarrier
    (H k : ℕ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2
        H k ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H 2 := by
  rw [
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2_eq_physicalDecomposable
      H k]
  apply
    Submodule.le_topologicalClosure
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H 2)
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan]
  apply Submodule.subset_span
  exact
    ⟨(periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2 H k,
        periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2), rfl⟩

/-- Transport to ordered endpoint coordinates preserves the full infinite
Gram--Schmidt orthonormal family. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2_orthonormal
    (H : ℕ) :
    Orthonormal ℝ
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2
        H) := by
  exact
    (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2_orthonormal
      H).comp_linearIsometry
        (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H 2)

end

end MathlibAnalytic
end MGAP4D
