import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderBoundaryPairFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfHaarTemporalGaugeReduction
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfSpatialPathBoundaryInteriorIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfSpatialPathBoundaryInteriorCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfSpatialPathBoundaryInteriorSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfSpatialPathBoundaryInteriorMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfSpatialPathBoundaryInteriorBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfSpatialPathBoundaryInteriorSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The strict interior spatial path consists of the slices at Euclidean times
`1, ..., H`.  It is deliberately a single `Fin H`-indexed path.  In
particular, for `H = 1` there is one central slice rather than two independent
copies of that slice. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPath
    (H N : ℕ) : Type :=
  Fin H → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N

/-- Product one-slice Haar law on all strict interior spatial slices. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaarMeasure
    (H N : ℕ) :
    Measure (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPath H N) :=
  Measure.pi
    (fun _ : Fin H =>
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

instance periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaar_isProbabilityMeasure
    (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaarMeasure
  infer_instance

/-- The target Haar law after separating the two outer reflection boundaries
from all strict interior spatial slices. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPositiveHalfBoundaryInteriorSpatialHaarMeasure
    (H N : ℕ) :
    Measure
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPath H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N).prod
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaarMeasure H N)

instance periodicHypercubicEvenSpecialUnitaryPositiveHalfBoundaryInteriorSpatialHaar_isProbabilityMeasure
    (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfBoundaryInteriorSpatialHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfBoundaryInteriorSpatialHaarMeasure
  infer_instance

/-- Exact time-index classification of the actual complete positive-half path
carrier.  Its source is written with the canonical slab-count index rather
than a propositionally equal `Fin (H+2)`, so all downstream measurable-space
and Haar statements live on exactly the existing carrier. -/
def periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv
    (H : ℕ) :
    Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) ≃
      (Fin 2 ⊕ Fin H) where
  toFun j :=
    if h0 : j.1 = 0 then
      Sum.inl 0
    else if hlast : j.1 = H + 1 then
      Sum.inl 1
    else
      Sum.inr ⟨j.1 - 1, by
        simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount] at j
        omega⟩
  invFun z :=
    match z with
    | Sum.inl i =>
        if hi : i.1 = 0 then
          0
        else
          ⟨H + 1, by
            simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
    | Sum.inr k => ⟨k.1 + 1, by
        simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]
        omega⟩
  left_inv j := by
    by_cases h0 : j.1 = 0
    · have hj : j = 0 := Fin.ext h0
      rw [hj]
      simp
    · by_cases hlast : j.1 = H + 1
      · have hj : j = ⟨H + 1, by
          simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩ :=
          Fin.ext hlast
        rw [hj]
        simp
    · simp [h0, hlast]
      apply Fin.ext
      simp
      omega
  right_inv z := by
    rcases z with i | k
    · fin_cases i <;> simp
    · have h0 : k.1 + 1 ≠ 0 := by omega
      have hlast : k.1 + 1 ≠ H + 1 := by omega
      simp [h0, hlast]

/-- Measurable equivalence separating a complete positive-half spatial path
into its ordered outer boundary pair and its strict interior path.

This is constructed only from canonical finite-product measurable
reindexing/splitting equivalences. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ≃ᵐ
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPath H N) :=
  let X : Fin 2 ⊕ Fin H → Type :=
    fun _ => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let reindex :=
    MeasurableEquiv.piCongrLeft X
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv H)
  let split := MeasurableEquiv.sumPiEquivProdPi X
  let pair :=
    MeasurableEquiv.piFinTwo
      (fun _ : Fin 2 =>
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
  reindex.trans
    (split.trans
      (MeasurableEquiv.prodCongr pair
        (MeasurableEquiv.refl
          (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPath H N))))

/-- The boundary/interior measurable equivalence returns the two literal outer
path slices and the literal strict interior slices in Euclidean-time order. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_apply
    (H N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
        H N path =
      ((path 0,
          path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))),
        fun k : Fin H => path ⟨k.1 + 1, by
          simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]
          omega⟩) := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · rfl
  · funext k
    rfl

/-- The first component of the Haar decomposition is exactly the outer
boundary pair already used by the pointwise Markov factorization. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_fst_eq_outerBoundaryPair
    (H N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
      H N path).1 =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathOuterBoundaryPair path := by
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_apply]
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathOuterBoundaryPair
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex
  rfl

/-- The complete positive-half spatial-path product Haar law is exactly the
product of pair-Haar on the two outer reflection boundaries and product Haar
on the `H` strict interior spatial slices.

This theorem is the finite-product Fubini coordinate theorem needed before
lifting the pointwise boundary-pair Markov factorization to an integral and
then to the ambient pair-Haar transfer operator. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_measurePreserving
    (H N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
        H N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfBoundaryInteriorSpatialHaarMeasure H N) := by
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let X : Fin 2 ⊕ Fin H → Type :=
    fun _ => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  have hReindex :=
    MeasureTheory.measurePreserving_piCongrLeft
      (fun _ : Fin 2 ⊕ Fin H => mu)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv H)
  have hSplit :=
    MeasureTheory.measurePreserving_sumPiEquivProdPi
      (fun _ : Fin 2 ⊕ Fin H => mu)
  have hPair :=
    MeasureTheory.measurePreserving_piFinTwo
      (fun _ : Fin 2 => mu)
  have hInterior :
      MeasurePreserving
        (MeasurableEquiv.refl
          (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPath H N))
        (Measure.pi (fun _ : Fin H => mu))
        (Measure.pi (fun _ : Fin H => mu)) :=
    MeasurePreserving.id _
  have hNested := hPair.prod hInterior
  simpa [
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfBoundaryInteriorSpatialHaarMeasure,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaarMeasure,
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
    X, mu] using
      (hReindex.trans hSplit).trans hNested

end

end MathlibAnalytic
end MGAP4D
