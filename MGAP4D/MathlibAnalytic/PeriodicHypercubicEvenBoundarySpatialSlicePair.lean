import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEdgeSideClassification
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedPiMeasure
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSlice
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryObservableGram
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance boundarySpatialSlicePairSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundarySpatialSlicePairSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance boundarySpatialSlicePairSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundarySpatialSlicePairSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundarySpatialSlicePairSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundarySpatialSlicePairSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundarySpatialSlicePairSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Vertices on the second, antipodal, reflection-fixed time slice. -/
abbrev PeriodicHypercubicEvenAntipodalSpatialSliceVertex (H : ℕ) : Type :=
  {v : PeriodicHypercubicEvenVertex H //
    periodicHypercubicEvenOnAntipodalReflectionPlane H v}

/-- Positively oriented spatial links on the antipodal reflection-fixed slice. -/
abbrev PeriodicHypercubicEvenAntipodalSpatialSliceLink (H : ℕ) : Type :=
  PeriodicHypercubicEvenAntipodalSpatialSliceVertex H ×
    PeriodicHypercubicEvenSpatialDirection

/-- Translate a vertex by exactly half of the even periodic Euclidean-time
circle.  This exchanges the primary and antipodal reflection-fixed slices. -/
def periodicHypercubicEvenHalfPeriodTimeShift
    (H : ℕ)
    (v : PeriodicHypercubicEvenVertex H) :
    PeriodicHypercubicEvenVertex H :=
  fun i =>
    if i = 0 then
      v i + ((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))
    else
      v i

@[simp] theorem periodicHypercubicEvenHalfPeriodTimeShift_time
    (H : ℕ)
    (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenHalfPeriodTimeShift H v 0 =
      v 0 + ((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) := by
  simp [periodicHypercubicEvenHalfPeriodTimeShift]

@[simp] theorem periodicHypercubicEvenHalfPeriodTimeShift_space
    (H : ℕ)
    (v : PeriodicHypercubicEvenVertex H)
    {i : PeriodicHypercubicAxis}
    (hi : i ≠ 0) :
    periodicHypercubicEvenHalfPeriodTimeShift H v i = v i := by
  simp [periodicHypercubicEvenHalfPeriodTimeShift, hi]

/-- The half-period time shift is an involution. -/
theorem periodicHypercubicEvenHalfPeriodTimeShift_involutive
    (H : ℕ) :
    Function.Involutive (periodicHypercubicEvenHalfPeriodTimeShift H) := by
  intro v
  funext i
  by_cases hi : i = 0
  · subst i
    rw [periodicHypercubicEvenHalfPeriodTimeShift_time]
    rw [periodicHypercubicEvenHalfPeriodTimeShift_time]
    rw [add_assoc, periodicHypercubicEven_halfPeriod_add_self H, add_zero]
  · rw [periodicHypercubicEvenHalfPeriodTimeShift_space H _ hi]
    rw [periodicHypercubicEvenHalfPeriodTimeShift_space H _ hi]

/-- Half-period translation sends the primary fixed slice to the antipodal one. -/
def periodicHypercubicEvenPrimaryToAntipodalSpatialSliceVertex
    (H : ℕ)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H) :
    PeriodicHypercubicEvenAntipodalSpatialSliceVertex H :=
  ⟨periodicHypercubicEvenHalfPeriodTimeShift H v.1, by
    unfold periodicHypercubicEvenOnAntipodalReflectionPlane
    rw [periodicHypercubicEvenHalfPeriodTimeShift_time, v.2]
    simp⟩

/-- Half-period translation sends the antipodal fixed slice back to the primary
one. -/
def periodicHypercubicEvenAntipodalToPrimarySpatialSliceVertex
    (H : ℕ)
    (v : PeriodicHypercubicEvenAntipodalSpatialSliceVertex H) :
    PeriodicHypercubicEvenSpatialSliceVertex H :=
  ⟨periodicHypercubicEvenHalfPeriodTimeShift H v.1, by
    unfold periodicHypercubicEvenOnPrimaryReflectionPlane
    rw [periodicHypercubicEvenHalfPeriodTimeShift_time, v.2]
    exact periodicHypercubicEven_halfPeriod_add_self H⟩

/-- Canonical equivalence between the two reflection-fixed spatial slices. -/
def periodicHypercubicEvenPrimaryAntipodalSpatialSliceVertexEquiv
    (H : ℕ) :
    PeriodicHypercubicEvenSpatialSliceVertex H ≃
      PeriodicHypercubicEvenAntipodalSpatialSliceVertex H where
  toFun := periodicHypercubicEvenPrimaryToAntipodalSpatialSliceVertex H
  invFun := periodicHypercubicEvenAntipodalToPrimarySpatialSliceVertex H
  left_inv v := by
    apply Subtype.ext
    exact periodicHypercubicEvenHalfPeriodTimeShift_involutive H v.1
  right_inv v := by
    apply Subtype.ext
    exact periodicHypercubicEvenHalfPeriodTimeShift_involutive H v.1

/-- The same half-period translation gives an equivalence of spatial link
indices; spatial directions themselves are unchanged. -/
def periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv
    (H : ℕ) :
    PeriodicHypercubicEvenSpatialSliceLink H ≃
      PeriodicHypercubicEvenAntipodalSpatialSliceLink H :=
  Equiv.prodCongr
    (periodicHypercubicEvenPrimaryAntipodalSpatialSliceVertexEquiv H)
    (Equiv.refl PeriodicHypercubicEvenSpatialDirection)

/-- The two reflection-fixed time slices are disjoint. -/
theorem periodicHypercubicEven_primary_antipodal_disjoint
    (H : ℕ)
    (v : PeriodicHypercubicEvenVertex H)
    (hprimary : periodicHypercubicEvenOnPrimaryReflectionPlane H v)
    (hantipodal : periodicHypercubicEvenOnAntipodalReflectionPlane H v) :
    False := by
  unfold periodicHypercubicEvenOnPrimaryReflectionPlane at hprimary
  unfold periodicHypercubicEvenOnAntipodalReflectionPlane at hantipodal
  have hzero :
      (0 : ZMod (PeriodicHypercubicEvenSideLength H)) =
        ((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) :=
    hprimary.symm.trans hantipodal
  have hlt : H + 1 < PeriodicHypercubicEvenSideLength H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  have hval := congrArg ZMod.val hzero
  simp [ZMod.val_natCast_of_lt hlt] at hval

/-- A fixed edge cannot point in the Euclidean-time direction. -/
theorem periodicHypercubicEvenFixedEdge_direction_ne_zero
    (H : ℕ)
    (e : (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge) :
    e.1.2 ≠ 0 := by
  intro htime
  have hfixed :
      periodicHypercubicEvenEdgeSide H e.1 = ReflectionEdgeSide.fixed :=
    e.2
  have hedge : e.1 = (e.1.1, 0) := by
    apply Prod.ext
    · rfl
    · exact htime
  by_cases hle : (e.1.1 0).val ≤ H
  · have hpos :=
      periodicHypercubicEvenEdgeSide_time_eq_positive_of_val_le
        H e.1.1 hle
    rw [← hedge, hfixed] at hpos
    cases hpos
  · have hhalf : H + 1 ≤ (e.1.1 0).val := by omega
    have hneg :=
      periodicHypercubicEvenEdgeSide_time_eq_negative_of_half_le_val
        H e.1.1 hhalf
    rw [← hedge, hfixed] at hneg
    cases hneg

/-- Every fixed edge is a spatial edge based on exactly one of the two
reflection-fixed time slices. -/
theorem periodicHypercubicEvenFixedEdge_on_primary_or_antipodal
    (H : ℕ)
    (e : (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge) :
    periodicHypercubicEvenOnPrimaryReflectionPlane H e.1.1 ∨
      periodicHypercubicEvenOnAntipodalReflectionPlane H e.1.1 := by
  have hspace := periodicHypercubicEvenFixedEdge_direction_ne_zero H e
  have hfixed :
      periodicHypercubicEvenEdgeSide H e.1 = ReflectionEdgeSide.fixed :=
    e.2
  by_cases hzero : (e.1.1 0).val = 0
  · left
    unfold periodicHypercubicEvenOnPrimaryReflectionPlane
    exact (ZMod.val_eq_zero _).mp hzero
  · by_cases hhalf : (e.1.1 0).val = H + 1
    · right
      unfold periodicHypercubicEvenOnAntipodalReflectionPlane
      rw [← ZMod.natCast_zmod_val (e.1.1 0)]
      exact congrArg
        (fun a : ℕ => (a : ZMod (PeriodicHypercubicEvenSideLength H))) hhalf
    · have hpos : 1 ≤ (e.1.1 0).val := Nat.one_le_iff_ne_zero.2 hzero
      by_cases hle : (e.1.1 0).val ≤ H
      · have hside :=
          periodicHypercubicEvenEdgeSide_spatial_eq_positive_of_val
            H e.1 hspace hpos hle
        rw [hfixed] at hside
        cases hside
      · have hneg : H + 1 < (e.1.1 0).val := by omega
        have hside :=
          periodicHypercubicEvenEdgeSide_spatial_eq_negative_of_half_lt_val
            H e.1 hspace hneg
        rw [hfixed] at hside
        cases hside

/-- Embed a primary-slice spatial link into the fixed edge sector. -/
def periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge
    (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge :=
  ⟨(e.1.1, e.2.1), by
    change periodicHypercubicEvenEdgeSide H (e.1.1, e.2.1) =
      ReflectionEdgeSide.fixed
    apply periodicHypercubicEvenEdgeSide_eq_fixed_of_reflection_eq
    exact periodicHypercubicEvenEdgeReflection_eq_self_of_spatial_on_fixedPlane
      H (e.1.1, e.2.1) e.2.2 (Or.inl e.1.2)⟩

/-- Embed an antipodal-slice spatial link into the fixed edge sector. -/
def periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge
    (H : ℕ)
    (e : PeriodicHypercubicEvenAntipodalSpatialSliceLink H) :
    (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge :=
  ⟨(e.1.1, e.2.1), by
    change periodicHypercubicEvenEdgeSide H (e.1.1, e.2.1) =
      ReflectionEdgeSide.fixed
    apply periodicHypercubicEvenEdgeSide_eq_fixed_of_reflection_eq
    exact periodicHypercubicEvenEdgeReflection_eq_self_of_spatial_on_fixedPlane
      H (e.1.1, e.2.1) e.2.2 (Or.inr e.1.2)⟩

/-- Read a fixed edge as either a primary-slice link or, after the canonical
half-period reindexing, another primary-slice link. -/
noncomputable def periodicHypercubicEvenFixedEdgeToSpatialSliceSum
    (H : ℕ)
    (e : (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge) :
    PeriodicHypercubicEvenSpatialSliceLink H ⊕
      PeriodicHypercubicEvenSpatialSliceLink H := by
  classical
  have hspace := periodicHypercubicEvenFixedEdge_direction_ne_zero H e
  by_cases hp : periodicHypercubicEvenOnPrimaryReflectionPlane H e.1.1
  · exact Sum.inl (⟨e.1.1, hp⟩, ⟨e.1.2, hspace⟩)
  · have ha : periodicHypercubicEvenOnAntipodalReflectionPlane H e.1.1 :=
      (periodicHypercubicEvenFixedEdge_on_primary_or_antipodal H e).resolve_left hp
    let ea : PeriodicHypercubicEvenAntipodalSpatialSliceLink H :=
      (⟨e.1.1, ha⟩, ⟨e.1.2, hspace⟩)
    exact Sum.inr
      ((periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H).symm ea)

/-- Assemble either of the two primary-indexed spatial-slice copies back into a
fixed edge; the second copy is first translated to the antipodal slice. -/
noncomputable def periodicHypercubicEvenSpatialSliceSumToFixedEdge
    (H : ℕ) :
    PeriodicHypercubicEvenSpatialSliceLink H ⊕
        PeriodicHypercubicEvenSpatialSliceLink H →
      (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge
  | Sum.inl e => periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e
  | Sum.inr e =>
      periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
        (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e)

/-- Exact index equivalence: the full reflection-fixed edge sector is two
copies of the modern time-zero spatial-slice link carrier. -/
noncomputable def periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices
    (H : ℕ) :
    (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge ≃
      (PeriodicHypercubicEvenSpatialSliceLink H ⊕
        PeriodicHypercubicEvenSpatialSliceLink H) where
  toFun := periodicHypercubicEvenFixedEdgeToSpatialSliceSum H
  invFun := periodicHypercubicEvenSpatialSliceSumToFixedEdge H
  left_inv e := by
    classical
    by_cases hp : periodicHypercubicEvenOnPrimaryReflectionPlane H e.1.1
    · apply Subtype.ext
      simp [periodicHypercubicEvenFixedEdgeToSpatialSliceSum,
        periodicHypercubicEvenSpatialSliceSumToFixedEdge,
        periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge, hp]
    · apply Subtype.ext
      simp [periodicHypercubicEvenFixedEdgeToSpatialSliceSum,
        periodicHypercubicEvenSpatialSliceSumToFixedEdge,
        periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge, hp]
  right_inv z := by
    classical
    rcases z with e | e
    · have hp : periodicHypercubicEvenOnPrimaryReflectionPlane H e.1.1 := e.1.2
      simp [periodicHypercubicEvenSpatialSliceSumToFixedEdge,
        periodicHypercubicEvenFixedEdgeToSpatialSliceSum,
        periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge, hp]
    · let ea := periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e
      have ha : periodicHypercubicEvenOnAntipodalReflectionPlane H ea.1.1 := ea.1.2
      have hnp : ¬ periodicHypercubicEvenOnPrimaryReflectionPlane H ea.1.1 := by
        intro hp
        exact periodicHypercubicEven_primary_antipodal_disjoint H ea.1.1 hp ha
      simp [periodicHypercubicEvenSpatialSliceSumToFixedEdge,
        periodicHypercubicEvenFixedEdgeToSpatialSliceSum,
        periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge,
        ea, hnp]

/-- Measurable coordinate equivalence between the reflection-fixed boundary
configuration and an ordered pair of modern spatial-slice configurations. -/
noncomputable def periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv
    (H : ℕ)
    (Value : Type*) [MeasurableSpace Value] :
    (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Value ≃ᵐ
      ((PeriodicHypercubicEvenSpatialSliceLink H → Value) ×
        (PeriodicHypercubicEvenSpatialSliceLink H → Value)) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : PeriodicHypercubicEvenSpatialSliceLink H ⊕
        PeriodicHypercubicEvenSpatialSliceLink H => Value)
      (periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H)).trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : PeriodicHypercubicEvenSpatialSliceLink H ⊕
        PeriodicHypercubicEvenSpatialSliceLink H => Value))

/-- Reindexing the fixed boundary into the two spatial slices preserves every
finite product measure whose one-link factor is sigma-finite. -/
theorem periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving
    (H : ℕ)
    {Value : Type*} [MeasurableSpace Value]
    (μ : Measure Value) [SigmaFinite μ] :
    MeasurePreserving
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H Value)
      ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryPiMeasure μ)
      ((Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => μ)).prod
        (Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => μ))) := by
  let reindex := MeasurableEquiv.piCongrLeft
    (fun _ : PeriodicHypercubicEvenSpatialSliceLink H ⊕
      PeriodicHypercubicEvenSpatialSliceLink H => Value)
    (periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H)
  let split := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : PeriodicHypercubicEvenSpatialSliceLink H ⊕
      PeriodicHypercubicEvenSpatialSliceLink H => Value)
  have hReindex :
      MeasurePreserving reindex
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryPiMeasure μ)
        (Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceLink H ⊕
            PeriodicHypercubicEvenSpatialSliceLink H => μ)) := by
    simpa [reindex, FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure] using
      (MeasureTheory.measurePreserving_piCongrLeft
        (fun _ : PeriodicHypercubicEvenSpatialSliceLink H ⊕
          PeriodicHypercubicEvenSpatialSliceLink H => μ)
        (periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H))
  have hSplit :
      MeasurePreserving split
        (Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceLink H ⊕
            PeriodicHypercubicEvenSpatialSliceLink H => μ))
        ((Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => μ)).prod
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => μ))) := by
    simpa [split] using
      (MeasureTheory.measurePreserving_sumPiEquivProdPi
        (fun _ : PeriodicHypercubicEvenSpatialSliceLink H ⊕
          PeriodicHypercubicEvenSpatialSliceLink H => μ))
  simpa [periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv,
    reindex, split] using hReindex.trans hSplit

/-- Product normalized Haar probability on one modern primary spatial slice,
written here on the boundary-side import path so no transfer-layer instance is
needed. -/
noncomputable def periodicHypercubicEvenBoundarySpatialSliceHaarMeasure
    (H N : ℕ) :
    Measure (PeriodicHypercubicEvenSpatialSliceConfiguration H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceLink H =>
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))

/-- Product Haar probability on the ordered primary/antipodal boundary pair,
with the antipodal slice canonically reindexed by half-period translation. -/
noncomputable def periodicHypercubicEvenBoundarySpatialSlicePairHaarMeasure
    (H N : ℕ) :
    Measure
      (PeriodicHypercubicEvenSpatialSliceConfiguration H
          (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        PeriodicHypercubicEvenSpatialSliceConfiguration H
          (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  (periodicHypercubicEvenBoundarySpatialSliceHaarMeasure H N).prod
    (periodicHypercubicEvenBoundarySpatialSliceHaarMeasure H N)

/-- The actual Wilson shared-boundary Haar measure is exactly product Haar on
two modern spatial slices after the canonical two-slice reindexing. -/
theorem periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_haar
    (H N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
        (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (periodicHypercubicEvenBoundaryHaarMeasure H N)
      (periodicHypercubicEvenBoundarySpatialSlicePairHaarMeasure H N) := by
  simpa [periodicHypercubicEvenBoundaryHaarMeasure,
    periodicHypercubicEvenBoundarySpatialSlicePairHaarMeasure,
    periodicHypercubicEvenBoundarySpatialSliceHaarMeasure] using
    (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving
      H (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))

end

end MathlibAnalytic
end MGAP4D
