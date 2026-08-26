import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSlice
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEdgeSideClassification
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedCoordinates
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Vertices on the antipodal reflection-fixed spatial slice. -/
abbrev PeriodicHypercubicEvenAntipodalSpatialSliceVertex (H : ℕ) : Type :=
  {v : PeriodicHypercubicEvenVertex H //
    periodicHypercubicEvenOnAntipodalReflectionPlane H v}

/-- Spatial links based on the antipodal reflection-fixed slice. -/
abbrev PeriodicHypercubicEvenAntipodalSpatialSliceLink (H : ℕ) : Type :=
  PeriodicHypercubicEvenAntipodalSpatialSliceVertex H ×
    PeriodicHypercubicEvenSpatialDirection

/-- Gauge-valued configurations on the antipodal spatial slice. -/
abbrev PeriodicHypercubicEvenAntipodalSpatialSliceConfiguration
    (H : ℕ) (Value : Type) : Type :=
  PeriodicHypercubicEvenAntipodalSpatialSliceLink H → Value

/-- The two site-reflection planes are disjoint. -/
theorem periodicHypercubicEven_primary_not_antipodal
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H)
    (hprimary : periodicHypercubicEvenOnPrimaryReflectionPlane H v) :
    ¬ periodicHypercubicEvenOnAntipodalReflectionPlane H v := by
  intro hantipodal
  unfold periodicHypercubicEvenOnPrimaryReflectionPlane at hprimary
  unfold periodicHypercubicEvenOnAntipodalReflectionPlane at hantipodal
  have hlt : H + 1 < PeriodicHypercubicEvenSideLength H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  have hval :
      (((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))).val = H + 1 :=
    ZMod.val_natCast_of_lt hlt
  have heq :
      (0 : ZMod (PeriodicHypercubicEvenSideLength H)) =
        ((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) := by
    calc
      (0 : ZMod (PeriodicHypercubicEvenSideLength H)) = v 0 := hprimary.symm
      _ = ((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) := hantipodal
  have hvalEq := congrArg ZMod.val heq
  simp [hval] at hvalEq

/-- A physical positive link belongs to the reflection-fixed edge sector iff it
is spatial and based on one of the two reflection-fixed time slices. -/
theorem periodicHypercubicEvenEdgeSide_eq_fixed_iff_spatial_fixedPlane
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.fixed ↔
      e.2 ≠ 0 ∧
        (periodicHypercubicEvenOnPrimaryReflectionPlane H e.1 ∨
          periodicHypercubicEvenOnAntipodalReflectionPlane H e.1) := by
  constructor
  · intro hfixed
    have hspace : e.2 ≠ 0 := by
      intro htime
      have hedge : e = (e.1, 0) := by
        apply Prod.ext
        · rfl
        · exact htime
      rw [hedge] at hfixed
      by_cases hle : (e.1 0).val ≤ H
      · have hside :=
          periodicHypercubicEvenEdgeSide_time_eq_positive_of_val_le H e.1 hle
        rw [hside] at hfixed
        cases hfixed
      · have hhalf : H + 1 ≤ (e.1 0).val := by omega
        have hside :=
          periodicHypercubicEvenEdgeSide_time_eq_negative_of_half_le_val H e.1 hhalf
        rw [hside] at hfixed
        cases hfixed
    refine ⟨hspace, ?_⟩
    by_cases hzero : (e.1 0).val = 0
    · left
      unfold periodicHypercubicEvenOnPrimaryReflectionPlane
      exact (ZMod.val_eq_zero _).mp hzero
    · by_cases hhalf : (e.1 0).val = H + 1
      · right
        unfold periodicHypercubicEvenOnAntipodalReflectionPlane
        rw [← ZMod.natCast_zmod_val (e.1 0)]
        exact congrArg
          (fun n : ℕ => (n : ZMod (PeriodicHypercubicEvenSideLength H))) hhalf
      · by_cases hle : (e.1 0).val ≤ H
        · have hpos : 1 ≤ (e.1 0).val := Nat.one_le_iff_ne_zero.2 hzero
          have hside :=
            periodicHypercubicEvenEdgeSide_spatial_eq_positive_of_val
              H e hspace hpos hle
          rw [hside] at hfixed
          cases hfixed
        · have hneg : H + 1 < (e.1 0).val := by omega
          have hside :=
            periodicHypercubicEvenEdgeSide_spatial_eq_negative_of_half_lt_val
              H e hspace hneg
          rw [hside] at hfixed
          cases hfixed
  · rintro ⟨hspace, hprimary | hantipodal⟩
    · unfold periodicHypercubicEvenOnPrimaryReflectionPlane at hprimary
      have hzero : (e.1 0).val = 0 := by simp [hprimary]
      exact periodicHypercubicEvenEdgeSide_spatial_eq_fixed_of_val_eq_zero
        H e hspace hzero
    · unfold periodicHypercubicEvenOnAntipodalReflectionPlane at hantipodal
      have hlt : H + 1 < PeriodicHypercubicEvenSideLength H := by
        simp only [PeriodicHypercubicEvenSideLength]
        omega
      have hhalf : (e.1 0).val = H + 1 := by
        rw [hantipodal, ZMod.val_natCast_of_lt hlt]
      exact periodicHypercubicEvenEdgeSide_spatial_eq_fixed_of_val_eq_half
        H e hspace hhalf

/-- The OS reflection-fixed edge carrier is exactly the disjoint union of the
primary and antipodal spatial-link carriers. -/
noncomputable def periodicHypercubicEvenOSFixedEdgeEquivTwoSpatialSlices
    (H : ℕ) :
    (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge ≃
      (PeriodicHypercubicEvenSpatialSliceLink H ⊕
        PeriodicHypercubicEvenAntipodalSpatialSliceLink H) where
  toFun e := by
    have hclass :=
      (periodicHypercubicEvenEdgeSide_eq_fixed_iff_spatial_fixedPlane H e.1).1 e.2
    by_cases hp : periodicHypercubicEvenOnPrimaryReflectionPlane H e.1.1
    · exact Sum.inl (⟨e.1.1, hp⟩, ⟨e.1.2, hclass.1⟩)
    · exact Sum.inr
        (⟨e.1.1, hclass.2.resolve_left hp⟩, ⟨e.1.2, hclass.1⟩)
  invFun s := by
    cases s with
    | inl e =>
        exact ⟨(e.1.1, e.2.1),
          (periodicHypercubicEvenEdgeSide_eq_fixed_iff_spatial_fixedPlane
            H (e.1.1, e.2.1)).2 ⟨e.2.2, Or.inl e.1.2⟩⟩
    | inr e =>
        exact ⟨(e.1.1, e.2.1),
          (periodicHypercubicEvenEdgeSide_eq_fixed_iff_spatial_fixedPlane
            H (e.1.1, e.2.1)).2 ⟨e.2.2, Or.inr e.1.2⟩⟩
  left_inv e := by
    apply Subtype.ext
    have hclass :=
      (periodicHypercubicEvenEdgeSide_eq_fixed_iff_spatial_fixedPlane H e.1).1 e.2
    by_cases hp : periodicHypercubicEvenOnPrimaryReflectionPlane H e.1.1
    · simp [hp]
    · simp [hp, hclass.2.resolve_left hp]
  right_inv s := by
    cases s with
    | inl e =>
        have hp : periodicHypercubicEvenOnPrimaryReflectionPlane H e.1.1 := e.1.2
        simp [hp]
    | inr e =>
        have ha : periodicHypercubicEvenOnAntipodalReflectionPlane H e.1.1 := e.1.2
        have hp : ¬ periodicHypercubicEvenOnPrimaryReflectionPlane H e.1.1 := by
          intro hprimary
          exact periodicHypercubicEven_primary_not_antipodal H e.1.1 hprimary ha
        simp [hp, ha]

/-- Boundary data on all reflection-fixed physical links are exactly a pair of
boundary configurations, one on each fixed spatial slice. -/
noncomputable def periodicHypercubicEvenOSBoundaryConfigurationEquivTwoSpatialSlices
    (H : ℕ) (Value : Type) :
    (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Value ≃
      (PeriodicHypercubicEvenSpatialSliceConfiguration H Value ×
        PeriodicHypercubicEvenAntipodalSpatialSliceConfiguration H Value) where
  toFun b :=
    (fun e => b ((periodicHypercubicEvenOSFixedEdgeEquivTwoSpatialSlices H).symm
      (Sum.inl e)),
     fun e => b ((periodicHypercubicEvenOSFixedEdgeEquivTwoSpatialSlices H).symm
      (Sum.inr e)))
  invFun p := fun e =>
    match periodicHypercubicEvenOSFixedEdgeEquivTwoSpatialSlices H e with
    | Sum.inl a => p.1 a
    | Sum.inr a => p.2 a
  left_inv b := by
    funext e
    let E := periodicHypercubicEvenOSFixedEdgeEquivTwoSpatialSlices H
    generalize hE : E e = s
    cases s with
    | inl a =>
        change b (E.symm (Sum.inl a)) = b e
        have hback : E.symm (Sum.inl a) = e := by
          rw [← hE]
          exact E.symm_apply_apply e
        rw [hback]
    | inr a =>
        change b (E.symm (Sum.inr a)) = b e
        have hback : E.symm (Sum.inr a) = e := by
          rw [← hE]
          exact E.symm_apply_apply e
        rw [hback]
  right_inv p := by
    apply Prod.ext
    · funext e
      change
        (match periodicHypercubicEvenOSFixedEdgeEquivTwoSpatialSlices H
            ((periodicHypercubicEvenOSFixedEdgeEquivTwoSpatialSlices H).symm
              (Sum.inl e)) with
          | Sum.inl a => p.1 a
          | Sum.inr a => p.2 a) = p.1 e
      rw [(periodicHypercubicEvenOSFixedEdgeEquivTwoSpatialSlices H).apply_symm_apply]
    · funext e
      change
        (match periodicHypercubicEvenOSFixedEdgeEquivTwoSpatialSlices H
            ((periodicHypercubicEvenOSFixedEdgeEquivTwoSpatialSlices H).symm
              (Sum.inr e)) with
          | Sum.inl a => p.1 a
          | Sum.inr a => p.2 a) = p.2 e
      rw [(periodicHypercubicEvenOSFixedEdgeEquivTwoSpatialSlices H).apply_symm_apply]

/-- Audit-visible geometry package for the genuine even-periodic OS boundary. -/
structure PeriodicHypercubicEvenOSBoundaryTwoSliceGeometryPackage
    (H : ℕ) : Prop where
  fixedEdgeClassification :
    ∀ e : PeriodicHypercubicEvenEdge H,
      periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.fixed ↔
        e.2 ≠ 0 ∧
          (periodicHypercubicEvenOnPrimaryReflectionPlane H e.1 ∨
            periodicHypercubicEvenOnAntipodalReflectionPlane H e.1)
  primaryAntipodalDisjoint :
    ∀ v : PeriodicHypercubicEvenVertex H,
      periodicHypercubicEvenOnPrimaryReflectionPlane H v →
        ¬ periodicHypercubicEvenOnAntipodalReflectionPlane H v

/-- Construct the exact two-slice OS-boundary geometry package. -/
theorem periodicHypercubicEvenOSBoundaryTwoSliceGeometryPackage
    (H : ℕ) : PeriodicHypercubicEvenOSBoundaryTwoSliceGeometryPackage H :=
  { fixedEdgeClassification :=
      periodicHypercubicEvenEdgeSide_eq_fixed_iff_spatial_fixedPlane H
    primaryAntipodalDisjoint :=
      periodicHypercubicEven_primary_not_antipodal H }

end

end MathlibAnalytic
end MGAP4D
