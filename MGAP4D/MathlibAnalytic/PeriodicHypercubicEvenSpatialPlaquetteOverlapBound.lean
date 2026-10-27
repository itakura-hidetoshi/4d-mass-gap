import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumLocalHarnack
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCountControlledLocalPhysicalGICoercivityV5_LQ
import Mathlib.Tactic

/-!
# Actual spatial plaquette overlap bounds

Use the four ORIGINAL oriented boundary links. The existing all-volume
six-touching-plaquettes bound yields at most 24 plaquettes sharing a link
with a given spatial plaquette. The sharper geometric 16 is not used.
An explicit original coordinate family proves that the genuine plaquette
count grows at least as 2(H+1). No synthetic lattice or Dobrushin argument.
-/

namespace MGAP4D.MathlibAnalytic
open scoped BigOperators
noncomputable section
set_option autoImplicit false

private noncomputable instance pz37zaSpatialPlaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) := Fintype.ofFinite _
private noncomputable instance pz37zaSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

/-- The four intrinsic links used by the original spatial holonomy. -/
def pz37zaSpatialPlaquetteBoundary (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    Fin 4 → PeriodicHypercubicEvenSpatialSliceLink H :=
  ![(p.1, p.2.1.1),
    (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.1, p.2.1.2),
    (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.2, p.2.1.1),
    (p.1, p.2.1.2)]

/-- Actual finite four-link support; repeated links, if any, are not counted twice. -/
noncomputable def pz37zaSpatialPlaquetteSupport (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact Finset.univ.image (pz37zaSpatialPlaquetteBoundary H p)

theorem pz37zaSpatialPlaquetteSupport_card_le_four (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    (pz37zaSpatialPlaquetteSupport H p).card ≤ 4 := by
  classical
  exact (Finset.card_image_le).trans (by simp)

theorem pz37zaSpatialPlaquetteSupport_mem_touches (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (he : e ∈ pz37zaSpatialPlaquetteSupport H p) :
    periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p e := by
  classical
  obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp he
  fin_cases k
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

/-- Every potential nonzero covariance lies in this actual finite family. -/
noncomputable def pz37zaSpatialPlaquetteOverlap (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    Finset (PeriodicHypercubicEvenSpatialSlicePlaquette H) := by
  classical
  exact (pz37zaSpatialPlaquetteSupport H p).biUnion
    (periodicHypercubicEvenSpatialSliceTouchingPlaquettes H)

theorem pz37zaSpatialPlaquetteOverlap_card_le_twentyFour (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    (pz37zaSpatialPlaquetteOverlap H p).card ≤ 24 := by
  classical
  calc
    (pz37zaSpatialPlaquetteOverlap H p).card ≤
        ∑ e ∈ pz37zaSpatialPlaquetteSupport H p,
          (periodicHypercubicEvenSpatialSliceTouchingPlaquettes H e).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ pz37zaSpatialPlaquetteSupport H p, 6 :=
      Finset.sum_le_sum (fun e _ =>
        periodicHypercubicEvenSpatialSliceTouchingPlaquettes_card_le_six H e)
    _ = (pz37zaSpatialPlaquetteSupport H p).card * 6 := by simp
    _ ≤ 24 := by
      have h := pz37zaSpatialPlaquetteSupport_card_le_four H p
      omega

theorem pz37zaSpatialPlaquetteSupport_disjoint_of_not_overlap (H : ℕ)
    (p q : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (hq : q ∉ pz37zaSpatialPlaquetteOverlap H p) :
    Disjoint (pz37zaSpatialPlaquetteSupport H p) (pz37zaSpatialPlaquetteSupport H q) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e hep heq
  apply hq
  apply Finset.mem_biUnion.mpr
  refine ⟨e, hep, ?_⟩
  exact (periodicHypercubicEvenSpatialSlice_mem_touchingPlaquettes_iff H e q).mpr
    (pz37zaSpatialPlaquetteSupport_mem_touches H q e heq)

/-- A genuine family of parallel plaquettes at time zero indexed by one
original periodic coordinate; used only to show unbounded true count. -/
def pz37zaSpatialPlaquetteCoordinateFamily (H : ℕ)
    (x : ZMod (PeriodicHypercubicEvenSideLength H)) :
    PeriodicHypercubicEvenSpatialSlicePlaquette H :=
  (⟨![0, x, 0, 0], by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
    ⟨(⟨1, by decide⟩, ⟨2, by decide⟩), by decide⟩)

theorem pz37zaSpatialPlaquetteCoordinateFamily_injective (H : ℕ) :
    Function.Injective (pz37zaSpatialPlaquetteCoordinateFamily H) := by
  intro x y hxy
  have h := congrArg (fun p : PeriodicHypercubicEvenSpatialSlicePlaquette H => p.1.1 1) hxy
  simpa [pz37zaSpatialPlaquetteCoordinateFamily] using h

/-- Growth of the actual original Wilson plaquette number, not an assumed volume proxy. -/
theorem pz37zaOriginalSpatialPlaquetteCount_ge_sideLength (H : ℕ) :
    2 * (H + 1) ≤ GroundStatePosteriorJoint.p4Q2LP_originalSpatialPlaquetteCount H := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    simp [PeriodicHypercubicEvenSideLength]⟩
  rw [GroundStatePosteriorJoint.p4Q2LQ_originalSpatialPlaquetteCount_eq_card]
  have h := Fintype.card_le_of_injective _ (pz37zaSpatialPlaquetteCoordinateFamily_injective H)
  simpa only [ZMod.card, PeriodicHypercubicEvenSideLength] using h

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.pz37zaSpatialPlaquetteOverlap_card_le_twentyFour
#print axioms MGAP4D.MathlibAnalytic.pz37zaSpatialPlaquetteSupport_disjoint_of_not_overlap
#print axioms MGAP4D.MathlibAnalytic.pz37zaOriginalSpatialPlaquetteCount_ge_sideLength
