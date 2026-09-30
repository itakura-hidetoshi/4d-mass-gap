import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedCompleteOrderLossContraction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialGroupedLinkSweep
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwoSidedTwelveSpatialConditionalExpectation
import MGAP4D.MathlibAnalytic.RealHilbertGroupedProjectionSweep
import Mathlib.Tactic

/-!
# The genuine two-sided spatial links grouped by the twelve canonical colors

This is the finite-color carrier required by G1.

The tagged one-link carrier is
`Sum rightLink leftLink`, while the twelve-color carrier is
`Sum (Fin 6) (Fin 6)`.  Each color group is the existing canonical
same-color link list, tagged by its boundary orientation.  Flattening all
twelve groups therefore visits every genuine tagged spatial link exactly once.

No operator commutativity or reordering theorem is used here.  The resulting
grouped list is a concrete complete duplicate-free order, so the order-robust
two-sided loss contraction can be applied to this exact order.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance twoSidedTwelveSpatialGroupedLinkSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStateSourceFixedPairEnergy

/-- Canonical twelve-color label of a tagged two-sided spatial link. -/
def twoSidedTwelveSpatialLinkColor
    (H : ℕ) :
    PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H →
      PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor
  | Sum.inl e =>
      Sum.inl
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin
          (periodicHypercubicEvenSpatialSliceLinkColor H e))
  | Sum.inr e =>
      Sum.inr
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin
          (periodicHypercubicEvenSpatialSliceLinkColor H e))

/-- One canonical tagged-link list for each of the twelve spatial colors. -/
def twoSidedTwelveSpatialColorLinkList
    (H : ℕ) :
    PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor →
      List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)
  | Sum.inl c =>
      (sixSpatialColorLinkList H c).map (fun e => Sum.inl e)
  | Sum.inr c =>
      (sixSpatialColorLinkList H c).map (fun e => Sum.inr e)

/-- Membership in a tagged color group is exactly equality of its canonical
orientation-and-color label. -/
@[simp] theorem mem_twoSidedTwelveSpatialColorLinkList
    (H : ℕ)
    (c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor)
    (e : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H) :
    e ∈ twoSidedTwelveSpatialColorLinkList H c ↔
      twoSidedTwelveSpatialLinkColor H e = c := by
  cases c with
  | inl c =>
      cases e with
      | inl e =>
          simp [
            twoSidedTwelveSpatialColorLinkList,
            twoSidedTwelveSpatialLinkColor,
            mem_sixSpatialColorLinkList]
      | inr e =>
          simp [
            twoSidedTwelveSpatialColorLinkList,
            twoSidedTwelveSpatialLinkColor]
  | inr c =>
      cases e with
      | inl e =>
          simp [
            twoSidedTwelveSpatialColorLinkList,
            twoSidedTwelveSpatialLinkColor]
      | inr e =>
          simp [
            twoSidedTwelveSpatialColorLinkList,
            twoSidedTwelveSpatialLinkColor,
            mem_sixSpatialColorLinkList]

/-- The pre-existing same-color right-link list has no duplicates. -/
theorem sixSpatialColorLinkList_nodup
    (H : ℕ) (c : Fin 6) :
    (sixSpatialColorLinkList H c).Nodup := by
  unfold sixSpatialColorLinkList
  exact (Finset.nodup_toList _).map Subtype.val_injective

/-- Every tagged twelve-color group is duplicate-free. -/
theorem twoSidedTwelveSpatialColorLinkList_nodup
    (H : ℕ)
    (c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor) :
    (twoSidedTwelveSpatialColorLinkList H c).Nodup := by
  cases c with
  | inl c =>
      unfold twoSidedTwelveSpatialColorLinkList
      exact (sixSpatialColorLinkList_nodup H c).map (by
        intro a b h
        exact Sum.inl.inj h)
  | inr c =>
      unfold twoSidedTwelveSpatialColorLinkList
      exact (sixSpatialColorLinkList_nodup H c).map (by
        intro a b h
        exact Sum.inr.inj h)

/-- Concatenate the twelve canonical tagged-link color groups. -/
def twoSidedTwelveSpatialGroupedLinkList
    (H : ℕ) :
    List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H) :=
  (Finset.univ :
    Finset PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor).toList.flatMap
      (twoSidedTwelveSpatialColorLinkList H)

/-- The twelve grouped lists are pairwise disjoint, hence their flattening is
duplicate-free. -/
theorem twoSidedTwelveSpatialGroupedLinkList_nodup
    (H : ℕ) :
    (twoSidedTwelveSpatialGroupedLinkList H).Nodup := by
  classical
  unfold twoSidedTwelveSpatialGroupedLinkList
  rw [List.nodup_flatMap]
  constructor
  · intro c _
    exact twoSidedTwelveSpatialColorLinkList_nodup H c
  · apply
      (Finset.nodup_toList
        (Finset.univ :
          Finset PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor)).imp
    intro c d hcd
    apply List.disjoint_left.mpr
    intro e hec hed
    have hc :=
      (mem_twoSidedTwelveSpatialColorLinkList H c e).mp hec
    have hd :=
      (mem_twoSidedTwelveSpatialColorLinkList H d e).mp hed
    exact hcd (hc.symm.trans hd)

/-- Every tagged right/left spatial link occurs in the twelve-color grouped
list. -/
theorem twoSidedTwelveSpatialGroupedLinkList_complete
    (H : ℕ)
    (e : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H) :
    e ∈ twoSidedTwelveSpatialGroupedLinkList H := by
  classical
  unfold twoSidedTwelveSpatialGroupedLinkList
  apply List.mem_flatMap.mpr
  refine ⟨twoSidedTwelveSpatialLinkColor H e, by simp, ?_⟩
  exact
    (mem_twoSidedTwelveSpatialColorLinkList
      H (twoSidedTwelveSpatialLinkColor H e) e).2 rfl

/-- A right-oriented tagged color group is exactly the existing right
same-color one-link sweep. -/
theorem twoSidedTwelveSpatialColorLinkList_right_sweep_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (c : Fin 6)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
          H N hN beta hbeta)
        (twoSidedTwelveSpatialColorLinkList H (Sum.inl c)) f =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
        H N hN beta hbeta
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f := by
  unfold twoSidedTwelveSpatialColorLinkList
  rw [GroupedProjectionSweep.map_apply]
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2] using
    sixSpatialColorLinkList_sweep_eq H N hN beta hbeta c f

/-- A left-oriented tagged color group is literally the sweep of the genuine
left one-link projections over the same canonical underlying link list. -/
theorem twoSidedTwelveSpatialColorLinkList_left_sweep_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (c : Fin 6)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
          H N hN beta hbeta)
        (twoSidedTwelveSpatialColorLinkList H (Sum.inr c)) f =
      realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H N hN beta hbeta)
        (sixSpatialColorLinkList H c) f := by
  unfold twoSidedTwelveSpatialColorLinkList
  rw [GroupedProjectionSweep.map_apply]
  rfl

/-- Flattening the twelve groups is exactly a sweep by the twelve whole-group
operators in the same outer order. -/
theorem twoSidedTwelveSpatialGroupedLinkList_sweep_eq_groupSweep
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
          H N hN beta hbeta)
        (twoSidedTwelveSpatialGroupedLinkList H) f =
      realHilbertProjectionSweep
        (fun c =>
          realHilbertProjectionSweep
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
              H N hN beta hbeta)
            (twoSidedTwelveSpatialColorLinkList H c))
        ((Finset.univ :
          Finset PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor).toList)
        f := by
  unfold twoSidedTwelveSpatialGroupedLinkList
  exact
    GroupedProjectionSweep.flatMap_apply
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta)
      (twoSidedTwelveSpatialColorLinkList H)
      ((Finset.univ :
        Finset PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor).toList)
      f

end GroundStateSourceFixedPairEnergy

end

end MathlibAnalytic
end MGAP4D
