import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointAllRightRelativePoincare
import MGAP4D.MathlibAnalytic.RealHilbertGroupedProjectionSweep

/-!
# A complete right-link sweep grouped by the six canonical spatial colors

Each internal list is exactly the existing fixed-color subtype enumeration,
then mapped into the ambient link type. The outer list contains the six colors
once. Distinct groups are disjoint by their literal color labels.
No commutativity or change of order is used in the operator identity.
-/

namespace MGAP4D.MathlibAnalytic

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype

namespace GroundStateSourceFixedPairEnergy

/-- The existing canonical fixed-color list, with its literal ambient labels. -/
def sixSpatialColorLinkList (H : ℕ) (c : Fin 6) : List (PeriodicHypercubicEvenSpatialSliceLink H) :=
  ((Finset.univ : Finset (PeriodicHypercubicEvenFixedSpatialColorLink H
    (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c))).toList).map Subtype.val

@[simp] theorem mem_sixSpatialColorLinkList (H : ℕ) (c : Fin 6)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    e ∈ sixSpatialColorLinkList H c ↔
      periodicHypercubicEvenSpatialSliceLinkColor H e =
        periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c := by
  classical
  simp only [sixSpatialColorLinkList, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro h
    exact ⟨⟨e, h⟩, rfl⟩

/-- The six groups concatenate to one actual all-right-link source list. -/
def sixSpatialGroupedLinkList (H : ℕ) : List (PeriodicHypercubicEvenSpatialSliceLink H) :=
  (Finset.univ : Finset (Fin 6)).toList.flatMap (sixSpatialColorLinkList H)

theorem sixSpatialGroupedLinkList_nodup (H : ℕ) :
    (sixSpatialGroupedLinkList H).Nodup := by
  classical
  unfold sixSpatialGroupedLinkList
  rw [List.nodup_flatMap]
  constructor
  · intro c _
    exact (Finset.nodup_toList _).map Subtype.val_injective
  · apply (Finset.nodup_toList (Finset.univ : Finset (Fin 6))).imp
    intro c d hcd
    apply List.disjoint_left.mpr
    intro e hec hed
    have hc := (mem_sixSpatialColorLinkList H c e).mp hec
    have hd := (mem_sixSpatialColorLinkList H d e).mp hed
    exact hcd (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm.injective
      (hc.symm.trans hd))

theorem sixSpatialGroupedLinkList_complete (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : e ∈ sixSpatialGroupedLinkList H := by
  classical
  apply List.mem_flatMap.mpr
  refine ⟨periodicHypercubicEvenGroundStateSpatialColorEquivFin
    (periodicHypercubicEvenSpatialSliceLinkColor H e), by simp, ?_⟩
  rw [mem_sixSpatialColorLinkList]
  simp

/-- Each group operator is exactly the previously defined same-color sweep. -/
theorem sixSpatialColorLinkList_sweep_eq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (c : Fin 6)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta) :
    realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta) (sixSpatialColorLinkList H c) f =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
        H N hN beta hbeta (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f := by
  unfold sixSpatialColorLinkList
  rw [GroupedProjectionSweep.map_apply]
  rfl

end GroundStateSourceFixedPairEnergy
end
end MGAP4D.MathlibAnalytic
