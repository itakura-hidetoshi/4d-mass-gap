import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixColorBoundaryDependence
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance groundStateSixRetainedStrongBoundaryMeasurabilityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- If one and the same real representative is strongly measurable for all six
right-update retained sigma-algebras, then it is strongly measurable with respect
to the complete left-boundary sigma-algebra.  This is a pointwise-representative
statement; it does not identify six separate a.e. modifications. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJoint_stronglyMeasurable_fst_of_rightSix
    (H N : ℕ)
    (f :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (h : ∀ c : Fin 6,
      StronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)] f) :
    StronglyMeasurable[
      MeasurableSpace.comap Prod.fst
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))] f := by
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  have hfac : ∀ c : Fin 6,
      Function.FactorsThrough f
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction
          H N c) := by
    intro c
    have hc := h c
    rw [periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_eq_comap_rightRetainedCoordinateRestriction]
      at hc
    exact hc.factorsThrough
  have hfst : Function.FactorsThrough f Prod.fst :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJoint_factorsThrough_fst_of_rightSix
      H N f hfac
  have h0 := h (0 : Fin 6)
  rw [periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_eq_comap_rightRetainedPairData]
    at h0
  obtain ⟨φ, hφ, hfφ⟩ := h0.exists_eq_measurable_comp
  let y0 : X := fun _ => 1
  let section : X → X × X := fun x => (x, y0)
  have hsection : Measurable section := by
    exact measurable_id.prodMk measurable_const
  have hpair :
      Measurable
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairData
          H N (0 : Fin 6) ∘ section) :=
    (measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairData
      H N (0 : Fin 6)).comp hsection
  let k : X → ℝ := fun x =>
    φ (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairData
      H N (0 : Fin 6) (section x))
  have hk : StronglyMeasurable k := by
    exact hφ.comp_measurable hpair
  have hfk : f = k ∘ Prod.fst := by
    funext z
    calc
      f z = f (section z.1) := hfst rfl
      _ = φ (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairData
            H N (0 : Fin 6) (section z.1)) := congrFun hfφ (section z.1)
      _ = (k ∘ Prod.fst) z := rfl
  rw [hfk]
  exact hk.comp_measurable (measurable_iff_comap_le.mpr le_rfl)

/-- Left/right symmetric counterpart: a common representative strongly measurable
for all six left-update retained sigma-algebras is strongly measurable with respect
to the complete right-boundary sigma-algebra. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJoint_stronglyMeasurable_snd_of_leftSix
    (H N : ℕ)
    (f :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (h : ∀ c : Fin 6,
      StronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)] f) :
    StronglyMeasurable[
      MeasurableSpace.comap Prod.snd
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))] f := by
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  have hfac : ∀ c : Fin 6,
      Function.FactorsThrough f
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateRestriction
          H N c) := by
    intro c
    have hc := h c
    rw [periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_eq_comap_leftRetainedCoordinateRestriction]
      at hc
    exact hc.factorsThrough
  have hsnd : Function.FactorsThrough f Prod.snd :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJoint_factorsThrough_snd_of_leftSix
      H N f hfac
  have h0 := h (0 : Fin 6)
  rw [periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_eq_comap_leftRetainedPairData]
    at h0
  obtain ⟨φ, hφ, hfφ⟩ := h0.exists_eq_measurable_comp
  let x0 : X := fun _ => 1
  let section : X → X × X := fun y => (x0, y)
  have hsection : Measurable section := by
    exact measurable_const.prodMk measurable_id
  have hpair :
      Measurable
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairData
          H N (0 : Fin 6) ∘ section) :=
    (measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairData
      H N (0 : Fin 6)).comp hsection
  let k : X → ℝ := fun y =>
    φ (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairData
      H N (0 : Fin 6) (section y))
  have hk : StronglyMeasurable k := by
    exact hφ.comp_measurable hpair
  have hfk : f = k ∘ Prod.snd := by
    funext z
    calc
      f z = f (section z.2) := hsnd rfl
      _ = φ (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairData
            H N (0 : Fin 6) (section z.2)) := congrFun hfφ (section z.2)
      _ = (k ∘ Prod.snd) z := rfl
  rw [hfk]
  exact hk.comp_measurable (measurable_iff_comap_le.mpr le_rfl)

end

end MathlibAnalytic
end MGAP4D
