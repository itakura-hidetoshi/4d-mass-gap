import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberOffTargetHarnack
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabSourceLikelihoodRatioFactorization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Two intrinsic spatial links share a local Wilson plaquette when one
intrinsic spatial plaquette touches both links. -/
def periodicHypercubicEvenSpatialSliceLinksSharePlaquette
    (H : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : Prop :=
  ∃ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
    periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p target ∧
      periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p source

/-- Updating a remote base link leaves the purely spatial half-update factor at
`target` unchanged when the two links share no spatial plaquette.  This is the
exact local-support statement behind cancellation of the raw slab factor after
one-link normalization. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor_update_remote
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (u g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hDistinct : fiber ≠ target)
    (hNoShare : ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target fiber) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
        H N beta (Function.update B fiber u) target g =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
        H N beta B target g := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hTouchesTarget :
      periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p target :=
    (periodicHypercubicEvenSpatialSlice_mem_touchingPlaquettes_iff H target p).mp hp
  have hNotTouchesFiber :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p fiber := by
    intro hTouchesFiber
    exact hNoShare ⟨p, hTouchesTarget, hTouchesFiber⟩
  have hBase :
      periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
          (Function.update B fiber u) p =
        periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p := by
    simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
      periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_continuousVacuumReplaceLink_eq_of_not_touches
        H N B fiber u p hNotTouchesFiber
  have hCfg :
      Function.update (Function.update B fiber u) target g =
        Function.update (Function.update B target g) fiber u := by
    funext e
    by_cases hTarget : e = target
    · subst e
      simp [hDistinct]
    · by_cases hFiber : e = fiber
      · subst e
        simp [hDistinct, Ne.symm hDistinct]
      · simp [hTarget, hFiber]
  have hUpdated :
      periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
          (Function.update (Function.update B fiber u) target g) p =
        periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
          (Function.update B target g) p := by
    rw [hCfg]
    simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
      periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_continuousVacuumReplaceLink_eq_of_not_touches
        H N (Function.update B target g) fiber u p hNotTouchesFiber
  rw [hUpdated, hBase]

/-- Under the same noninteraction hypothesis, the complete exact local factor
for a right-boundary update at `target` is independent of a remote base-link
value at `fiber`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_rightBase_remote
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (u g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hDistinct : fiber ≠ target)
    (hNoShare : ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target fiber) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A (Function.update B fiber u) target g =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target g := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
  have hAt : (Function.update B fiber u) target = B target := by
    simp [hDistinct]
  rw [hAt]
  congr 1
  congr 1
  apply congrArg (fun x : ℝ => (1 / 2 : ℝ) * x)
  apply Finset.sum_congr rfl
  intro p hp
  have hTouchesTarget :
      periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p target :=
    (periodicHypercubicEvenSpatialSlice_mem_touchingPlaquettes_iff H target p).mp hp
  have hNotTouchesFiber :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p fiber := by
    intro hTouchesFiber
    exact hNoShare ⟨p, hTouchesTarget, hTouchesFiber⟩
  have hBase :
      periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
          (Function.update B fiber u) p =
        periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p := by
    simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
      periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_continuousVacuumReplaceLink_eq_of_not_touches
        H N B fiber u p hNotTouchesFiber
  have hCfg :
      Function.update (Function.update B fiber u) target g =
        Function.update (Function.update B target g) fiber u := by
    funext e
    by_cases hTarget : e = target
    · subst e
      simp [hDistinct]
    · by_cases hFiber : e = fiber
      · subst e
        simp [hDistinct, Ne.symm hDistinct]
      · simp [hTarget, hFiber]
  have hUpdated :
      periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
          (Function.update (Function.update B fiber u) target g) p =
        periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
          (Function.update B target g) p := by
    rw [hCfg]
    simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
      periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_continuousVacuumReplaceLink_eq_of_not_touches
        H N (Function.update B target g) fiber u p hNotTouchesFiber
  rw [hUpdated, hBase]

/-- Division-free form of remote slab cancellation.  If `fiber` and
`backgroundFiber` share no spatial plaquette, then changing the background
value has a slab likelihood ratio independent of the value inserted at
`fiber`.  Equivalently, the four slab weights have vanishing cross-ratio defect.

This theorem is purely about the raw symmetric one-slab kernel; it makes no
locality claim about the canonical continuous vacuum factor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_remote_background_crossRatio_eq
    (H N : ℕ)
    (beta : ℝ)
    (Br A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (fiber backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (u v g h : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hDistinct : fiber ≠ backgroundFiber)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H backgroundFiber fiber) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br
          (Function.update (Function.update A fiber u) backgroundFiber g) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br
          (Function.update (Function.update A fiber v) backgroundFiber h) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br
          (Function.update (Function.update A fiber u) backgroundFiber h) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br
          (Function.update (Function.update A fiber v) backgroundFiber g) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul]
  have hUg :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_rightBase_remote
      H N beta Br A backgroundFiber fiber u g hDistinct hNoShare
  have hUh :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_rightBase_remote
      H N beta Br A backgroundFiber fiber u h hDistinct hNoShare
  have hVg :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_rightBase_remote
      H N beta Br A backgroundFiber fiber v g hDistinct hNoShare
  have hVh :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_rightBase_remote
      H N beta Br A backgroundFiber fiber v h hDistinct hNoShare
  rw [hUg, hUh, hVg, hVh]
  ring

end

end MathlibAnalytic
end MGAP4D