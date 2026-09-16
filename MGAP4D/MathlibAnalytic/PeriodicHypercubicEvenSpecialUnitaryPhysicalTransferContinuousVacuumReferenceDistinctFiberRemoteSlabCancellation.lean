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

/-- The exact spatial half-action increment at `target` is unchanged when the
base configuration is modified at a distinct link that shares no spatial
plaquette with `target`.  Keeping the finite sum explicit avoids asking the
elaborator to normalize the full exponential definition at once. -/
private theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialIncrementSum_update_remote
    (H N : ℕ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (u g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hDistinct : fiber ≠ target)
    (hNoShare : ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target fiber) :
    (∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
      (specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update (Function.update B fiber u) target g) p) -
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update B fiber u) p))) =
      ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
        (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
              (Function.update B target g) p) -
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p)) := by
  classical
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
      simp [Ne.symm hDistinct]
    · by_cases hFiber : e = fiber
      · subst e
        simp [hDistinct]
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

/-- Updating a remote base link leaves the purely spatial half-update factor at
`target` unchanged when the two links share no spatial plaquette. -/
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
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialIncrementSum_update_remote
      H N B target fiber u g hDistinct hNoShare]

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
    simp [Ne.symm hDistinct]
  rw [hAt]
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialIncrementSum_update_remote
      H N B target fiber u g hDistinct hNoShare]

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
  let Au : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update A fiber u
  let Av : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update A fiber v
  have hKug :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
      H N beta Br Au backgroundFiber g
  have hKuh :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
      H N beta Br Au backgroundFiber h
  have hKvg :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
      H N beta Br Av backgroundFiber g
  have hKvh :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
      H N beta Br Av backgroundFiber h
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
  change
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br
          (Function.update Au backgroundFiber g) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br
          (Function.update Av backgroundFiber h) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br
          (Function.update Au backgroundFiber h) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br
          (Function.update Av backgroundFiber g)
  calc
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br
          (Function.update Au backgroundFiber g) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br
          (Function.update Av backgroundFiber h) =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta Br Au backgroundFiber g *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br Au) *
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta Br Av backgroundFiber h *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br Av) := by
          rw [hKug, hKvh]
    _ =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta Br A backgroundFiber g *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br Au) *
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta Br A backgroundFiber h *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br Av) := by
          rw [hUg, hVh]
    _ =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta Br A backgroundFiber h *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br Au) *
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta Br A backgroundFiber g *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br Av) := by
          ring
    _ =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta Br Au backgroundFiber h *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br Au) *
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta Br Av backgroundFiber g *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br Av) := by
          rw [hUh, hVg]
    _ =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br
          (Function.update Au backgroundFiber h) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br
          (Function.update Av backgroundFiber g) := by
          rw [hKuh, hKvg]

end

end MathlibAnalytic
end MGAP4D