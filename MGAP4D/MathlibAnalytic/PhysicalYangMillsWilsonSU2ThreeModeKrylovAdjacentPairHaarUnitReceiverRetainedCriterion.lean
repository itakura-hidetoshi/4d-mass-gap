import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFineZeroUniformIffUnitEnergyZero
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumZeroIffRetainedWilson
import Mathlib.Tactic

/-!
# P4-Q2-G: original physical constant-unit receiver retained-link criterion

The positive-beta SU(2) Wilson density non-retained theorem of P4-F2/F3
concerns the inverse square root of the joint density, not automatically
the genuine normalized-transfer image of a physical constant input.

This file keeps the distinction explicit. For the ACTUAL uncentered
constant physical unit u_H, its original pair-Haar receiver v_beta(u_H)
and the true one-link Wilson conditional expectation Q_beta,e satisfy

  ||v_beta(u_H) - Q_beta,e v_beta(u_H)||^2 = 0
    iff J_beta,u_H is retained-link AEStronglyMeasurable in mu_joint.

Here J_beta,u_H is the EXISTING bounded continuous joint observable
W_beta M_beta,u_H, exactly equal in joint L² to the authentic half-density
transport U_beta v_beta(u_H). No surrogate density or conditional law.

The full original physical unit receiver energy vanishes iff this
retained sigma-algebra condition holds at EVERY original right link.
Non-retention at even one genuine physical link implies strict positivity
of the full physical constant-unit receiver energy.

The remaining analytic task is to prove non-retention of this particular
positive-beta receiver, not to substitute P4-F3 vacuum non-retention
without justification. No Dobrushin, sorry, admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4UnitRetTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4UnitRetCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4UnitRetSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4UnitRetMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4UnitRetBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4UnitRetLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The original single-link constant-unit physical innovation is zero
exactly when its ACTUAL joint continuous receiver is retained-measurable.
The claimed representative is supplied by the existing pair-Haar
half-density isometry, not a pointwise statement about arbitrary L². -/
theorem physicalOriginalUnitReceiver_linkResidual_sq_zero_iff_retained
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
    let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta u
    let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
    let J := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta u
    ‖v - Q v‖ ^ 2 = 0 ↔
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N e]
        (fun z => J z)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) := by
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta u
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
    H N hN beta hbeta e
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
  let J := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta u
  let μ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta
  let m := periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
    H N e
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H N hN beta hbeta
  have hTransport : BoundedContinuousFunction.toLp 2 μ ℝ J = U v := by
    exact normalizedPhysicalOneSlabJointReceiverProductBCF_toLp_eq_pairHaarReceiver
      H N hN beta hbeta u
  have hRep : (fun z => (U v) z) =ᵐ[μ] fun z => J z := by
    rw [← hTransport]
    exact BoundedContinuousFunction.coeFn_toLp 2 μ ℝ J
  have hRetained :
      AEStronglyMeasurable[m] (fun z => (U v) z) μ ↔
        AEStronglyMeasurable[m] (fun z => J z) μ := by
    constructor
    · intro h; exact h.congr hRep
    · intro h; exact h.congr hRep.symm
  have hP :
      P (U v) = U v ↔
        AEStronglyMeasurable[m] (fun z => (U v) z) μ := by
    change periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta e (U v) = U v ↔ _
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_apply]
    exact realL2_condExp_fixed_iff_retained_aestronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
        H N e) (U v)
  have hQ : Q v = v ↔ P (U v) = U v := by
    change U.symm (P (U v)) = v ↔ P (U v) = U v
    constructor
    · intro h
      have h' := congrArg U h
      simpa only [LinearIsometryEquiv.apply_symm_apply] using h'
    · intro h
      rw [h]
      exact U.symm_apply_apply v
  have hNorm : (‖v - Q v‖ ^ 2 = 0) ↔ Q v = v := by
    constructor
    · intro h
      have hv : ‖v - Q v‖ = 0 := by
        nlinarith [norm_nonneg (v - Q v)]
      exact (sub_eq_zero.mp (norm_eq_zero.mp hv)).symm
    · intro h
      rw [h]
      simp
  change (‖v - Q v‖ ^ 2 = 0) ↔
    AEStronglyMeasurable[m] (fun z => J z) μ
  exact hNorm.trans (hQ.trans (hP.trans hRetained))

/-- The ORIGINAL physical constant-unit full spatial-link Wilson
posterior energy is zero exactly when its authentic continuous joint
receiver is retained-measurable at EVERY target link. -/
theorem physicalOriginalUnitReceiverFullLinkEnergy_zero_iff_all_retained
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    physicalOriginalUnitReceiverFullLinkEnergy H N hN beta hbeta = 0 ↔
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        AEStronglyMeasurable[
          periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N e]
          (fun z => normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) z)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta) := by
  classical
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta u
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta
  let J := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta u
  let μ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta
  have hSum :
      ((∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖v - Q e v‖ ^ 2) = 0) ↔
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖v - Q e v‖ ^ 2 = 0 := by
    constructor
    · intro h e
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (s := Finset.univ) (f := fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
          ‖v - Q e v‖ ^ 2)
        (by intro j _hj; exact sq_nonneg _)).mp h e (Finset.mem_univ e)
    · intro h
      apply (Finset.sum_eq_zero_iff_of_nonneg
        (s := Finset.univ) (f := fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
          ‖v - Q e v‖ ^ 2)
        (by intro j _hj; exact sq_nonneg _)).mpr
      intro e _he
      exact h e
  change ((∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖v - Q e v‖ ^ 2) = 0) ↔
    ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N e]
        (fun z => J z) μ
  constructor
  · intro h e
    exact (physicalOriginalUnitReceiver_linkResidual_sq_zero_iff_retained
      H N hN beta hbeta e).mp ((hSum.mp h) e)
  · intro h
    apply hSum.mpr
    intro e
    exact (physicalOriginalUnitReceiver_linkResidual_sq_zero_iff_retained
      H N hN beta hbeta e).mpr (h e)

/-- Non-retention of the ACTUAL normalized-transfer physical constant
receiver at ONE original Wilson link strictly forces positive E_unit.
This is the correct transfer-independent mathematical interface for
the P4-F2 crossing witness; vacuum non-retention is not substituted. -/
theorem physicalOriginalUnitReceiverFullLinkEnergy_pos_of_not_retained
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (hNotRetained : ¬ AEStronglyMeasurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N e]
      (fun z => normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) z)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)) :
    0 < physicalOriginalUnitReceiverFullLinkEnergy H N hN beta hbeta := by
  have hNonneg := physicalOriginalUnitReceiverFullLinkEnergy_nonneg H N hN beta hbeta
  rcases lt_or_eq_of_le hNonneg with hPos | hZero
  · exact hPos
  · have hRet := (physicalOriginalUnitReceiverFullLinkEnergy_zero_iff_all_retained
      H N hN beta hbeta).mp hZero.symm
    exact False.elim (hNotRetained (hRet e))

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
