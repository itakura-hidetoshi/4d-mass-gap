import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedActualOneLinkLeakage
import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepTargetResidualForcingBudgetTelescope
import Mathlib.Tactic

/-!
# Bounded-core two-sided cyclic forcing budget

The actual two-sided one-link forcing estimate from #4966 is valid on the
bounded concrete core, and every genuine two-sided one-link projection
preserves that core.  The generic forcing telescope in the repository was
stated with an ambient universal one-step premise.

This file adds the domain-correct trajectory form: the one-step premise is
required only on a preserved predicate.  It is then instantiated with the
bounded concrete core and the exact two-boundary ordered kernel.

For any target-fixed bounded-core starting vector and any finite tagged
two-sided source list,

  target residual after the sweep
    <= sum along the actual trajectory of
       K(target,source) * source residual.

A cyclic specialization starts immediately after a target projection and then
runs any suffix ++ prefix list.  No ambient-L2 extension, cardinality factor,
coefficient two, or volume factor is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance twoSidedCyclicForcingSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Domain-correct version of the fixed-start forcing telescope.  The
one-step estimate is required only on a predicate preserved by every
projection along the trajectory. -/
theorem
    realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_of_fixed_of_preserved
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target : C)
    (forcing : C → E → ℝ)
    (Core : E → Prop)
    (hPreserve : ∀ source x, Core x → Core (P source x))
    (hStep : ∀ source x, Core x →
      ‖P source x - P target (P source x)‖ ≤
        forcing source x + ‖x - P target x‖)
    (sources : List C)
    (x : E)
    (hx : Core x)
    (hFixed : P target x = x) :
    ‖realHilbertProjectionSweep P sources x -
        P target (realHilbertProjectionSweep P sources x)‖ ≤
      realHilbertProjectionSweepTargetResidualForcingBudget
        P forcing sources x := by
  induction sources generalizing x with
  | nil =>
      simpa only [
        realHilbertProjectionSweep,
        realHilbertProjectionSweepTargetResidualForcingBudget,
        ContinuousLinearMap.id_apply,
        hFixed, sub_self, norm_zero] using
        (le_rfl : (0 : ℝ) ≤ 0)
  | cons source sources ih =>
      have hxNext : Core (P source x) :=
        hPreserve source x hx
      have hTail := ih (P source x) hxNext
      have hOne := hStep source x hx
      simp only [realHilbertProjectionSweep, ContinuousLinearMap.comp_apply]
      calc
        ‖realHilbertProjectionSweep P sources (P source x) -
            P target (realHilbertProjectionSweep P sources (P source x))‖ ≤
          realHilbertProjectionSweepTargetResidualForcingBudget
              P forcing sources (P source x) +
            ‖P source x - P target (P source x)‖ := by
          exact
            (hTail.trans
              (le_add_of_nonneg_right (norm_nonneg _)))
        _ ≤
          realHilbertProjectionSweepTargetResidualForcingBudget
              P forcing sources (P source x) +
            (forcing source x + ‖x - P target x‖) :=
          _root_.add_le_add le_rfl hOne
        _ =
          realHilbertProjectionSweepTargetResidualForcingBudget
              P forcing (source :: sources) x +
            ‖x - P target x‖ := by
          change
            realHilbertProjectionSweepTargetResidualForcingBudget
                P forcing sources (P source x) +
              (forcing source x + ‖x - P target x‖) =
            (forcing source x +
              realHilbertProjectionSweepTargetResidualForcingBudget
                P forcing sources (P source x)) +
              ‖x - P target x‖
          ring
        _ =
          realHilbertProjectionSweepTargetResidualForcingBudget
              P forcing (source :: sources) x := by
          rw [hFixed, sub_self, norm_zero, add_zero]

/-- Every finite sweep by the genuine two-sided one-link family preserves the
bounded concrete core. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweep_mem_boundedConcreteCore
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
          H N hN beta hbeta)
        sources f ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta := by
  induction sources generalizing f with
  | nil =>
      simpa [realHilbertProjectionSweep] using hf
  | cons source sources ih =>
      simp only [realHilbertProjectionSweep, ContinuousLinearMap.comp_apply]
      apply ih
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_mem_boundedConcreteCore
          H N hN beta hbeta source f hf

/-- A target-fixed bounded-core vector obeys the actual two-sided ordered
forcing budget along any finite tagged one-link list. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_targetResidual_norm_le_orderedForcingBudget_of_fixed
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 < s)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (target : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hx :
      x ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta)
    (hFixed :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
          H N hN beta hbeta target x = x) :
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta
    let K :=
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel
        H N hN beta hbeta s
    ‖realHilbertProjectionSweep P sources x -
        P target (realHilbertProjectionSweep P sources x)‖ ≤
      realHilbertProjectionSweepTargetResidualForcingBudget
        P
        (fun source y => K target source * ‖y - P source y‖)
        sources x := by
  dsimp only
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let K :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel
      H N hN beta hbeta s
  let Core :=
    fun y :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta =>
      y ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta
  apply
    realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_of_fixed_of_preserved
      P target
      (fun source y => K target source * ‖y - P source y‖)
      Core
      (fun source y hy =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_mem_boundedConcreteCore
          H N hN beta hbeta source y hy)
      ?_ sources x hx hFixed
  intro source y hy
  by_cases hst : source = target
  · subst source
    have hIdem :
        P target (P target y) = P target y := by
      simpa only [P, ContinuousLinearMap.comp_apply] using
        congrArg
          (fun T :
            PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
                H N hN beta hbeta →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
                H N hN beta hbeta =>
            T y)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_idempotent
            H N hN beta hbeta target)
    rw [hIdem, sub_self, norm_zero]
    exact
      add_nonneg
        (mul_nonneg
          (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel_nonneg
            H N hN beta hbeta s target target)
          (norm_nonneg _))
        (norm_nonneg _)
  · have hActual :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_sourceUpdate_targetResidual_norm_le_add_sourceResidual
        H N hN beta hbeta s hs hcut hBetaLt source target hst y hy
    simpa [P, K, add_comm] using hActual

/-- Cyclic specialization: start immediately after the distinguished target
projection, then run any suffix followed by any prefix.  This is the exact
shape used between two consecutive visits to the target in a canonical sweep. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_cyclicTargetResidual_norm_le_orderedForcingBudget
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 < s)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (pre suffix :
      List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (target : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta
    let K :=
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel
        H N hN beta hbeta s
    let x0 := P target (realHilbertProjectionSweep P pre f)
    ‖realHilbertProjectionSweep P (suffix ++ pre) x0 -
        P target (realHilbertProjectionSweep P (suffix ++ pre) x0)‖ ≤
      realHilbertProjectionSweepTargetResidualForcingBudget
        P
        (fun source y => K target source * ‖y - P source y‖)
        (suffix ++ pre) x0 := by
  dsimp only
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let x0 := P target (realHilbertProjectionSweep P pre f)
  have hPre :
      realHilbertProjectionSweep P pre f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta := by
    simpa only [P] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweep_mem_boundedConcreteCore
        H N hN beta hbeta pre f hf
  have hStart :
      x0 ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_mem_boundedConcreteCore
        H N hN beta hbeta target
        (realHilbertProjectionSweep P pre f) hPre
  have hFixed : P target x0 = x0 := by
    have h :=
      congrArg
        (fun T :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
              H N hN beta hbeta →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
              H N hN beta hbeta =>
          T (realHilbertProjectionSweep P pre f))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_idempotent
          H N hN beta hbeta target)
    simpa only [x0, P, ContinuousLinearMap.comp_apply] using h
  simpa [P, x0] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_targetResidual_norm_le_orderedForcingBudget_of_fixed
      H N hN beta hbeta s hs hcut hBetaLt target
      (suffix ++ pre) x0 hStart hFixed

end

end MathlibAnalytic
end MGAP4D
