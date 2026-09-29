import MGAP4D.MathlibAnalytic.RealHilbertProjectionSourceFixedLeakage
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicTerminalProfileForcingBudgetBoundedCore
import Mathlib.Tactic

/-!
# Cyclic source-residual forcing from source-fixed leakage

The missing analytic estimate can be stated on source-fixed bounded-core
inputs g, with the explicit coefficient orientation K(source,target):

  ||P_target g - P_source(P_target g)||
    <= K(source,target) * ||g - P_target g||,
  P_source g = g.

Hilbert duality then gives the actual one-step forcing
K(source,target) * ||x - P_source x||, not a projected full-input norm.
PR #4923 supplies the domain-correct terminal receiver and is reused directly.

This is a sufficient-input theorem: the physical beta-small leakage estimate
and the identification/domination of K by the #4902 envelope remain separate.
No commutator/source-residual substitution, new telescope, cardinality factor,
source/target symmetry, or positive-beta commutativity is assumed.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace

noncomputable section

local instance cyclicSourceFixedLeakageSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

/-- Source-fixed bounded-core leakage suffices for a source-residual cyclic budget.
The analytic premise is never extended to the ambient joint L2 space. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_le_cyclicSourceResidualBudget_of_sourceFixedLeakage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix : List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (target : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta)
    (hf : f ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta)
    (hSplit : (Finset.univ : Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
      pre ++ target :: suffix)
    (K : PeriodicHypercubicEvenFixedSpatialColorLink H color →
      PeriodicHypercubicEvenFixedSpatialColorLink H color → ℝ)
    (hK : ∀ source, 0 ≤ K source target)
    (hLeakage :
      let P :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color
      ∀ (source : PeriodicHypercubicEvenFixedSpatialColorLink H color),
        source.1 ≠ target.1 →
        ∀ (g : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta),
          g ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
            H N hN beta hbeta →
          P source g = g →
          ‖P target g - P source (P target g)‖ ≤
            K source target * ‖g - P target g‖) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
        H N hN beta hbeta color f target ≤
      realHilbertProjectionSweepTargetResidualForcingBudget
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color)
        (fun source x => K source target *
          ‖x - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color source x‖)
        (suffix ++ pre)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color target
          (realHilbertProjectionSweep
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color) pre f)) := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  have hIdem : ∀ e, (P e).comp (P e) = P e := by
    intro e
    simpa only [P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
        H N hN beta hbeta e.1
  have hSymm : ∀ (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
      (u v : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta),
      inner ℝ (P e u) v = inner ℝ u (P e v) := by
    intro e u v
    simpa only [P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_symmetric
        H N hN beta hbeta e.1 u v
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_le_cyclicForcingBudget_of_boundedCore
      H N hN beta hbeta color pre suffix target f hf hSplit
      (fun source x => K source target * ‖x - P source x‖)
  -- Normalize the receiver's leading `let P := ...` before naming its forall binders.
  change ∀ (source : PeriodicHypercubicEvenFixedSpatialColorLink H color),
    source.1 ≠ target.1 →
    ∀ (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta),
      x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta →
      ‖P source x - P target (P source x)‖ ≤
        K source target * ‖x - P source x‖ + ‖x - P target x‖
  intro source hne x hx
  have hUpdatedCore : P source x ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2_mem_boundedConcreteCore
      H N hN beta hbeta color source x hx
  have hUpdatedFixed : P source (P source x) = P source x := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg
        (fun T : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →L[ℝ]
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            H N hN beta hbeta => T x)
        (hIdem source)
  have hOne :=
    realHilbertProjection_targetResidual_norm_le_add_sourceResidual_of_leakage
      (P target) (P source) (hIdem target) (hIdem source)
      (hSymm target) (hSymm source) (K source target) (hK source) x
      (hLeakage source hne (P source x) hUpdatedCore hUpdatedFixed)
  calc
    ‖P source x - P target (P source x)‖ ≤
      ‖x - P target x‖ + K source target * ‖x - P source x‖ := hOne
    _ = K source target * ‖x - P source x‖ + ‖x - P target x‖ := add_comm _ _

end

end MGAP4D.MathlibAnalytic
