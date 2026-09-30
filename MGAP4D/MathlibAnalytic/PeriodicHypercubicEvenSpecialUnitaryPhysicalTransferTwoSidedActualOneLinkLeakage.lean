import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferCrossBoundaryLeftSourceSupported
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointTwoBoundaryOrderedSchur
import MGAP4D.MathlibAnalytic.RealHilbertProjectionSourceFixedLeakage
import Mathlib.Tactic

/-!
# Actual two-sided one-link leakage with the ordered block kernel

The one-boundary ordered leakage is already available on genuine right one-link
updates. PR #4965 closes the opposite-boundary analytic input with the exact
one-point-supported cross majorant.

This file puts the four source/target boundary orientations on the common
Sum Link Link carrier:

* right -> right: existing ordered same-boundary coefficient;
* left -> left: endpoint-swap conjugate of the same theorem;
* left -> right: #4965 directly;
* right -> left: endpoint-swap conjugate of #4965.

Thus the actual source-update leakage is controlled pointwise by exactly
GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel target source.

The generic Hilbert projection identity then converts this to the actual
source-residual one-step forcing estimate required by the two-sided recurrence.

No new coefficient, cutoff, factor two, link-count factor, or volume factor is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance twoSidedActualLeakageSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance twoSidedActualLeakageSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance twoSidedActualLeakageSecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance twoSidedActualLeakageMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance twoSidedActualLeakageBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance twoSidedActualLeakageSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Endpoint swap sends a genuine left one-link projection back to the
corresponding right one-link projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_leftSpatialLinkCondExpL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H N hN beta hbeta target f) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN beta hbeta target
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
          H N hN beta hbeta f) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_eq_swap_right_swap
      H N hN beta hbeta target f,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_apply_apply
      H N hN beta hbeta]

/-- The two-sided one-link family preserves the bounded concrete core. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_mem_boundedConcreteCore
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta source f ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta := by
  cases source with
  | inl source =>
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_mem_boundedConcreteCore
          H N hN beta hbeta source f hf
  | inr source =>
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_mem_boundedConcreteCore
          H N hN beta hbeta source f hf

/-- Every projection in the two-sided one-link family is idempotent. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_idempotent
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta target).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta target) =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta target := by
  cases target with
  | inl target =>
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
          H N hN beta hbeta target
  | inr target =>
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_idempotent
          H N hN beta hbeta target

/-- Every projection in the two-sided one-link family is symmetric. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_symmetric
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta target :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            H N hN beta hbeta →L[ℝ]
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            H N hN beta hbeta) :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →ₗ[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta).IsSymmetric := by
  cases target with
  | inl target =>
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_symmetric
          H N hN beta hbeta target
  | inr target =>
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_symmetric
          H N hN beta hbeta target

/-- Same-boundary ordered leakage on actual left one-link updates, obtained by
endpoint-swap conjugacy from the established right-boundary theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSourceUpdate_jointLeakage_norm_le_orderedNormCoefficient
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
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
      target ≠ source →
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
            H N hN beta hbeta target
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
              H N hN beta hbeta source f) -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
            H N hN beta hbeta source
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
                H N hN beta hbeta source f))‖ ≤
        GroundStateSourceFixedPairEnergy.jointLeakageNormCoefficient
            H N hN beta hbeta s source target *
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
                H N hN beta hbeta source f -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
                H N hN beta hbeta target
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
                  H N hN beta hbeta source f)‖ := by
  intro target hne
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
      H N hN beta hbeta
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta
  let L :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
      H N hN beta hbeta
  have hECore :
      E f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_mem_boundedConcreteCore
      H N hN beta hbeta f hf
  have hRight :=
    GroundStateSourceFixedPairEnergy.sourceUpdate_jointLeakage_norm_le_orderedNormCoefficient
      H N hN beta hbeta s hs hcut source (E f) hECore target hne
  have hNum :
      ‖L target (L source f) - L source (L target (L source f))‖ =
        ‖R target (R source (E f)) - R source (R target (R source (E f)))‖ := by
    calc
      ‖L target (L source f) - L source (L target (L source f))‖ =
          ‖E (L target (L source f) - L source (L target (L source f)))‖ :=
        (E.norm_map _).symm
      _ =
          ‖R target (R source (E f)) - R source (R target (R source (E f)))‖ := by
        rw [E.map_sub]
        simp only [
          E, R, L,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_leftSpatialLinkCondExpL2]
  have hDen :
      ‖L source f - L target (L source f)‖ =
        ‖R source (E f) - R target (R source (E f))‖ := by
    calc
      ‖L source f - L target (L source f)‖ =
          ‖E (L source f - L target (L source f))‖ :=
        (E.norm_map _).symm
      _ = ‖R source (E f) - R target (R source (E f))‖ := by
        rw [E.map_sub]
        simp only [
          E, R, L,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_leftSpatialLinkCondExpL2]
  rw [hNum, hDen]
  exact hRight

/-- Reverse cross-boundary orientation: an actual right source update followed
by a left target update. This is the swap-conjugate of #4965. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundary_rightSourceUpdate_leakage_norm_le_crossMajorant
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta source f) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta source
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
            H N hN beta hbeta target
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta source f))‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta target source *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta source f -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                H N hN beta hbeta source f)‖ := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
      H N hN beta hbeta
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta
  let L :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
      H N hN beta hbeta
  have hECore :
      E f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_mem_boundedConcreteCore
      H N hN beta hbeta f hf
  have hCross :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundary_leftSourceUpdate_leakage_norm_le_crossMajorant
      H N hN beta hbeta hBetaLt source target (E f) hECore
  have hNum :
      ‖L target (R source f) - R source (L target (R source f))‖ =
        ‖R target (L source (E f)) - L source (R target (L source (E f)))‖ := by
    calc
      ‖L target (R source f) - R source (L target (R source f))‖ =
          ‖E (L target (R source f) - R source (L target (R source f)))‖ :=
        (E.norm_map _).symm
      _ =
          ‖R target (L source (E f)) - L source (R target (L source (E f)))‖ := by
        rw [E.map_sub]
        simp only [
          E, R, L,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_leftSpatialLinkCondExpL2,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightSpatialLinkCondExpL2]
  have hDen :
      ‖R source f - L target (R source f)‖ =
        ‖L source (E f) - R target (L source (E f))‖ := by
    calc
      ‖R source f - L target (R source f)‖ =
          ‖E (R source f - L target (R source f))‖ :=
        (E.norm_map _).symm
      _ = ‖L source (E f) - R target (L source (E f))‖ := by
        rw [E.map_sub]
        simp only [
          E, R, L,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_leftSpatialLinkCondExpL2,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightSpatialLinkCondExpL2]
  rw [hNum, hDen]
  exact hCross

/-- Actual source-update leakage on the complete two-sided one-link carrier.
The coefficient is exactly the target-first/source-second block kernel from
#4946. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_sourceUpdate_leakage_norm_le_orderedKernel
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
    (source target : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)
    (hne : target ≠ source)
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
    ‖P target (P source f) - P source (P target (P source f))‖ ≤
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel
          H N hN beta hbeta s target source *
        ‖P source f - P target (P source f)‖ := by
  dsimp only
  cases source with
  | inl source =>
      cases target with
      | inl target =>
          have hne' : target ≠ source := by
            intro h
            subst target
            exact hne rfl
          simpa [
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2,
            GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel] using
            GroundStateSourceFixedPairEnergy.sourceUpdate_jointLeakage_norm_le_orderedNormCoefficient
              H N hN beta hbeta s hs hcut source f hf target hne'
      | inr target =>
          simpa [
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2,
            GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel] using
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundary_rightSourceUpdate_leakage_norm_le_crossMajorant
              H N hN beta hbeta hBetaLt source target f hf
  | inr source =>
      cases target with
      | inl target =>
          simpa [
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2,
            GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel] using
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundary_leftSourceUpdate_leakage_norm_le_crossMajorant
              H N hN beta hbeta hBetaLt source target f hf
      | inr target =>
          have hne' : target ≠ source := by
            intro h
            subst target
            exact hne rfl
          simpa [
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2,
            GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel] using
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSourceUpdate_jointLeakage_norm_le_orderedNormCoefficient
              H N hN beta hbeta s hs hcut source f hf target hne'

/-- The corresponding genuine two-sided one-step forcing estimate. This is the
source-residual form needed by the cyclic/renewal recurrence machinery. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_sourceUpdate_targetResidual_norm_le_add_sourceResidual
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
    (source target : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)
    (hne : target ≠ source)
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
    ‖P source f - P target (P source f)‖ ≤
      ‖f - P target f‖ +
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel
            H N hN beta hbeta s target source *
          ‖f - P source f‖ := by
  dsimp only
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  exact
    realHilbertProjection_targetResidual_norm_le_add_sourceResidual_of_leakage
      (P target) (P source)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_idempotent
        H N hN beta hbeta target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_idempotent
        H N hN beta hbeta source)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_symmetric
        H N hN beta hbeta target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_symmetric
        H N hN beta hbeta source)
      (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel
        H N hN beta hbeta s target source)
      (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel_nonneg
        H N hN beta hbeta s target source)
      f
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_sourceUpdate_leakage_norm_le_orderedKernel
        H N hN beta hbeta s hs hcut hBetaLt source target hne f hf)

end

end MathlibAnalytic
end MGAP4D
