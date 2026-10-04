import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointBoundedConcreteCoreDensity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialOneLinkSweepStageProfile
import Mathlib.Tactic

/-!
# Dense-core closure for the genuine sweep-stage profile energy

The bounded-concrete response machinery is proved on a dense core of the
genuine ground-state joint L2 carrier.  The adjacent frozen Krylov vector,
however, is obtained through a half-density transform and need not itself have
a globally bounded representative.

This file isolates the lossless topological bridge.  Finite projection-sweep
path loss is continuous in the Hilbert vector.  Consequently the normalized
six-spatial sweep-stage profile energy is continuous.  Any upper estimate by
a continuous majorant proved on the already-dense bounded-concrete core
therefore extends to every genuine joint L2 vector with exactly the same
constant.

No bounded representative is asserted for an arbitrary L2 vector.  No
Dobrushin, transfer, or support-separation estimate is added here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- Finite projection-sweep path loss is continuous in the input vector. -/
theorem continuous_realHilbertProjectionSweepPathLoss
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (cs : List C) :
    Continuous (realHilbertProjectionSweepPathLoss P cs) := by
  induction cs with
  | nil =>
      simpa [realHilbertProjectionSweepPathLoss] using
        (continuous_const : Continuous (fun _ : E => (0 : ℝ)))
  | cons c cs ih =>
      simp only [realHilbertProjectionSweepPathLoss]
      have hResidual :
          Continuous (fun x : E => ‖x - P c x‖ ^ 2) := by
        fun_prop
      have hTail :
          Continuous
            (fun x : E =>
              realHilbertProjectionSweepPathLoss P cs (P c x)) :=
        ih.comp (P c).continuous
      exact hResidual.add hTail

/-- One label's squared sweep-stage residual profile is continuous in the
input vector. -/
theorem continuous_realHilbertProjectionSweepStageResidualSqProfile
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [DecidableEq C]
    (P : C → E →L[ℝ] E)
    (cs : List C)
    (d : C) :
    Continuous
      (fun x : E =>
        realHilbertProjectionSweepStageResidualSqProfile P cs x d) := by
  induction cs with
  | nil =>
      simpa [realHilbertProjectionSweepStageResidualSqProfile] using
        (continuous_const : Continuous (fun _ : E => (0 : ℝ)))
  | cons c cs ih =>
      simp only [realHilbertProjectionSweepStageResidualSqProfile]
      have hTail :
          Continuous
            (fun x : E =>
              realHilbertProjectionSweepStageResidualSqProfile
                P cs (P c x) d) :=
        ih.comp (P c).continuous
      by_cases hdc : d = c
      · simp only [if_pos hdc]
        have hHead :
            Continuous (fun x : E => ‖x - P c x‖ ^ 2) := by
          fun_prop
        exact hHead.add hTail
      · simp only [if_neg hdc, zero_add]
        exact hTail

/-- One label's nonnegative sweep-stage residual amplitude is continuous. -/
theorem continuous_realHilbertProjectionSweepStageResidualAmplitude
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [DecidableEq C]
    (P : C → E →L[ℝ] E)
    (cs : List C)
    (d : C) :
    Continuous
      (fun x : E =>
        realHilbertProjectionSweepStageResidualAmplitude P cs x d) := by
  unfold realHilbertProjectionSweepStageResidualAmplitude
  exact
    Real.continuous_sqrt.comp
      (continuous_realHilbertProjectionSweepStageResidualSqProfile
        P cs d)

local instance groundStateSweepStageProfileCoreClosureSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The normalized genuine spatial-link sweep-stage profile energy on the
whole ground-state joint L2 carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) : ℝ :=
  (1 / 6 : ℝ) *
    ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
        H N hN beta hbeta f e ^ 2

/-- The normalized profile energy is exactly the existing six-spatial
one-link sweep path loss. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy_eq_pathLoss
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
        H N hN beta hbeta f =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
        H N hN beta hbeta f := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
  ] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_normalized_sq_sum_eq_sweepPathLoss
      H N hN beta hbeta f)

/-- The genuine six-spatial one-link sweep path loss is continuous. -/
theorem
    continuous_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
        H N hN beta hbeta) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
  apply continuous_const.mul
  apply continuous_finset_sum
  intro c _hc
  exact
    continuous_realHilbertProjectionSweepPathLoss
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
        H N hN beta hbeta
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c))
      ((Finset.univ :
        Finset
          (PeriodicHypercubicEvenFixedSpatialColorLink H
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c))).toList)

/-- The genuine normalized link-profile energy is continuous on the full
joint L2 carrier. -/
theorem
    continuous_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
        H N hN beta hbeta) := by
  have hPath :=
    continuous_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
      H N hN beta hbeta
  apply hPath.congr
  intro f
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy_eq_pathLoss
      H N hN beta hbeta f).symm

/-- Any continuous upper majorant established on the dense bounded-concrete
core controls the normalized sweep-stage profile energy on every genuine
ground-state joint L2 vector, with no loss in coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy_le_of_boundedConcreteCore
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (majorant :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta → ℝ)
    (hMajorant : Continuous majorant)
    (hcore :
      ∀ f,
        f ∈
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
              H N hN beta hbeta →
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
              H N hN beta hbeta f ≤
            majorant f) :
    ∀ f,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
          H N hN beta hbeta f ≤
        majorant f := by
  let core : Set
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
      H N hN beta hbeta
  let good : Set
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :=
    {f |
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
          H N hN beta hbeta f ≤
        majorant f}
  have hEnergy :
      Continuous
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
          H N hN beta hbeta) :=
    continuous_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
      H N hN beta hbeta
  have hGoodClosed : IsClosed good := by
    simpa [good] using isClosed_le hEnergy hMajorant
  have hCoreSub : core ⊆ good := by
    intro f hf
    exact hcore f (by simpa [core] using hf)
  have hClosureSub : closure core ⊆ good :=
    closure_minimal hCoreSub hGoodClosed
  have hDense : Dense core := by
    simpa [core] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore_dense
        H N hN beta hbeta
  intro f
  have hf : f ∈ closure core := by
    rw [hDense.closure_eq]
    exact Set.mem_univ f
  exact hClosureSub hf

/-- Constant-upper-bound specialization of the dense-core closure theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy_le_const_of_boundedConcreteCore
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : ℝ)
    (hcore :
      ∀ f,
        f ∈
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
              H N hN beta hbeta →
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
              H N hN beta hbeta f ≤ C) :
    ∀ f,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
          H N hN beta hbeta f ≤ C := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy_le_of_boundedConcreteCore
      H N hN beta hbeta (fun _ => C) continuous_const hcore

end

end MathlibAnalytic
end MGAP4D
