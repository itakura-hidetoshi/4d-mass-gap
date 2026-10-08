import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarBetaZeroAnchoredProjectionRankOne
import Mathlib.Tactic

/-!
# P4: the remaining anchored vacuum drift is a genuine joint posterior L2 variance

PR #5281 reduces the positive-beta projection drift of the exact beta-zero
physical receiver to the original transported posterior loss of the literal
pair-Haar constant-one function. This stage moves that exact loss back into
the ACTUAL positive-beta ground-state joint law using the already-defined
half-density linear isometry U_beta and its ORIGINAL conditional expectation
P_beta,e.

For every pair-Haar vector v (not just physical receiver inputs):
  ||v - Q_beta,e v||^2 = ||U_beta v - P_beta,e (U_beta v)||^2.

Hence the projection drift is exactly the squared Fourier coefficient
of the physical constant unit times the sum of genuine conditional
expectation residual energies of U_beta(1) under the original joint law.
No independent posterior law, replacement kernel, Dobrushin constant,
volume-dependent link count multiplier, or continuum-gap assertion occurs.

The volume-uniform bound on this TRUE vacuum energy, and that on the
receiver-drift term of #5280, remain open.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4JointVacTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4JointVacCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4JointVacSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4JointVacMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4JointVacBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4JointVacSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The transported projection Q_beta,e is *exactly* conjugate to the
original joint conditional expectation P_beta,e by the existing real L2
linear isometry U_beta. Thus genuine residual NORMS agree for every
pair-Haar input, with the original joint law unchanged. -/
theorem pairHaarTransportedGroundStateSpatialLinkProjection_residual_norm_eq_jointCondExp
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (v : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    ‖v - pairHaarTransportedGroundStateSpatialLinkProjection
        H N hN beta hbeta e v‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
          H N hN beta hbeta v -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta e
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta v)‖ := by
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H N hN beta hbeta
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta e
  have hU :
      U (v - U.symm (P (U v))) = U v - P (U v) := by
    rw [map_sub, LinearIsometryEquiv.apply_symm_apply]
  change ‖v - U.symm (P (U v))‖ = ‖U v - P (U v)‖
  calc
    ‖v - U.symm (P (U v))‖ =
        ‖U (v - U.symm (P (U v)))‖ := (U.norm_map _).symm
    _ = ‖U v - P (U v)‖ := by rw [hU]

/-- Squared-form version, adapted to the original all-link residual Gram. -/
theorem pairHaarTransportedGroundStateSpatialLinkProjection_residual_sq_eq_jointCondExp
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (v : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    ‖v - pairHaarTransportedGroundStateSpatialLinkProjection
        H N hN beta hbeta e v‖ ^ 2 =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
          H N hN beta hbeta v -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta e
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta v)‖ ^ 2 := by
  rw [pairHaarTransportedGroundStateSpatialLinkProjection_residual_norm_eq_jointCondExp
    H N hN beta hbeta e v]

/-- The TRUE full spatial-link vacuum loss in pair-Haar is the original
positive-beta posterior conditional-expectation L2 residual sum of
the actual transported vacuum U_beta(1), with NO changed law. -/
theorem pairHaarConstantOne_fullLinkResidual_eq_jointCondExpVacuum
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖(Lp.const 2
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
          (1 : ℝ)) -
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (Lp.const 2
            (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
            (1 : ℝ))‖ ^ 2) =
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta
            (Lp.const 2
              (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
              (1 : ℝ)) -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta e
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
              H N hN beta hbeta
              (Lp.const 2
                (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
                (1 : ℝ)))‖ ^ 2) := by
  classical
  apply Finset.sum_congr rfl
  intro e _he
  exact pairHaarTransportedGroundStateSpatialLinkProjection_residual_sq_eq_jointCondExp
    H N hN beta hbeta e
    (Lp.const 2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
      (1 : ℝ))

/-- COMPLETE exact reduction of the original anchored positive-beta
projection drift to the genuine joint posterior conditional fluctuation
of ONE transported beta-zero vacuum. A volume-uniform bound on the
resulting right-hand energy is not yet established. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_beta_zeroAnchored_fullProjectionDrift_eq_jointVacuum
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) -
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)‖ ^ 2) =
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f) ^ 2 *
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta
            (Lp.const 2
              (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
              (1 : ℝ)) -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta e
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
              H N hN beta hbeta
              (Lp.const 2
                (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
                (1 : ℝ)))‖ ^ 2) := by
  calc
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) -
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)‖ ^ 2) =
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f) ^ 2 *
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖(Lp.const 2
            (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
            (1 : ℝ)) -
          pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
            (Lp.const 2
              (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
              (1 : ℝ))‖ ^ 2) :=
      normalizedPhysicalOneSlabPairHaarReceiver_beta_zeroAnchored_fullProjectionDrift_eq_constOne
        H N hN beta hbeta f
    _ = _ := by
      rw [pairHaarConstantOne_fullLinkResidual_eq_jointCondExpVacuum
        H N hN beta hbeta]

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
