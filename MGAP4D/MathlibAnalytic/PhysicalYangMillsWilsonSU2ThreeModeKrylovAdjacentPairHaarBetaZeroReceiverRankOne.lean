import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarGramDiagonalRayleighCriterion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroRankOne
import Mathlib.Tactic

/-!
# P4: beta-zero frozen physical pair-Haar receiver is exactly rank one

At frozen coupling beta = 0 the ORIGINAL normalized physical one-slab
transfer is already the canonical real rank-one projection onto the
physical constant unit vector. No posterior comparison or Dobrushin
coefficient is needed.

This unit transports that identity through the exact already-defined
pair-Haar receiver
  v_f = lambda^(-1) ((S f) o snd).

For ALL physical inputs f at every finite spatial size H, v_f is the
single beta-zero constant-input receiver multiplied by the exact
physical Haar inner product with the canonical constant unit vector.
Because Q_e is the ORIGINAL half-density-transported genuine posterior
conditional expectation, its one-link residual obeys the same rank-one
scaling. Hence every true full-link Gram diagonal reduces to one
common constant-input residual sum.

This is a reduction, not a claim that the common residual is already
zero or uniformly controlled. A subsequent step must prove how Q_e
acts on that constant-input receiver. There is no hard-support
assumption for positive orbit depth and no continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4BetaZeroReceiverTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4BetaZeroReceiverCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4BetaZeroReceiverSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4BetaZeroReceiverMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4BetaZeroReceiverBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4BetaZeroReceiverSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The actual frozen pair-Haar receiver at beta zero factors exactly
through the one-dimensional physical constant mode, for EVERY physical
input, without a volume-dependent vacuum-denominator estimate. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_zero_rankOne
    (H N : ℕ) (hN : 0 < N)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f =
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f) •
        normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) := by
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN 0 (by norm_num)
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN 0 (by norm_num)
  let c : ℝ := inner ℝ u f
  let B :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
    (Lp.compMeasurePreservingₗ ℝ Prod.snd
        (spatialSlicePairHaar_snd_measurePreserving H N)).comp
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).subtype
  have hSf : S f = c • u := by
    change periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN 0 (by norm_num) f = _
    rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_zero_eq_rankOne
      H N hN, InnerProductSpace.rankOne_apply]
  have hSu : S u = u :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_zero_constantUnit
      H N hN
  have hSfUnit : S f = c • S u := by rw [hSf, hSu]
  change ‖T‖⁻¹ • B (S f) = c • (‖T‖⁻¹ • B (S u))
  rw [hSfUnit, map_smul, smul_comm]

/-- Each ORIGINAL transported posterior one-link squared residual of
the beta-zero physical receiver is the constant-input residual times
the exact square of the physical constant Fourier coefficient. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_zero_linkResidual_sq_rankOne
    (H N : ℕ) (hN : 0 < N)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f -
      pairHaarTransportedGroundStateSpatialLinkProjection
        H N hN 0 (by norm_num) e
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)‖ ^ 2 =
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f) ^ 2 *
      ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) -
        pairHaarTransportedGroundStateSpatialLinkProjection
          H N hN 0 (by norm_num) e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N))‖ ^ 2 := by
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let V := normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection
    H N hN 0 (by norm_num) e
  let c : ℝ := inner ℝ u f
  have hv : V f = c • V u :=
    normalizedPhysicalOneSlabPairHaarReceiver_zero_rankOne H N hN f
  have hq : Q (V f) = c • Q (V u) := by
    rw [hv]
    exact pairHaarTransportedGroundStateSpatialLinkProjection_smul
      H N hN 0 (by norm_num) e c (V u)
  have hr : V f - Q (V f) = c • (V u - Q (V u)) := by
    rw [hv, hq, smul_sub]
  change ‖V f - Q (V f)‖ ^ 2 = c ^ 2 * ‖V u - Q (V u)‖ ^ 2
  rw [hr, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- The ENTIRE genuine spatial-link residual sum has the same rank-one
factorization at beta zero. No link count or per-link worst-case bound. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_zero_fullLinkResidual_rankOne
    (H N : ℕ) (hN : 0 < N)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f -
        pairHaarTransportedGroundStateSpatialLinkProjection
          H N hN 0 (by norm_num) e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)‖ ^ 2) =
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f) ^ 2 *
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) -
          pairHaarTransportedGroundStateSpatialLinkProjection
            H N hN 0 (by norm_num) e
            (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
              (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N))‖ ^ 2 := by
  classical
  calc
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f -
        pairHaarTransportedGroundStateSpatialLinkProjection
          H N hN 0 (by norm_num) e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)‖ ^ 2) =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        (inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f) ^ 2 *
        ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) -
          pairHaarTransportedGroundStateSpatialLinkProjection
            H N hN 0 (by norm_num) e
            (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
              (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N))‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro e _he
        exact normalizedPhysicalOneSlabPairHaarReceiver_zero_linkResidual_sq_rankOne
          H N hN f e
    _ = _ := by rw [Finset.mul_sum]

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
