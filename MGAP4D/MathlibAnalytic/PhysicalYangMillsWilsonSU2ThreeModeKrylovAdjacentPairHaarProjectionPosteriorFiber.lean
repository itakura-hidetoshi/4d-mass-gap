import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPosteriorResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointCondExpIdentification
import Mathlib.Tactic

/-!
# Literal posterior-fiber representative of the transported pair-Haar projection

PR #5263 defines the true pair-Haar projection

  Q_e = U^{-1} P_e U

by conjugating the original joint one-link CondExpL2 projection with
the genuine half-density isometric equivalence U.

This file makes its action concrete on the actual bounded-continuous
joint core.  For a joint BCF F and its original joint-L2 class [F],

  Q_e(U^{-1}[F])(A,B)
    = sqrt(rho_joint(A,B)) *
        integral F(A, B[e <- g]) d posterior_(A,B,e)(g)

holds pair-Haar almost everywhere.  Both the density and conditional
law are the ORIGINAL ones.  There is no arbitrary new conditional law,
no independent product-measure approximation and no claim of pointwise
equality between L2 representatives.

Specializing to the actual normalized physical frozen receiver W*M_f
identifies the previously abstract projection from #5263 with the
literal posterior fiber integral of the COMPLETE signed-output
half-density receiver.  We then express its pair-Haar projection residual
and exact energy as the integral of the square of that explicit difference.

The normalization lambda^{-1}, source sign, full output drift,
beta(n+1)/beta(n) mismatch and exact joint measure are not changed.
These are identities, not unproved smallness or volume-uniform gap claims.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3PairHaarFiberTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3PairHaarFiberCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3PairHaarFiberSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3PairHaarFiberMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3PairHaarFiberBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3PairHaarFiberSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p3PairHaarFiberJointProbability
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
    H N hN beta hbeta

namespace GroundStatePosteriorJoint

/-- The transported genuine projection has the explicit original
posterior-kernel fiber mean as its pair-Haar a.e. representative, multiplied
by the ORIGINAL joint square-root density at the un-updated endpoint. -/
theorem pairHaarTransportedGroundStateSpatialLinkProjection_BCF_coeFn
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta).symm
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
            H N hN beta hbeta F)) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      fun z =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
            H N hN beta hbeta z *
          posteriorMean H N hN beta hbeta e F z := by
  let muP := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let muJ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H N hN beta hbeta
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta e
  let x := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
    H N hN beta hbeta F
  have hQ :
      pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (U.symm x) = U.symm (P x) := by
    change U.symm (P (U (U.symm x))) = U.symm (P x)
    rw [LinearIsometryEquiv.apply_symm_apply]
  have hMeanJoint :
      (fun z => (P x) z) =ᵐ[muJ]
        posteriorMean H N hN beta hbeta e F := by
    simpa only [
      jointBCF_boundedConcreteL2_eq_standardRepresentative
    ] using
      (condExpL2_coeFn_eq_posteriorMean
        H N hN beta hbeta e F
        F.continuous.stronglyMeasurable ‖F‖ F.norm_coe_le_norm)
  have hMuPtoJ : muP ≪ muJ := by
    simpa [muP, muJ] using
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure_absolutelyContinuous_groundStateJointMeasure
        H N hN beta hbeta
  have hMeanPair := hMuPtoJ.ae_eq hMeanJoint
  have hInv :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarL2_coeFn
      H N hN beta hbeta (P x)
  rw [hQ]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv_symm_apply
      H N hN beta hbeta (P x)
  ]
  filter_upwards [hInv, hMeanPair] with z hV hMean
  rw [hV]
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
        H N hN beta hbeta z * (P x) z =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
        H N hN beta hbeta z * posteriorMean H N hN beta hbeta e F z
  rw [hMean]

/-- The actual physical frozen receiver, after the half-density
transport, uses exactly that posterior fiber action on the true
pair-Haar carrier. -/
theorem pairHaarTransportedGroundStateSpatialLinkProjection_physicalReceiver_coeFn
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      fun z =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
            H N hN beta hbeta z *
          posteriorMean H N hN beta hbeta e
            (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) z := by
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H N hN beta hbeta
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f
  let F := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
  have hCarrier :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
        H N hN beta hbeta F = U v := by
    change BoundedContinuousFunction.toLp
      2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)
      ℝ F = U v
    exact
      normalizedPhysicalOneSlabJointReceiverProductBCF_toLp_eq_pairHaarReceiver
        H N hN beta hbeta f
  have hUndo :
      U.symm
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
            H N hN beta hbeta F) = v := by
    rw [hCarrier]
    exact U.symm_apply_apply v
  have hFormula :=
    pairHaarTransportedGroundStateSpatialLinkProjection_BCF_coeFn
      H N hN beta hbeta e F
  rw [hUndo] at hFormula
  exact hFormula

/-- The exact pair-Haar projection residual is the difference between
the physical pair-Haar receiver and the square-root-density-weighted
ORIGINAL posterior fiber mean of the full joint receiver. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_projectionResidual_coeFn
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
      pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f)) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      fun z =>
        normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f z -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
            H N hN beta hbeta z *
          posteriorMean H N hN beta hbeta e
            (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) z := by
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f
  let q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e v
  have hQ :
      q =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
        fun z =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
              H N hN beta hbeta z *
            posteriorMean H N hN beta hbeta e
              (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) z := by
    simpa only [q, v] using
      pairHaarTransportedGroundStateSpatialLinkProjection_physicalReceiver_coeFn
        H N hN beta hbeta f e
  filter_upwards [Lp.coeFn_sub v q, hQ] with z hSub hMean
  rw [hSub]
  change
    v z - q z =
      v z -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
          H N hN beta hbeta z *
        posteriorMean H N hN beta hbeta e
          (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) z
  rw [hMean]

/-- Literal integral formula for the original frozen joint resampling
energy on the TRUE pair-Haar measure, with the weighted posterior mean
and its half-density retained at both endpoints. -/
theorem normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_eq_pairHaar_posteriorFiber_integral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    posteriorResamplingEnergy H N hN beta hbeta e
        (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) =
      2 * ∫ z,
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f z -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
            H N hN beta hbeta z *
          posteriorMean H N hN beta hbeta e
            (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) z) ^ 2
        ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N := by
  let muP := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f
  let q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e v
  let r : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N := v - q
  have hRep :
      r =ᵐ[muP] fun z =>
        v z -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
            H N hN beta hbeta z *
          posteriorMean H N hN beta hbeta e
            (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) z := by
    simpa only [r, v, q, muP] using
      (normalizedPhysicalOneSlabPairHaarReceiver_projectionResidual_coeFn
        H N hN beta hbeta f e)
  have hSq :
      ‖r‖ ^ 2 =
        ∫ z,
          (v z -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
              H N hN beta hbeta z *
            posteriorMean H N hN beta hbeta e
              (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) z) ^ 2
          ∂muP := by
    rw [realL2_norm_sq_eq_integral_norm_sq r]
    apply integral_congr_ae
    filter_upwards [hRep] with z hz
    rw [hz]
    simp only [Real.norm_eq_abs, sq_abs]
  have hExact :=
    normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_eq_two_pairHaarResidual
      H N hN beta hbeta f e
  change
    posteriorResamplingEnergy H N hN beta hbeta e
        (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) =
      2 * ‖r‖ ^ 2 at hExact
  rw [hExact, hSq]

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
