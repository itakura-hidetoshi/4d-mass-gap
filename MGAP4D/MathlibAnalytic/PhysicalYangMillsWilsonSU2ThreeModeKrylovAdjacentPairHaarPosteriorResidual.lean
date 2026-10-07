import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFrozenHalfDensityResamplingL2Budget
import Mathlib.Tactic

/-!
# Exact pair-Haar residual of the genuine frozen posterior link projection

PR #5261 identifies the complete original joint half-density receiver with
the actual pair-Haar L2 vector

  v_f := lambda^(-1) * ((S f) o snd),

transported by the genuine pair-Haar-to-ground-state-joint isometry U.
PR #5262 uses only the upper bound E_e <= 2 ||v_f||².

Here we retain the exact projection defect.  If P_e is the ORIGINAL
ground-state-joint CondExpL2 one-link projection, define its conjugate on
the actual pair-Haar carrier by

  Q_e(v) := U^(-1) (P_e (U v)).

The literal posterior resampling energy is exactly

  E_e(W M_f) = 2 ||v_f - Q_e(v_f)||².

The same identity converts the existing common-right frozen 1/12 energy
estimate and the mode-dependent left-link residual estimate into
pair-Haar projected defects.  In particular, the output drift, lambda,
genuine posterior law, beta(n)/beta(n+1) distinction and exact endpoint
swap are retained.  No volume-uniform gap or covariance/L2-coordinate
identification is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3PairHaarPosteriorResidualTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3PairHaarPosteriorResidualCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3PairHaarPosteriorResidualSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3PairHaarPosteriorResidualMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3PairHaarPosteriorResidualBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3PairHaarPosteriorResidualSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p3PairHaarPosteriorResidualSliceHaarProbability (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance p3PairHaarPosteriorResidualJointProbability
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
    H N hN beta hbeta

namespace GroundStatePosteriorJoint

/-- The actual physical one-slab normalized transfer image, with the
mandatory extra lambda inverse, pulled back along the right coordinate
of the original pair-Haar product measure. -/
noncomputable def normalizedPhysicalOneSlabPairHaarReceiver
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ •
    Lp.compMeasurePreserving Prod.snd
      (spatialSlicePairHaar_snd_measurePreserving H N)
      ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta f :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- Conjugation of the original joint conditional expectation by the actual
pair-Haar / ground-state-joint half-density isometric equivalence.
No new conditional probability law is defined. -/
noncomputable def pairHaarTransportedGroundStateSpatialLinkProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (v : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H N hN beta hbeta).symm
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta e
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
        H N hN beta hbeta v))

/-- The FULL original joint receiver is precisely the half-density
transport of its named physical pair-Haar vector. -/
theorem normalizedPhysicalOneSlabJointReceiverProductBCF_toLp_eq_pairHaarReceiver
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)
        ℝ
        (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
        H N hN beta hbeta
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f) := by
  simpa only [normalizedPhysicalOneSlabPairHaarReceiver] using
    normalizedPhysicalOneSlabJointReceiverProductBCF_toLp_eq_halfDensityHaarRight
      H N hN beta hbeta f

/-- Exact signed receiver resampling energy as the pair-Haar norm of the
conjugated conditional-expectation residual.  This improves the mere
upper bound 2*lambda^(-2)||f||² without changing the original law. -/
theorem normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_eq_two_pairHaarResidual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    posteriorResamplingEnergy H N hN beta hbeta e
        (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) =
      2 *
        ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
          pairHaarTransportedGroundStateSpatialLinkProjection
            H N hN beta hbeta e
            (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f)‖ ^ 2 := by
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H N hN beta hbeta
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta e
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f
  let F := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
  have hCarrier :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
          H N hN beta hbeta F = U v := by
    change
      BoundedContinuousFunction.toLp 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)
        ℝ F = U v
    exact normalizedPhysicalOneSlabJointReceiverProductBCF_toLp_eq_pairHaarReceiver
      H N hN beta hbeta f
  have hExact :=
    posteriorInitialResidual_sq_eq_half_resampling
      H N hN beta hbeta e F
  rw [hCarrier] at hExact
  have hNorm :
      ‖U v - P (U v)‖ =
        ‖v - U.symm (P (U v))‖ := by
    calc
      ‖U v - P (U v)‖ =
        ‖U (v - U.symm (P (U v)))‖ := by
          rw [map_sub, LinearIsometryEquiv.apply_symm_apply]
      _ = ‖v - U.symm (P (U v))‖ := U.norm_map _
  rw [hNorm] at hExact
  change
    ‖v - U.symm (P (U v))‖ ^ 2 =
      (1 / 2 : ℝ) *
        posteriorResamplingEnergy H N hN beta hbeta e F at hExact
  change
    posteriorResamplingEnergy H N hN beta hbeta e F =
      2 * ‖v - U.symm (P (U v))‖ ^ 2
  linarith

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "Frozen" =>
  physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "PLeft" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
    Hn 2 Pos (beta n) (hbeta n)
local notation "Q" =>
  pairHaarTransportedGroundStateSpatialLinkProjection Hn 2 Pos (beta n) (hbeta n)

/-- The original six-color frozen initial energy retains its exact 1/12
link sum and is controlled by the full pair-Haar projection defects
of the unchanged common right input. -/
theorem fineFrozenInitialEnergy_le_pairHaarRightProjectionResiduals
    (k : Fin 3) :
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n)
        (Frozen n r k) ≤
      (1 / 12 : ℝ) * ∑ e : Link,
        2 *
          ‖normalizedPhysicalOneSlabPairHaarReceiver
              Hn 2 Pos (beta n) (hbeta n) (RightFactor n r) -
            Q e
              (normalizedPhysicalOneSlabPairHaarReceiver
                Hn 2 Pos (beta n) (hbeta n) (RightFactor n r))‖ ^ 2 := by
  have hOriginal :=
    fineFrozenInitialEnergy_le_commonRightResampling
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  rw [fineOrbitCommonRightBCF_eq_jointReceiverProductBCF
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r] at hOriginal
  calc
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n)
        (Frozen n r k) ≤
      (1 / 12 : ℝ) * ∑ e : Link,
        posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
          e
          (normalizedPhysicalOneSlabJointReceiverProductBCF
            Hn 2 Pos (beta n) (hbeta n) (RightFactor n r)) := hOriginal
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro e _he
      exact
        normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_eq_two_pairHaarResidual
          Hn 2 Pos (beta n) (hbeta n) (RightFactor n r) e

/-- Each ORIGINAL left one-link orthogonal residual is bounded by the
corresponding transported pair-Haar projection defect of the evolved
left physical mode, without replacing its sign or the endpoint swap. -/
theorem fineFrozenLeftSpatialLinkResidual_sq_le_pairHaarLeftProjectionResidual
    (k : Fin 3) (e : Link) :
    ‖Frozen n r k - PLeft e (Frozen n r k)‖ ^ 2 ≤
      ‖normalizedPhysicalOneSlabPairHaarReceiver
          Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k) -
        Q e
          (normalizedPhysicalOneSlabPairHaarReceiver
            Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k))‖ ^ 2 := by
  have hOriginal :=
    physicalYangMillsSU2AdjacentFineFrozenStep_leftSpatialLinkResidual_sq_le_half_seedRightResampling
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k e
  rw [physicalYangMillsSU2AdjacentFineSeedRightBCF_eq_jointReceiverProductBCF
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r k] at hOriginal
  calc
    ‖Frozen n r k - PLeft e (Frozen n r k)‖ ^ 2 ≤
      (1 / 2 : ℝ) *
        posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n) e
          (normalizedPhysicalOneSlabJointReceiverProductBCF
            Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k)) := hOriginal
    _ = _ := by
      rw [normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_eq_two_pairHaarResidual
        Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k) e]
      ring

end ActualAdjacentOrbit

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
