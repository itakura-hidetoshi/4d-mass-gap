import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentActualFrozenPairHaarPosteriorFiberEnergy
import Mathlib.Tactic

/-!
# P4: pair-Haar posterior projection norm loss, without Dobrushin

PR #5266 expresses the ORIGINAL frozen adjacent Dirichlet receivers as
literal posterior-fiber square integrals against the true pair-Haar measure.

Here we use the Hilbert projection Pythagorean identity already established
for the original joint conditional expectation.  Since the exact
half-density transport U is an isometric equivalence, its conjugate

  Q_e = U.symm ∘ P_e ∘ U

preserves the projection-norm loss.  Consequently, for the actual complete
physical pair-Haar receiver v_f,

  integral (v_f - sqrt(rho_joint) * posteriorMean_e(W*M_f))^2
    = ||v_f||^2 - ||Q_e v_f||^2.

This identifies a direct non-Dobrushin route for an eventual volume-uniform
bound: control the SUM of genuine projection losses for the actual orbit,
rather than bounding each link by its individual unit-norm budget.
No new Dobrushin estimate, locality assumption, hard support, arbitrary
product approximation, or volume-uniform full-link bound is asserted.
The signed source, output drift, original endpoint swap and normalized
physical transfer are unchanged.  The orbit uses beta(n+1), whereas its
frozen posterior law continues to use beta(n).
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4PairHaarLossTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p4PairHaarLossCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p4PairHaarLossSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p4PairHaarLossMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p4PairHaarLossBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p4PairHaarLossSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p4PairHaarLossJointProbability
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
    H N hN beta hbeta

namespace GroundStatePosteriorJoint

/-- The genuine transported one-link projection is still orthogonal:
the full signed physical pair-Haar receiver loses exactly the squared norm
of its transported posterior projection.  This is not a covariance bound. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_projectionResidual_sq_eq_normLoss
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
      pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f)‖ ^ 2 =
      ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f‖ ^ 2 -
      ‖pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f)‖ ^ 2 := by
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H N hN beta hbeta
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta e
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f
  let q := pairHaarTransportedGroundStateSpatialLinkProjection
    H N hN beta hbeta e v
  let F := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
  have hCarrier :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
          H N hN beta hbeta F = U v := by
    change BoundedContinuousFunction.toLp
      2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)
      ℝ F = U v
    exact normalizedPhysicalOneSlabJointReceiverProductBCF_toLp_eq_pairHaarReceiver
      H N hN beta hbeta f
  have hP : P (U v) = U q := by
    change P (U v) = U (U.symm (P (U v)))
    rw [LinearIsometryEquiv.apply_symm_apply]
  have hV : ‖U v‖ = ‖v‖ := U.norm_map _
  have hQ : ‖P (U v)‖ = ‖q‖ := by
    rw [hP]
    exact U.norm_map _
  have hLoss :=
    posteriorResamplingEnergy_eq_two_jointL2_projectionLoss
      H N hN beta hbeta e F
  rw [hCarrier] at hLoss
  change posteriorResamplingEnergy H N hN beta hbeta e F =
      2 * (‖U v‖ ^ 2 - ‖P (U v)‖ ^ 2) at hLoss
  rw [hV, hQ] at hLoss
  have hExact :=
    normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_eq_two_pairHaarResidual
      H N hN beta hbeta f e
  change posteriorResamplingEnergy H N hN beta hbeta e F =
      2 * ‖v - q‖ ^ 2 at hExact
  have hResult : ‖v - q‖ ^ 2 = ‖v‖ ^ 2 - ‖q‖ ^ 2 := by
    linarith
  exact hResult

/-- Concrete weighted posterior-fiber integral equals the genuine
pair-Haar Hilbert projection norm loss.  The density factor and the
posterior mean are the original, unmodified frozen-joint ones. -/
theorem normalizedPhysicalOneSlabJointReceiverProductBCF_pairHaar_fiber_integral_eq_normLoss
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∫ z,
      (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f z -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
          H N hN beta hbeta z *
        posteriorMean H N hN beta hbeta e
          (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) z) ^ 2
      ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) =
      ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f‖ ^ 2 -
      ‖pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f)‖ ^ 2 := by
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f
  let q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e v
  have hFiber :=
    normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_eq_pairHaar_posteriorFiber_integral
      H N hN beta hbeta f e
  have hResidual :=
    normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_eq_two_pairHaarResidual
      H N hN beta hbeta f e
  have hNormLoss :=
    normalizedPhysicalOneSlabPairHaarReceiver_projectionResidual_sq_eq_normLoss
      H N hN beta hbeta f e
  change ‖v - q‖ ^ 2 = ‖v‖ ^ 2 - ‖q‖ ^ 2 at hNormLoss
  change posteriorResamplingEnergy H N hN beta hbeta e
      (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) =
    2 * ‖v - q‖ ^ 2 at hResidual
  linarith

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Pair" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "muP" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2
local notation "SqrtJ" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
    Hn 2 Pos (beta n) (hbeta n)
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "VRight" =>
  normalizedPhysicalOneSlabPairHaarReceiver
    Hn 2 Pos (beta n) (hbeta n) (RightFactor n r)
local notation "Q" =>
  pairHaarTransportedGroundStateSpatialLinkProjection
    Hn 2 Pos (beta n) (hbeta n)
local notation "Frozen" =>
  physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "PLeft" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
    Hn 2 Pos (beta n) (hbeta n)

/-- The ORIGINAL frozen six-color initial energy is controlled by the
SUM OF EXACT PAIR-HAAR PROJECTION LOSSES of the actual common-right orbit
factor, not by the cardinality of the lattice times a one-link budget. -/
theorem fineFrozenInitialEnergy_le_pairHaar_projectionNormLoss
    (k : Fin 3) :
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n)
        (Frozen n r k) ≤
      (1 / 6 : ℝ) * ∑ e : Link,
        (‖VRight‖ ^ 2 - ‖Q e VRight‖ ^ 2) := by
  have hOriginal :=
    fineFrozenInitialEnergy_le_pairHaar_posteriorFiber_integral
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  calc
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n)
        (Frozen n r k) ≤
      (1 / 6 : ℝ) * ∑ e : Link,
        ∫ z : Pair,
          (VRight z - SqrtJ z *
            posteriorMean Hn 2 Pos (beta n) (hbeta n) e
              (normalizedPhysicalOneSlabJointReceiverProductBCF
                Hn 2 Pos (beta n) (hbeta n) (RightFactor n r)) z) ^ 2
          ∂muP := hOriginal
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro e _he
      exact
        normalizedPhysicalOneSlabJointReceiverProductBCF_pairHaar_fiber_integral_eq_normLoss
          Hn 2 Pos (beta n) (hbeta n) (RightFactor n r) e

/-- The actual mode-dependent original left one-link frozen residual
has the corresponding exact transported loss bound, without replacing
its physical receiver with a generic mode or dropping source signs. -/
theorem fineFrozenLeftSpatialLinkResidual_sq_le_pairHaar_projectionNormLoss
    (k : Fin 3) (e : Link) :
    ‖Frozen n r k - PLeft e (Frozen n r k)‖ ^ 2 ≤
      ‖normalizedPhysicalOneSlabPairHaarReceiver
          Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k)‖ ^ 2 -
      ‖Q e (normalizedPhysicalOneSlabPairHaarReceiver
          Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k))‖ ^ 2 := by
  have hOriginal :=
    fineFrozenLeftSpatialLinkResidual_sq_le_pairHaar_posteriorFiber_integral
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k e
  calc
    ‖Frozen n r k - PLeft e (Frozen n r k)‖ ^ 2 ≤
      ∫ z : Pair,
        (normalizedPhysicalOneSlabPairHaarReceiver
            Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k) z -
          SqrtJ z *
            posteriorMean Hn 2 Pos (beta n) (hbeta n) e
              (normalizedPhysicalOneSlabJointReceiverProductBCF
                Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k)) z) ^ 2
        ∂muP := hOriginal
    _ = _ := by
      exact
        normalizedPhysicalOneSlabJointReceiverProductBCF_pairHaar_fiber_integral_eq_normLoss
          Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k) e

end ActualAdjacentOrbit
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
