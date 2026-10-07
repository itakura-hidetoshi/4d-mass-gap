import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGroundStateJointPairSwap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentCommonRightResamplingReceiver
import Mathlib.Tactic

/-!
# Seed-right posterior resampling after endpoint swap

PR #5243 moves the actual mode-dependent adjacent SU(2) orbit factor from the
first endpoint to the second endpoint without loss, and identifies the original
left one-link residual with the ordinary right one-link residual of the swapped
frozen vector.

This file turns that exact conjugacy into the corresponding signed posterior
Dirichlet receiver.

For the swapped pair input

  commonRightFactor ⊗ modeDependentSeedFactor,

the original signed one-link transfer defect factors exactly as

  commonAmplitude * seedRightDefect.

The common amplitude is pointwise bounded by one: the constant starting vector
has norm one and every normalized one-slice transfer has operator norm one.
Therefore the original left one-link residual of the unswapped frozen vector is
bounded by one half of the posterior resampling energy of one bounded-continuous
observable carrying the mode-dependent seed factor on the right endpoint.

The exact factor 1/2 is the pre-existing posterior resampling identity.  No
posterior covariance is identified with an L2 coordinate norm, no hard support
is asserted for positive orbit depth, and the beta_(n+1) orbit versus beta_n
frozen-transfer distinction is unchanged.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3SwappedSeedRightTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3SwappedSeedRightCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3SwappedSeedRightSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3SwappedSeedRightMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3SwappedSeedRightBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3SwappedSeedRightSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "GaugeT" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "SliceL2" =>
  Lp ℝ 2
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure Hn 2)
local notation "PairL2" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 Hn 2
local notation "muJ" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    Hn 2 Pos (beta n) (hbeta n)
local notation "Nu" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
    Hn 2 Pos (beta n) (hbeta n)
local notation "BCFRep" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
    Hn 2 Pos (beta n) (hbeta n)
local notation "PRight" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
    Hn 2 Pos (beta n) (hbeta n)
local notation "PLeft" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
    Hn 2 Pos (beta n) (hbeta n)
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
    Hn 2 Pos (beta n) (hbeta n)
local notation "SJoint" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
    Hn 2 Pos (beta n) (hbeta n)
local notation "NormTransfer" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
    Hn 2 Pos (beta n) (hbeta n)
local notation "Frozen" =>
  physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- Pair-Haar input obtained by exchanging the two exact factors of the actual
adjacent orbit.  The mode-dependent seed factor is now on the right. -/
noncomputable def physicalYangMillsSU2AdjacentFineSwappedPairInput
    (k : Fin 3) : PairL2 :=
  periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
    Hn 2 (RightFactor n r) (LeftFactor n r k)

/-- The swapped frozen joint vector is exactly the BCF representative generated
by the swapped pair-Haar input at the final frozen coupling. -/
theorem
    physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector_swap_eq_swappedBCFRep
    (k : Fin 3) :
    SJoint (Frozen n r k) =
      BCFRep
        (jointTransferBCF
          Hn 2 Pos (beta n) (hbeta n)
          (physicalYangMillsSU2AdjacentFineSwappedPairInput
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k)) := by
  rw [
    physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector_swap_eq_decomposable
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  ]
  symm
  simpa [
    physicalYangMillsSU2AdjacentFineSwappedPairInput
  ] using
    (jointTransferBCF_rep_eq
      Hn 2 Pos (beta n) (hbeta n)
      (physicalYangMillsSU2AdjacentFineSwappedPairInput
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k))

/-- Exact posterior Dirichlet identity for the original left one-link residual:
after endpoint swap it is one half of the signed resampling energy of the
swapped pair input. -/
theorem
    physicalYangMillsSU2AdjacentFineFrozenStep_leftSpatialLinkResidual_sq_eq_half_swappedResampling
    (k : Fin 3)
    (e : Link) :
    ‖Frozen n r k - PLeft e (Frozen n r k)‖ ^ 2 =
      (1 / 2 : ℝ) *
        jointTransferLinkResamplingEnergy
          Hn 2 Pos (beta n) (hbeta n)
          (physicalYangMillsSU2AdjacentFineSwappedPairInput
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k)
          e := by
  have hResidual :=
    physicalYangMillsSU2AdjacentFineFrozenStep_leftSpatialLinkResidual_norm_eq_swappedRight
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k e
  rw [hResidual]
  rw [
    physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector_swap_eq_swappedBCFRep
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  ]
  rw [
    posteriorInitialResidual_sq_eq_half_resampling
      Hn 2 Pos (beta n) (hbeta n) e
      (jointTransferBCF
        Hn 2 Pos (beta n) (hbeta n)
        (physicalYangMillsSU2AdjacentFineSwappedPairInput
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k))
  ]
  rw [← jointTransferLinkResamplingEnergy_eq
    Hn 2 Pos (beta n) (hbeta n)
    (physicalYangMillsSU2AdjacentFineSwappedPairInput
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k) e]

/-- Exact single-link defect factorization for the swapped pair input.  All
mode dependence is now carried by the right, seed-evolved factor. -/
theorem
    physicalYangMillsSU2AdjacentFineSwappedPairInput_jointTransferLinkDifference_eq
    (k : Fin 3)
    (e : Link)
    (z : Joint)
    (u : GaugeT) :
    jointTransferLinkDifference
        Hn 2 Pos (beta n) (hbeta n)
        (physicalYangMillsSU2AdjacentFineSwappedPairInput
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k)
        e z u =
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
          (RightFactor n r : SliceL2) z.1 *
        decomposableRightLinkDifferenceFactor
          Hn 2 Pos (beta n) (hbeta n)
          (LeftFactor n r k) e z u := by
  unfold physicalYangMillsSU2AdjacentFineSwappedPairInput
  exact
    jointTransferLinkDifference_physicalPairDecomposableL2_eq_left_mul_right
      Hn 2 Pos (beta n) (hbeta n)
      (RightFactor n r) (LeftFactor n r k)
      e z u

/-- Squared version of the swapped seed-right defect factorization. -/
theorem
    physicalYangMillsSU2AdjacentFineSwappedPairInput_jointTransferLinkDifference_sq_eq
    (k : Fin 3)
    (e : Link)
    (z : Joint)
    (u : GaugeT) :
    (jointTransferLinkDifference
        Hn 2 Pos (beta n) (hbeta n)
        (physicalYangMillsSU2AdjacentFineSwappedPairInput
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k)
        e z u) ^ 2 =
      (decomposableOneSliceTransferIntegral Hn 2 (beta n)
          (RightFactor n r : SliceL2) z.1) ^ 2 *
        (decomposableRightLinkDifferenceFactor
          Hn 2 Pos (beta n) (hbeta n)
          (LeftFactor n r k) e z u) ^ 2 := by
  rw [
    physicalYangMillsSU2AdjacentFineSwappedPairInput_jointTransferLinkDifference_eq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k e z u
  ]
  ring

/-- Exact resampling-energy representation after endpoint swap. -/
theorem
    physicalYangMillsSU2AdjacentFineSwappedPairInput_jointTransferLinkResamplingEnergy_eq
    (k : Fin 3)
    (e : Link) :
    jointTransferLinkResamplingEnergy
        Hn 2 Pos (beta n) (hbeta n)
        (physicalYangMillsSU2AdjacentFineSwappedPairInput
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k)
        e =
      ∫ z, ∫ u,
        (decomposableOneSliceTransferIntegral Hn 2 (beta n)
            (RightFactor n r : SliceL2) z.1) ^ 2 *
          (decomposableRightLinkDifferenceFactor
            Hn 2 Pos (beta n) (hbeta n)
            (LeftFactor n r k) e z u) ^ 2
        ∂Nu z.1 z.2 e ∂muJ := by
  unfold jointTransferLinkResamplingEnergy
  apply integral_congr_ae
  filter_upwards with z
  apply integral_congr_ae
  filter_upwards with u
  exact
    physicalYangMillsSU2AdjacentFineSwappedPairInput_jointTransferLinkDifference_sq_eq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k e z u

/-- The common first factor of the swapped input stays in the unit L2 ball. -/
theorem physicalYangMillsSU2AdjacentFinePairOrbitRightFactor_norm_le_one :
    ‖RightFactor n r‖ ≤ 1 := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      Hn 2 Pos (beta (n + 1)) (hbeta (n + 1))
  let f :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
  have hS : ‖S‖ = 1 := by
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
        Hn 2 Pos (beta (n + 1)) (hbeta (n + 1))
  have hf : ‖f‖ = 1 := by
    simpa [f] using
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm Hn 2
  change ‖(S ^ r) f‖ ≤ 1
  induction r with
  | zero =>
      simpa [hf]
  | succ m ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      calc
        ‖S ((S ^ m) f)‖ ≤ ‖S‖ * ‖(S ^ m) f‖ :=
          ContinuousLinearMap.le_opNorm S ((S ^ m) f)
        _ = ‖(S ^ m) f‖ := by rw [hS, one_mul]
        _ ≤ 1 := ih

/-- Consequently the common scalar multiplying the seed-right defect is
pointwise bounded by one in absolute value. -/
theorem
    physicalYangMillsSU2AdjacentFineSwappedCommonAmplitude_abs_le_one
    (A : Cfg) :
    |decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (RightFactor n r : SliceL2) A| ≤ 1 := by
  exact
    (decomposableOneSliceTransferIntegral_abs_le_norm
      Hn 2 Pos (beta n) (hbeta n)
      (RightFactor n r : SliceL2) A).trans
      (by
        simpa only [Submodule.norm_coe] using
          physicalYangMillsSU2AdjacentFinePairOrbitRightFactor_norm_le_one
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r)

/-- Bounded-continuous receiver whose right endpoint carries the actual
mode-dependent seed-evolved factor. -/
def physicalYangMillsSU2AdjacentFineSeedRightBCF
    (k : Fin 3) :
    BoundedContinuousFunction Joint ℝ :=
  decomposableRightOutputBCF
    Hn 2 Pos (beta n) (hbeta n)
    (LeftFactor n r k)

/-- The seed-right defect is literally the posterior one-link difference of
the seed-right bounded-continuous receiver. -/
theorem
    physicalYangMillsSU2AdjacentFineSeedRightLinkDifferenceFactor_eq_bcf_sub_update
    (k : Fin 3)
    (e : Link)
    (z : Joint)
    (u : GaugeT) :
    decomposableRightLinkDifferenceFactor
        Hn 2 Pos (beta n) (hbeta n)
        (LeftFactor n r k) e z u =
      physicalYangMillsSU2AdjacentFineSeedRightBCF
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k z -
        physicalYangMillsSU2AdjacentFineSeedRightBCF
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k
          (z.1, Function.update z.2 e u) := by
  unfold physicalYangMillsSU2AdjacentFineSeedRightBCF
  exact
    decomposableRightLinkDifferenceFactor_eq_outputBCF_sub_update
      Hn 2 Pos (beta n) (hbeta n)
      (LeftFactor n r k) e z u

/-- Pointwise seed-right receiver bound with coefficient one. -/
theorem
    physicalYangMillsSU2AdjacentFineSwappedPairInput_jointTransferLinkDifference_sq_le_seedRightBCF
    (k : Fin 3)
    (e : Link)
    (z : Joint)
    (u : GaugeT) :
    (jointTransferLinkDifference
        Hn 2 Pos (beta n) (hbeta n)
        (physicalYangMillsSU2AdjacentFineSwappedPairInput
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k)
        e z u) ^ 2 ≤
      (physicalYangMillsSU2AdjacentFineSeedRightBCF
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k z -
        physicalYangMillsSU2AdjacentFineSeedRightBCF
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k
          (z.1, Function.update z.2 e u)) ^ 2 := by
  rw [
    physicalYangMillsSU2AdjacentFineSwappedPairInput_jointTransferLinkDifference_sq_eq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k e z u,
    physicalYangMillsSU2AdjacentFineSeedRightLinkDifferenceFactor_eq_bcf_sub_update
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k e z u
  ]
  have hAbs :=
    physicalYangMillsSU2AdjacentFineSwappedCommonAmplitude_abs_le_one
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r z.1
  have hSq :
      (decomposableOneSliceTransferIntegral Hn 2 (beta n)
          (RightFactor n r : SliceL2) z.1) ^ 2 ≤ 1 := by
    have hp := pow_le_pow_left₀ (abs_nonneg _) hAbs 2
    simpa only [sq_abs, one_pow] using hp
  exact
    (mul_le_mul_of_nonneg_right hSq
      (sq_nonneg
        (physicalYangMillsSU2AdjacentFineSeedRightBCF
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k z -
          physicalYangMillsSU2AdjacentFineSeedRightBCF
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k
            (z.1, Function.update z.2 e u)))).trans_eq
      (one_mul _)

/-- The swapped signed resampling energy is controlled by the posterior
resampling energy of the mode-dependent seed-right BCF. -/
theorem
    physicalYangMillsSU2AdjacentFineSwappedPairInput_jointTransferLinkResamplingEnergy_le_seedRight
    (k : Fin 3)
    (e : Link) :
    jointTransferLinkResamplingEnergy
        Hn 2 Pos (beta n) (hbeta n)
        (physicalYangMillsSU2AdjacentFineSwappedPairInput
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k)
        e ≤
      posteriorResamplingEnergy
        Hn 2 Pos (beta n) (hbeta n) e
        (physicalYangMillsSU2AdjacentFineSeedRightBCF
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k) := by
  unfold jointTransferLinkResamplingEnergy posteriorResamplingEnergy
  apply integral_mono
  · exact
      jointTransferLinkResamplingSquare_integrable
        Hn 2 Pos (beta n) (hbeta n)
        (physicalYangMillsSU2AdjacentFineSwappedPairInput
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k)
        e
  · exact
      posteriorResamplingSquare_integrable
        Hn 2 Pos (beta n) (hbeta n) e
        (physicalYangMillsSU2AdjacentFineSeedRightBCF
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k)
  · intro z
    unfold posteriorResamplingSquare
    apply integral_mono
    · exact
        jointTransferLinkDifference_sq_posterior_integrable
          Hn 2 Pos (beta n) (hbeta n)
          (physicalYangMillsSU2AdjacentFineSwappedPairInput
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k)
          e z
    · exact
        posteriorResamplingDifferenceSquare_integrable
          Hn 2 Pos (beta n) (hbeta n) e
          (physicalYangMillsSU2AdjacentFineSeedRightBCF
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k)
          z
    · intro u
      exact
        physicalYangMillsSU2AdjacentFineSwappedPairInput_jointTransferLinkDifference_sq_le_seedRightBCF
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k e z u

/-- Main receiver: the original left one-link residual square is bounded by one
half of the mode-dependent seed-right posterior resampling energy. -/
theorem
    physicalYangMillsSU2AdjacentFineFrozenStep_leftSpatialLinkResidual_sq_le_half_seedRightResampling
    (k : Fin 3)
    (e : Link) :
    ‖Frozen n r k - PLeft e (Frozen n r k)‖ ^ 2 ≤
      (1 / 2 : ℝ) *
        posteriorResamplingEnergy
          Hn 2 Pos (beta n) (hbeta n) e
          (physicalYangMillsSU2AdjacentFineSeedRightBCF
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k) := by
  rw [
    physicalYangMillsSU2AdjacentFineFrozenStep_leftSpatialLinkResidual_sq_eq_half_swappedResampling
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k e
  ]
  exact
    mul_le_mul_of_nonneg_left
      (physicalYangMillsSU2AdjacentFineSwappedPairInput_jointTransferLinkResamplingEnergy_le_seedRight
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k e)
      (by norm_num)

end ActualAdjacentOrbit

end GroundStatePosteriorJoint

end

end MathlibAnalytic
end MGAP4D
