import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentVacuumReceiverDirichletLeibniz
import Mathlib.Tactic

/-!
# Actual frozen adjacent one-slab energy: posterior mean versus half-density

PR #5257 proves the exact Leibniz splitting and its coefficient-two
posterior resampling bound for arbitrary joint BCF products.

Here we close the missing connection back to the ORIGINAL actual adjacent
SU(2) Gram--Schmidt orbit, retaining the two different finite-volume
couplings beta(n+1) (used to evolve the orbit) and beta(n) (used for the
frozen final transfer and posterior/joint law).

For the mode-independent right factor, the original six-color initial
Dirichlet energy has the exact 1/12 link-sum normalization.  It is bounded
by two explicitly separated genuine posterior resampling energies:
  * variation of the normalized physical vacuum posterior mean, and
  * variation of the full joint half-density/output factor.

For each mode-dependent left factor, the ORIGINAL frozen left one-link
orthogonal residual receives the analogous half-resampling estimate.

The supremum norms on both coefficients are deliberately retained and
may depend on volume.  This theorem is not a volume-uniform Poincare
bound, nor does it discard output drift, identify covariance with L2
coordinates, or assume strict locality at a positive orbit depth.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3FrozenActualLeibnizTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3FrozenActualLeibnizCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3FrozenActualLeibnizSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3FrozenActualLeibnizMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3FrozenActualLeibnizBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3FrozenActualLeibnizSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "W" =>
  normalizedPhysicalOneSlabJointHalfDensityWeightBCF
    Hn 2 Pos (beta n) (hbeta n)
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "MRight" =>
  normalizedPhysicalOneSlabVacuumMeanJointBCF
    Hn 2 Pos (beta n) (hbeta n) (RightFactor n r)
local notation "Frozen" =>
  physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "PLeft" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
    Hn 2 Pos (beta n) (hbeta n)

/-- The mode-independent common-right BCF in the original one-input
Dirichlet receiver is literally the product W*MRight on the actual
frozen joint probability carrier. -/
theorem fineOrbitCommonRightBCF_eq_jointReceiverProductBCF :
    fineOrbitCommonRightBCF
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r =
      normalizedPhysicalOneSlabJointReceiverProductBCF
        Hn 2 Pos (beta n) (hbeta n) (RightFactor n r) := by
  apply BoundedContinuousFunction.ext
  intro z
  rw [fineOrbitCommonRightBCF_apply_eq_jointHalfDensityReceiver
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r z]
  exact
    (normalizedPhysicalOneSlabJointReceiverProductBCF_apply
      Hn 2 Pos (beta n) (hbeta n) (RightFactor n r) z).symm

/-- The mode-dependent seed-right BCF in the ORIGINAL left-link residual
is literally W*MLeft for the corresponding evolved mode. -/
theorem physicalYangMillsSU2AdjacentFineSeedRightBCF_eq_jointReceiverProductBCF
    (k : Fin 3) :
    physicalYangMillsSU2AdjacentFineSeedRightBCF
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k =
      normalizedPhysicalOneSlabJointReceiverProductBCF
        Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k) := by
  apply BoundedContinuousFunction.ext
  intro z
  rw [physicalYangMillsSU2AdjacentFineSeedRightBCF_apply_eq_jointHalfDensityReceiver
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r k z]
  exact
    (normalizedPhysicalOneSlabJointReceiverProductBCF_apply
      Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k) z).symm

/-- The unchanged initial frozen Dirichlet energy is bounded by the
SEPARATED posterior-mean and half-density resampling energies, with the
original 1/12 link-sum factor still present and no extra link count. -/
theorem fineFrozenInitialEnergy_le_posteriorMean_add_halfDensity_resampling
    (k : Fin 3) :
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n)
        (Frozen n r k) ≤
      (1 / 12 : ℝ) * ∑ e : Link,
        ((2 * ‖W‖ ^ 2) *
          posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
            e MRight +
        (2 * ‖MRight‖ ^ 2) *
          posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
            e W) := by
  have hOriginal :=
    fineFrozenInitialEnergy_le_commonRightResampling
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  rw [fineOrbitCommonRightBCF_eq_jointReceiverProductBCF
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r] at hOriginal
  have hEach (e : Link) :
      posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
          e (W * MRight) ≤
        (2 * ‖W‖ ^ 2) *
          posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
            e MRight +
        (2 * ‖MRight‖ ^ 2) *
          posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
            e W := by
    exact
      posteriorResamplingEnergy_mul_le_two
        Hn 2 Pos (beta n) (hbeta n) e W MRight
  have hSum :
      (∑ e : Link,
          posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
            e (W * MRight)) ≤
        ∑ e : Link,
          ((2 * ‖W‖ ^ 2) *
            posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
              e MRight +
          (2 * ‖MRight‖ ^ 2) *
            posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
              e W) := by
    apply Finset.sum_le_sum
    intro e _he
    exact hEach e
  have hScaled :=
    mul_le_mul_of_nonneg_left hSum (by norm_num : (0 : ℝ) ≤ 1 / 12)
  change
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n)
        (Frozen n r k) ≤
      (1 / 12 : ℝ) * ∑ e : Link,
        posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
          e (W * MRight) at hOriginal
  exact hOriginal.trans hScaled

/-- Every ORIGINAL frozen left one-link residual obeys the analogous
two-component split for its own mode-dependent seed-right receiver. -/
theorem fineFrozenLeftSpatialLinkResidual_sq_le_posteriorMean_add_halfDensity
    (k : Fin 3) (e : Link) :
    ‖Frozen n r k - PLeft e (Frozen n r k)‖ ^ 2 ≤
      (1 / 2 : ℝ) *
        ((2 * ‖W‖ ^ 2) *
          posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n) e
            (normalizedPhysicalOneSlabVacuumMeanJointBCF
              Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k)) +
        (2 * ‖normalizedPhysicalOneSlabVacuumMeanJointBCF
              Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k)‖ ^ 2) *
          posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n) e W) := by
  let ML :=
    normalizedPhysicalOneSlabVacuumMeanJointBCF
      Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k)
  have hOriginal :=
    physicalYangMillsSU2AdjacentFineFrozenStep_leftSpatialLinkResidual_sq_le_half_seedRightResampling
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k e
  rw [physicalYangMillsSU2AdjacentFineSeedRightBCF_eq_jointReceiverProductBCF
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r k] at hOriginal
  have hEach :
      posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
          e (W * ML) ≤
        (2 * ‖W‖ ^ 2) *
          posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n) e ML +
        (2 * ‖ML‖ ^ 2) *
          posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n) e W :=
    posteriorResamplingEnergy_mul_le_two
      Hn 2 Pos (beta n) (hbeta n) e W ML
  have hScaled :=
    mul_le_mul_of_nonneg_left hEach (by norm_num : (0 : ℝ) ≤ 1 / 2)
  change
    ‖Frozen n r k - PLeft e (Frozen n r k)‖ ^ 2 ≤
      (1 / 2 : ℝ) *
        posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
          e (W * ML) at hOriginal
  exact hOriginal.trans hScaled

end ActualAdjacentOrbit

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
