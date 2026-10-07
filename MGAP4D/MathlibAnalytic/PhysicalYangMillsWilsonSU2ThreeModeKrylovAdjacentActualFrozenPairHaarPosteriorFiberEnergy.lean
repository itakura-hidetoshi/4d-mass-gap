import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarProjectionPosteriorFiber
import Mathlib.Tactic

/-!
# Actual adjacent frozen Dirichlet energy as literal pair-Haar posterior fibers

PR #5265 gives the concrete pair-Haar-a.e. posterior-fiber expression
for the genuine conditional-expectation projection transported through
the exact ground-state joint half-density.  Its energy identity retains

  v_f(z) - sqrt(rho_joint(z)) * posteriorMean_e(W*M_f)(z)

as the original signed pair-Haar residual of the complete frozen
one-slab receiver, not a surrogate or raw seed covariance.

This file substitutes that EXACT fiber formula into the original
actual adjacent orbit's two distinct energy receivers:

* The six-color initial Dirichlet energy, with its exact 1/12 link-sum
  normalization (equivalently 1/6 times the pair-Haar squared-integral
  sum) and the mode-independent right physical factor;
* Each ORIGINAL left one-link projection residual, with the mode-dependent
  evolved left physical factor and exact half-resampling normalization.

All measures, half-density denominators and source/output signs are
those of the existing formal construction.  Orbit evolution uses
beta(n+1), the frozen posterior laws use beta(n), and r=0 remains valid.

No unwarranted support bound at positive depth, no new conditional law,
no volume-uniform upper bound on the link sum and no continuum
Yang--Mills mass-gap theorem is claimed here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3ActualFrozenPairHaarFiberTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3ActualFrozenPairHaarFiberCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3ActualFrozenPairHaarFiberSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3ActualFrozenPairHaarFiberMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3ActualFrozenPairHaarFiberBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3ActualFrozenPairHaarFiberSpatialLinkFintype (H : ℕ) :
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
local notation "FRight" =>
  normalizedPhysicalOneSlabJointReceiverProductBCF
    Hn 2 Pos (beta n) (hbeta n) (RightFactor n r)
local notation "Frozen" =>
  physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "PLeft" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
    Hn 2 Pos (beta n) (hbeta n)

/-- The ORIGINAL frozen six-color initial energy is dominated by the
explicit genuine pair-Haar posterior-fiber residual of the common-right
evolved factor.  The canonical 1/12 link-sum survives EXACTLY as 1/6
after substituting E_e(F) = 2 * integral of the squared residual. -/
theorem fineFrozenInitialEnergy_le_pairHaar_posteriorFiber_integral
    (k : Fin 3) :
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n)
        (Frozen n r k) ≤
      (1 / 6 : ℝ) * ∑ e : Link,
        ∫ z : Pair,
          (VRight z - SqrtJ z *
            posteriorMean Hn 2 Pos (beta n) (hbeta n) e FRight z) ^ 2
          ∂muP := by
  have hOriginal :=
    fineFrozenInitialEnergy_le_commonRightResampling
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  rw [fineOrbitCommonRightBCF_eq_jointReceiverProductBCF
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r] at hOriginal
  have hFiberSum :
      (∑ e : Link,
        posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
          e FRight) =
      ∑ e : Link,
        2 * ∫ z : Pair,
          (VRight z - SqrtJ z *
            posteriorMean Hn 2 Pos (beta n) (hbeta n) e FRight z) ^ 2
          ∂muP := by
    apply Finset.sum_congr rfl
    intro e _he
    exact
      normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_eq_pairHaar_posteriorFiber_integral
        Hn 2 Pos (beta n) (hbeta n) (RightFactor n r) e
  calc
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n)
        (Frozen n r k) ≤
      (1 / 12 : ℝ) * ∑ e : Link,
        posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
          e FRight := hOriginal
    _ =
      (1 / 12 : ℝ) * ∑ e : Link,
        2 * ∫ z : Pair,
          (VRight z - SqrtJ z *
            posteriorMean Hn 2 Pos (beta n) (hbeta n) e FRight z) ^ 2
          ∂muP := by rw [hFiberSum]
    _ =
      (1 / 6 : ℝ) * ∑ e : Link,
        ∫ z : Pair,
          (VRight z - SqrtJ z *
            posteriorMean Hn 2 Pos (beta n) (hbeta n) e FRight z) ^ 2
          ∂muP := by
      rw [← Finset.mul_sum]
      ring

/-- The ORIGINAL frozen LEFT one-link Hilbert residual is controlled by the
genuine pair-Haar posterior fiber residual of the corresponding evolved
mode-dependent left factor.  The 1/2 times 2 normalization cancels
exactly, without dropping output drift or changing the endpoint swap. -/
theorem fineFrozenLeftSpatialLinkResidual_sq_le_pairHaar_posteriorFiber_integral
    (k : Fin 3) (e : Link) :
    ‖Frozen n r k - PLeft e (Frozen n r k)‖ ^ 2 ≤
      ∫ z : Pair,
        (normalizedPhysicalOneSlabPairHaarReceiver
            Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k) z -
          SqrtJ z *
            posteriorMean Hn 2 Pos (beta n) (hbeta n) e
              (normalizedPhysicalOneSlabJointReceiverProductBCF
                Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k)) z) ^ 2
        ∂muP := by
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
    _ = (1 / 2 : ℝ) *
        (2 * ∫ z : Pair,
          (normalizedPhysicalOneSlabPairHaarReceiver
              Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k) z -
            SqrtJ z *
              posteriorMean Hn 2 Pos (beta n) (hbeta n) e
                (normalizedPhysicalOneSlabJointReceiverProductBCF
                  Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k)) z) ^ 2
          ∂muP) := by
      rw [
        normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_eq_pairHaar_posteriorFiber_integral
          Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k) e
      ]
    _ = _ := by ring

end ActualAdjacentOrbit
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
