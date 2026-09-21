import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferOneSlabOperatorNormBetaLipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Normalized one-slab physical transfer: continuity in beta

The preceding theorem unit proves operator-norm Lipschitz continuity of the
literal finite-volume physical one-slab transfer and of its top norm.  The
spectral continuation machinery used later is centered at the fixed normalized
top point `1`, so the correct next carrier is the norm-normalized transfer.

This file packages the nonnegative Wilson coupling as the closed half-line
`Set.Ici 0`.  On that fixed parameter space the unnormalized physical
transfer is Lipschitz, its norm is continuous and strictly positive, and hence
its reciprocal is continuous.  Scalar multiplication then gives continuity of
the normalized physical transfer in operator norm.

No spectral-gap continuity, eigenvector choice, compactness argument, or
volume-uniform estimate is used here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped InnerProductSpace Topology

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

local instance normalizedOneSlabBetaContinuitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance normalizedOneSlabBetaContinuitySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance normalizedOneSlabBetaContinuitySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance normalizedOneSlabBetaContinuitySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance normalizedOneSlabBetaContinuitySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance normalizedOneSlabBetaContinuitySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The actual finite-volume physical one-slab transfer viewed as a family on
the closed nonnegative Wilson-coupling half-line. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine
    (H N : ℕ)
    (hN : 0 < N) :
    Set.Ici (0 : ℝ) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  fun beta =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta.1 beta.2

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : Set.Ici (0 : ℝ)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine
        H N hN beta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta.1 beta.2 := rfl

/-- The half-line physical transfer family is globally Lipschitz in operator
norm with the finite-volume one-slab action budget. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine_lipschitz
    (H N : ℕ)
    (hN : 0 < N) :
    LipschitzWith
      (⟨periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H,
        by
          unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget
          positivity⟩ : NNReal)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine
        H N hN) := by
  apply LipschitzWith.of_dist_le_mul
  intro beta gamma
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_sub_le_beta
      H N hN gamma.1 beta.1 gamma.2 beta.2
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine,
    dist_eq_norm] using h

/-- Consequently the actual physical transfer is continuous in operator norm
on the nonnegative coupling half-line. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine_continuous
    (H N : ℕ)
    (hN : 0 < N) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine
        H N hN) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine_lipschitz
    H N hN).continuous

/-- The positive top-transfer norm is a continuous scalar function of beta on
the physical half-line. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine_norm_continuous
    (H N : ℕ)
    (hN : 0 < N) :
    Continuous
      (fun beta : Set.Ici (0 : ℝ) =>
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine
          H N hN beta‖) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine_continuous
    H N hN).norm

/-- The half-line top-transfer norm never vanishes. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine_norm_ne_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : Set.Ici (0 : ℝ)) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine
      H N hN beta‖ ≠ 0 := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta.1 beta.2).ne'

/-- The norm-normalized physical transfer, now as a genuine family on the fixed
nonnegative beta parameter space. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine
    (H N : ℕ)
    (hN : 0 < N) :
    Set.Ici (0 : ℝ) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  fun beta =>
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta.1 beta.2

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : Set.Ici (0 : ℝ)) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine
        H N hN beta =
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta.1 beta.2 := rfl

/-- The normalized physical transfer is continuous in operator norm on the
entire nonnegative Wilson-coupling half-line.  This is the fixed-top-point
continuity input required by the subsequent Riesz/CFC top-sector continuation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine_continuous
    (H N : ℕ)
    (hN : 0 < N) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine
        H N hN) := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine
      H N hN
  have hT : Continuous T := by
    simpa [T] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine_continuous
        H N hN
  have hNorm : Continuous (fun beta => ‖T beta‖) :=
    hT.norm
  have hInv : Continuous (fun beta => ‖T beta‖⁻¹) :=
    hNorm.inv₀ (by
      intro beta
      simpa [T] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine_norm_ne_zero
          H N hN beta)
  change Continuous (fun beta => ‖T beta‖⁻¹ • T beta)
  exact hInv.smul hT

end

end MathlibAnalytic
end MGAP4D
