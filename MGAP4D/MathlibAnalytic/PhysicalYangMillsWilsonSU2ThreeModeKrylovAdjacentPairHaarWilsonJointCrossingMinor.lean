import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveBetaOrthogonalReceiverExact
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointMeasure
import Mathlib.Tactic

/-!
# P4: exact Wilson joint crossing minor and cancellation of the true vacuum

The original physical positive-beta one-slab ground-state joint density is

  W_beta(A,B) = lambda_beta^(-1) Omega_beta(A) K_beta(A,B) Omega_beta(B),

where K_beta is the unmodified finite-volume temporal-gauge Wilson
one-slab kernel, Omega_beta the actual nonnegative top physical
L2 eigenvector representative, and lambda_beta the norm of the
original physical transfer.

The FULL 2-by-2 crossing minor of W_beta factors EXACTLY as

  W(A1,B1) W(A2,B2) - W(A1,B2) W(A2,B1)
    = lambda^(-2) Omega(A1)Omega(A2)Omega(B1)Omega(B2)
        * (K(A1,B1)K(A2,B2)-K(A1,B2)K(A2,B1)).

This is a genuine physical Wilson factorization, not a surrogate
posterior. It avoids dividing by potentially zero pointwise L2
representatives and keeps all four boundary points explicit.
In particular a NONZERO temporal crossing kernel minor plus the
explicitly stated nonzero vacuum values forces a nonzero minor
of the original normalized ground-state joint density and prevents
any POINTWISE left/right separable density factorization.

No claim is made that the required pointwise nonzero crossing witness
has been constructed for every beta>0, or that pointwise nonseparability
alone establishes almost-everywhere non-measurability and positive
posterior fiber energy. Those are subsequent analytic obligations.
No Dobrushin, artificial law, positive-beta volume-uniformity,
or continuum Yang--Mills mass-gap assertion is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4CrossMinorTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4CrossMinorCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4CrossMinorSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4CrossMinorMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4CrossMinorBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4CrossMinorSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Name for the literal original physical top eigenvector L2
representative, with no replacement of its pointwise null set. -/
noncomputable def originalWilsonPhysicalTopVacuumValue
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta).1 A

/-- The concrete signed 2-by-2 minor of the unchanged temporal-gauge
Wilson crossing kernel. -/
noncomputable def originalWilsonTemporalKernelTwoByTwoMinor
    (H N : ℕ) (beta : ℝ)
    (A₁ A₂ B₁ B₂ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A₁ B₁ *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A₂ B₂ -
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A₁ B₂ *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A₂ B₁

/-- The concrete signed 2-by-2 minor of the TRUE normalized
Wilson physical ground-state joint density. -/
noncomputable def originalWilsonJointTwoByTwoMinor
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A₁ A₂ B₁ B₂ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
      H N hN beta hbeta (A₁, B₁) *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
      H N hN beta hbeta (A₂, B₂) -
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
      H N hN beta hbeta (A₁, B₂) *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
      H N hN beta hbeta (A₂, B₁)

/-- Exact CROSS-MULTIPLIED minor cancellation: all physical top
vacuum and normalization factors separate cleanly from the actual
two-boundary Wilson interaction minor, without any division. -/
theorem originalWilsonJointTwoByTwoMinor_eq_vacuumFactors_mul_temporalKernelMinor
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A₁ A₂ B₁ B₂ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    originalWilsonJointTwoByTwoMinor H N hN beta hbeta A₁ A₂ B₁ B₂ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ ^ 2 *
      (originalWilsonPhysicalTopVacuumValue H N hN beta hbeta A₁ *
        originalWilsonPhysicalTopVacuumValue H N hN beta hbeta A₂ *
        originalWilsonPhysicalTopVacuumValue H N hN beta hbeta B₁ *
        originalWilsonPhysicalTopVacuumValue H N hN beta hbeta B₂) *
      originalWilsonTemporalKernelTwoByTwoMinor H N beta A₁ A₂ B₁ B₂ := by
  unfold originalWilsonJointTwoByTwoMinor
    originalWilsonTemporalKernelTwoByTwoMinor
    originalWilsonPhysicalTopVacuumValue
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
  ring

/-- Any explicit nonzero Wilson crossing-kernel minor and four
NONZERO actual physical-vacuum representative values imply a
nonzero minor of the original normalized physical joint density.
The transfer normalization is nonzero by the existing strict
physical transfer norm theorem. -/
theorem originalWilsonJointTwoByTwoMinor_ne_zero_of_temporalKernelMinor
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A₁ A₂ B₁ B₂ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (hA₁ : originalWilsonPhysicalTopVacuumValue H N hN beta hbeta A₁ ≠ 0)
    (hA₂ : originalWilsonPhysicalTopVacuumValue H N hN beta hbeta A₂ ≠ 0)
    (hB₁ : originalWilsonPhysicalTopVacuumValue H N hN beta hbeta B₁ ≠ 0)
    (hB₂ : originalWilsonPhysicalTopVacuumValue H N hN beta hbeta B₂ ≠ 0)
    (hCross : originalWilsonTemporalKernelTwoByTwoMinor
      H N beta A₁ A₂ B₁ B₂ ≠ 0) :
    originalWilsonJointTwoByTwoMinor H N hN beta hbeta A₁ A₂ B₁ B₂ ≠ 0 := by
  have hTpos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H N hN beta hbeta
  have hLambda :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt hTpos)
  rw [originalWilsonJointTwoByTwoMinor_eq_vacuumFactors_mul_temporalKernelMinor]
  exact mul_ne_zero
    (mul_ne_zero
      (pow_ne_zero 2 hLambda)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hA₁ hA₂) hB₁) hB₂))
    hCross

/-- Under an explicit physical nonzero-crossing witness, the actual
normalized Wilson joint weight cannot be a POINTWISE rank-one
left/right product. This is a precise crossing obstruction, not
an unsupported a.e. conditional-measurability conclusion. -/
theorem originalWilsonJointNormalizedWeight_not_pointwise_separable_of_temporalCrossing
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A₁ A₂ B₁ B₂ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (hA₁ : originalWilsonPhysicalTopVacuumValue H N hN beta hbeta A₁ ≠ 0)
    (hA₂ : originalWilsonPhysicalTopVacuumValue H N hN beta hbeta A₂ ≠ 0)
    (hB₁ : originalWilsonPhysicalTopVacuumValue H N hN beta hbeta B₁ ≠ 0)
    (hB₂ : originalWilsonPhysicalTopVacuumValue H N hN beta hbeta B₂ ≠ 0)
    (hCross : originalWilsonTemporalKernelTwoByTwoMinor
      H N beta A₁ A₂ B₁ B₂ ≠ 0) :
    ¬ ∃ (F G : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ),
      ∀ A B,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
          H N hN beta hbeta (A, B) = F A * G B := by
  intro ⟨F, G, hSep⟩
  have hnonzero :=
    originalWilsonJointTwoByTwoMinor_ne_zero_of_temporalKernelMinor
      H N hN beta hbeta A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ hCross
  have hzero :
      originalWilsonJointTwoByTwoMinor H N hN beta hbeta A₁ A₂ B₁ B₂ = 0 := by
    unfold originalWilsonJointTwoByTwoMinor
    rw [hSep A₁ B₁, hSep A₂ B₂, hSep A₁ B₂, hSep A₂ B₁]
    ring
  exact hnonzero hzero

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
