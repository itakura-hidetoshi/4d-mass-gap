import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationDiagnostic
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNormalization
import Mathlib.Tactic

/-!
# Explicit finite-volume denominator bound for physical transfer normalization

The normalized physical pair transfer uses the scalar

  (||T_phys(H,beta)||^2)^(-1).

For later beta-perturbation estimates we need an explicit lower bound on the
unnormalized physical one-slab transfer norm, not merely positivity.

The existing global Wilson minorization floor

  m_H(beta) = exp(- beta * globalActionBudget(H))

is pointwise below the exact one-slab kernel.  Integrating against normalized
product Haar and evaluating the physical transfer on the constant unit vector
gives

  m_H(beta) <= <T_phys 1,1> <= ||T_phys||.

Consequently the inverse normalization scale is explicitly bounded by the
inverse global floor, including the inverse-square coefficient used by the pair
transfer.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance normalizationFloorTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance normalizationFloorCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance normalizationFloorSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance normalizationFloorMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance normalizationFloorBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance normalizationFloorSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The explicit global minorization floor is below the normalized
product-Haar average of the exact one-slab Wilson kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_kernelPairIntegral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta ≤
      ∫ p :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let m :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
      H beta
  have hmInt :
      Integrable
        (fun _ :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          m)
        μ :=
    integrable_const m
  have hKInt :
      Integrable
        (fun p :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2)
        μ := by
    simpa [μ] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pair_integrable
        H N hN beta hbeta
  have hmono :
      ∫ _ :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          m ∂μ ≤
        ∫ p :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 ∂μ := by
    apply integral_mono_ae hmInt hKInt
    filter_upwards with p
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_kernel
        H N hN beta hbeta p.1 p.2
  simpa [μ, m] using hmono

/-- The global minorization floor is below the transfer expectation of the
canonical physical constant unit vector. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_constantExpectation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta ≤
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N))
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) := by
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta ≤
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta
          (Lp.const 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
            (1 : ℝ)))
        (Lp.const 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
          (1 : ℝ))
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_const_one_eq_integral]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_kernelPairIntegral
      H N hN beta hbeta

/-- Explicit denominator certificate: the global minorization floor is below
the physical one-slab transfer norm. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_transferNorm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let oneP := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  have hfloor :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
          H beta ≤
        inner ℝ (T oneP) oneP := by
    simpa [T, oneP] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_constantExpectation
        H N hN beta hbeta
  have hone : ‖oneP‖ = 1 := by
    simpa [oneP] using
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H N
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta ≤ inner ℝ (T oneP) oneP := hfloor
    _ ≤ ‖T oneP‖ * ‖oneP‖ := real_inner_le_norm _ _
    _ ≤ (‖T‖ * ‖oneP‖) * ‖oneP‖ := by
      exact mul_le_mul_of_nonneg_right (T.le_opNorm oneP) (norm_nonneg oneP)
    _ = ‖T‖ := by rw [hone]; ring

/-- The inverse physical normalization scale is controlled by the inverse
explicit global minorization floor. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferNorm_inv_le_globalMinorizationFloor_inv
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta)⁻¹ := by
  have hfloorPos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos
      H beta
  have hnormPos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta
  exact
    (inv_le_inv₀ hnormPos hfloorPos).2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_transferNorm
        H N hN beta hbeta)

private theorem real_sq_le_sq_of_nonneg_of_le
    (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 2 ≤ y ^ 2 := by
  nlinarith

/-- The inverse-square coefficient used in the normalized physical pair
transfer is bounded by the inverse square of the explicit global floor. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferNorm_sq_inv_le_globalMinorizationFloor_sq_inv
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ ^ 2)⁻¹ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta ^ 2)⁻¹ := by
  have hInv :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
          H beta)⁻¹ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferNorm_inv_le_globalMinorizationFloor_inv
      H N hN beta hbeta
  have hInvNonneg :
      0 ≤
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ :=
    (inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta)).le
  have hsq :=
    pow_le_pow_left₀ hInvNonneg hInv 2
  simpa only [inv_pow] using hsq

end

end MathlibAnalytic
end MGAP4D
