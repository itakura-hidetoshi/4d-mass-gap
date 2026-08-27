import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSNormalizedGramExcitationDecay
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance osGaussEndpointPreHilbertSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osGaussEndpointPreHilbertSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osGaussEndpointPreHilbertSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osGaussEndpointPreHilbertSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osGaussEndpointPreHilbertSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osGaussEndpointPreHilbertSpatialSliceVertexFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance osGaussEndpointPreHilbertSpatialSliceLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Every natural power of a positive bounded operator on a real Hilbert space
is positive.

The proof deliberately avoids a spectral-calculus detour.  Two-step induction
uses symmetry to move the two outer copies of `T` across the inner product:
`⟪T * T^n * T x, x⟫ = ⟪T^n (T x), T x⟫`.  Thus positivity at exponent `n`
implies positivity at exponent `n+2`; the base cases are the identity and `T`.
This is the exact algebra needed by reflection-positive transfer powers. -/
private theorem realContinuousLinearMap_pow_isPositive
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hT : (T : E →ₗ[ℝ] E).IsPositive)
    (n : ℕ) :
    (((T ^ n : E →L[ℝ] E) : E →ₗ[ℝ] E).IsPositive) := by
  refine ⟨hT.isSymmetric.pow n, ?_⟩
  intro x
  change 0 ≤ inner ℝ ((T ^ n) x) x
  induction n generalizing x using Nat.twoStepInduction with
  | zero =>
      simp
  | one =>
      simpa using hT.inner_nonneg_left x
  | more n hn _hn1 =>
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
      rw [pow_succ']
      change 0 ≤ inner ℝ (T ((T ^ n) (T x))) x
      calc
        0 ≤ inner ℝ ((T ^ n) (T x)) (T x) := hn (T x)
        _ = inner ℝ (T ((T ^ n) (T x))) x :=
          (hT.isSymmetric ((T ^ n) (T x)) x).symm

/-- The actual positive physical one-slab transfer remains positive after
vacuum normalization by its strictly positive operator norm. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isPositive
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsPositive) := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  change ((((‖T‖⁻¹ • T) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsPositive)
  have hT : (T :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsPositive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isPositive
      H N hN beta hbeta
  have hc : 0 ≤ ‖T‖⁻¹ := inv_nonneg.mpr (norm_nonneg T)
  simpa using hT.smul_of_nonneg hc

/-- The unnormalized transfer through the complete positive reflection
half-cylinder is a positive operator. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator_isPositive
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
        H N hN beta hbeta :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsPositive) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
  exact
    realContinuousLinearMap_pow_isPositive
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isPositive
        H N hN beta hbeta)
      (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)

/-- The vacuum-normalized positive-half transfer is positive as well. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator_isPositive
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator
        H N hN beta hbeta :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsPositive) := by
  unfold periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator
  exact
    realContinuousLinearMap_pow_isPositive
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isPositive
        H N hN beta hbeta)
      (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)

/-- The canonical normalized boundary OS Gram coefficient restricted to the two
Gauss-law endpoint states.  Naming this scalar separates the OS form itself
from its path-coordinate presentation. -/
noncomputable def periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpointCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) : ℝ :=
  ∫ z,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta z.1 z.2 *
      ((f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
          ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
            H N z).1 0) *
        (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
          ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
            H N z).1
            (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
    ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)

/-- The bounded operator whose matrix coefficients are exactly the canonical
normalized Gauss-endpoint OS Gram coefficients.

It is the actual `H+1`-slab physical transfer multiplied by the positive scalar
`Z^{-1/2}`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryGaussEndpointOSOperator
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  (Real.sqrt
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹ •
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
      H N hN beta hbeta

/-- The canonical Gauss-endpoint OS operator is positive.  This is the operator
form of finite-volume reflection positivity on the endpoint sector. -/
theorem periodicHypercubicEvenSpecialUnitaryGaussEndpointOSOperator_isPositive
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (((periodicHypercubicEvenSpecialUnitaryGaussEndpointOSOperator
        H N hN beta hbeta :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsPositive) := by
  let c : ℝ :=
    (Real.sqrt
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
      H N hN beta hbeta
  change ((((c • T) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsPositive)
  have hT : (T :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsPositive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator_isPositive
      H N hN beta hbeta
  have hc : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  simpa using hT.smul_of_nonneg hc

/-- The path-coordinate canonical OS endpoint Gram coefficient is exactly the
matrix coefficient of the positive Gauss-endpoint OS operator. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpointCoefficient_eq_inner_osOperator
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpointCoefficient
        H N hN beta hbeta f g =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryGaussEndpointOSOperator
          H N hN beta hbeta f) g := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpointCoefficient
  rw [periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_closureIntegral_eq_invSqrtPartition_mul_physicalTransfer]
  unfold periodicHypercubicEvenSpecialUnitaryGaussEndpointOSOperator
  simp [inner_smul_left]

/-- Canonical normalized OS endpoint reflection positivity for every actual
Gauss-law Haar-`L²` state. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpointCoefficient_self_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    0 ≤
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpointCoefficient
        H N hN beta hbeta f f := by
  rw [periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpointCoefficient_eq_inner_osOperator]
  exact
    (periodicHypercubicEvenSpecialUnitaryGaussEndpointOSOperator_isPositive
      H N hN beta hbeta).inner_nonneg_left f

/-- The transfer-normalized OS endpoint coefficient from the preceding bridge
is positive semidefinite as well.  This is the norm-one version used by the
excitation decay theorem. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient_self_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    0 ≤
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient
        H N hN beta hbeta f f := by
  rw [periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient_eq_normalizedPhysicalTransfer]
  exact
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator_isPositive
      H N hN beta hbeta).inner_nonneg_left f

/-- Mathlib pre-inner-product core carried by the actual finite-volume
Gauss-law Haar-`L²` endpoint states, with inner form equal to the canonical
normalized OS Gram coefficient.

No new norm instance is installed on the physical Haar-`L²` space.  The core is
kept explicit so that a subsequent `SeparationQuotient` can use the OS
seminorm without conflicting with the already existing Haar-`L²` Hilbert norm. -/
@[reducible] noncomputable def periodicHypercubicEvenSpecialUnitaryGaussEndpointOSPreInnerProductCore
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PreInnerProductSpace.Core ℝ
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) where
  inner f g :=
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryGaussEndpointOSOperator
        H N hN beta hbeta f) g
  conj_inner_symm f g := by
    change inner ℝ
        (periodicHypercubicEvenSpecialUnitaryGaussEndpointOSOperator
          H N hN beta hbeta g) f =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryGaussEndpointOSOperator
          H N hN beta hbeta f) g
    have hsymm :=
      (periodicHypercubicEvenSpecialUnitaryGaussEndpointOSOperator_isPositive
        H N hN beta hbeta).isSymmetric
    calc
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryGaussEndpointOSOperator
            H N hN beta hbeta g) f =
        inner ℝ g
          (periodicHypercubicEvenSpecialUnitaryGaussEndpointOSOperator
            H N hN beta hbeta f) := hsymm g f
      _ = inner ℝ
          (periodicHypercubicEvenSpecialUnitaryGaussEndpointOSOperator
            H N hN beta hbeta f) g := real_inner_comm _ _
  re_inner_nonneg f := by
    change 0 ≤ inner ℝ
      (periodicHypercubicEvenSpecialUnitaryGaussEndpointOSOperator
        H N hN beta hbeta f) f
    exact
      (periodicHypercubicEvenSpecialUnitaryGaussEndpointOSOperator_isPositive
        H N hN beta hbeta).inner_nonneg_left f
  add_left f g h := by
    simp
  smul_left f g r := by
    simp

/-- The Mathlib pre-inner-product core is not merely abstract: its form is
exactly the canonical normalized OS endpoint Gram path integral. -/
theorem periodicHypercubicEvenSpecialUnitaryGaussEndpointOSPreInnerProductCore_inner_eq_GramCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (periodicHypercubicEvenSpecialUnitaryGaussEndpointOSPreInnerProductCore
        H N hN beta hbeta).inner f g =
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpointCoefficient
        H N hN beta hbeta f g := by
  change inner ℝ
      (periodicHypercubicEvenSpecialUnitaryGaussEndpointOSOperator
        H N hN beta hbeta f) g =
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpointCoefficient
      H N hN beta hbeta f g
  exact
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpointCoefficient_eq_inner_osOperator
      H N hN beta hbeta f g).symm

end

end MathlibAnalytic
end MGAP4D
