import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSNormalizedGramEndpointPhysicalTransfer
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance osNormalizedGramExcitationDecaySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osNormalizedGramExcitationDecaySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osNormalizedGramExcitationDecaySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osNormalizedGramExcitationDecaySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osNormalizedGramExcitationDecaySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osNormalizedGramExcitationDecaySpatialSliceVertexFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance osNormalizedGramExcitationDecaySpatialSliceLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Powers commute with a real scalar normalization of a bounded operator,
pointwise on the underlying normed space.  This generic lemma keeps the
concrete lattice carrier out of the normalization algebra. -/
private theorem realContinuousLinearMap_smul_pow_apply
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (c : ℝ)
    (T : E →L[ℝ] E)
    (n : ℕ)
    (f : E) :
    ((c • T) ^ n) f = c ^ n • (T ^ n) f := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      simp [pow_succ, ContinuousLinearMap.mul_def, ih, smul_smul]

/-- Powers of the invariant top-eigenspace orthogonal restriction are exactly
the ambient powers after coercion back to the Hilbert carrier. -/
private theorem realHilbertTopEigenspaceOrthogonalRestriction_pow_coe
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric)
    (n : ℕ)
    (f : (realHilbertTopEigenspace S)ᗮ) :
    ((((realHilbertTopEigenspaceOrthogonalRestriction S hS) ^ n) f :
        (realHilbertTopEigenspace S)ᗮ) : E) =
      (S ^ n) (f : E) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      change
        ((((realHilbertTopEigenspaceOrthogonalRestriction S hS) ^ n)
            (realHilbertTopEigenspaceOrthogonalRestriction S hS f) :
          (realHilbertTopEigenspace S)ᗮ) : E) =
          (S ^ n) (S (f : E))
      rw [ih]
      rw [realHilbertTopEigenspaceOrthogonalRestriction_coe]

/-- The normalized positive-half transfer is the physical `H+1`-slab transfer
scaled by the corresponding power of the inverse physical one-slab norm. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator_apply_eq_invNormPow_smul_physical
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator
        H N hN beta hbeta f =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ ^
          periodicHypercubicEvenPositiveHalfCylinderSlabCount H •
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta f := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator,
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator,
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
  ] using
    (realContinuousLinearMap_smul_pow_apply
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)
      f)

/-- The positive-half excitation transfer is literally the normalized ambient
positive-half transfer restricted to the full top-eigenspace orthogonal
sector. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator_coe
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator
        H N hN beta hbeta f :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator
        H N hN beta hbeta
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace,
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator
  ] using
    (realHilbertTopEigenspaceOrthogonalRestriction_pow_coe
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
        H N hN beta hbeta)
      (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)
      f)

/-- Transfer-normalized endpoint coefficient extracted from the canonical
normalized OS Gram feature.

The factor `sqrt Z` removes the finite-volume OS feature normalization, while
the power of the inverse one-slab transfer norm passes from the unnormalized
physical transfer to its vacuum-normalized norm-one transfer. -/
noncomputable def periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ ^
      periodicHypercubicEvenPositiveHalfCylinderSlabCount H *
    (Real.sqrt
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction *
      (∫ z,
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta z.1 z.2 *
          ((f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                H N z).1 0) *
            (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                H N z).1
                (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)))

/-- The transfer-normalized canonical OS endpoint coefficient is exactly the
matrix coefficient of the norm-one physical positive-half transfer. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient_eq_normalizedPhysicalTransfer
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient
        H N hN beta hbeta f g =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta f) g := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient
  rw [periodicHypercubicEven_sqrtPartition_mul_BoundaryCompletedPositiveGramFeature_GaussEndpoint_closureIntegral_eq_physicalTransfer]
  rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator_apply_eq_invNormPow_smul_physical]
  simp [inner_smul_left]

/-- On the full top-eigenspace orthogonal sector, the transfer-normalized OS
endpoint coefficient is exactly the physical excitation-transfer matrix
coefficient. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient_excitation_eq
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient
        H N hN beta hbeta
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
      inner ℝ
        (((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator
          H N hN beta hbeta f :
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
              H N hN beta hbeta) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) := by
  rw [periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient_eq_normalizedPhysicalTransfer]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator_coe]

/-- The excitation part of the canonical transfer-normalized OS endpoint Gram
coefficient decays exponentially across the complete positive half-cylinder.

This is a finite-volume Euclidean-time statement at the exact geometric time
`H+1`.  It introduces no volume-uniform or continuum mass-gap hypothesis. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient_excitation_norm_le_exp
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient
        H N hN beta hbeta
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)‖ ≤
      (Real.exp
        (-(periodicHypercubicEvenPositiveHalfCylinderSlabCount H : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) * ‖f‖) * ‖g‖ := by
  rw [periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient_excitation_eq]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator_matrixCoefficient_norm_le_exp
      H N hN beta hbeta f g

end

end MathlibAnalytic
end MGAP4D
