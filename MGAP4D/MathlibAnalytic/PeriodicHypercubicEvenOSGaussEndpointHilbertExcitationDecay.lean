import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOSHilbert
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSNormalizedGramExcitationDecay
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance osGaussEndpointHilbertDecaySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osGaussEndpointHilbertDecaySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osGaussEndpointHilbertDecaySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osGaussEndpointHilbertDecaySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osGaussEndpointHilbertDecaySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osGaussEndpointHilbertDecaySpatialSliceVertexFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance osGaussEndpointHilbertDecaySpatialSliceLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Scalar which simultaneously removes the canonical finite-volume
`Z^{-1/2}` endpoint normalization and vacuum-normalizes the complete
`H+1`-slab transfer power.

Multiplying the endpoint OS inner product by this scalar produces exactly the
matrix coefficients of the norm-one physical positive-half transfer. -/
noncomputable def periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ ^
      periodicHypercubicEvenPositiveHalfCylinderSlabCount H *
    Real.sqrt
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction

/-- The endpoint transfer-normalization scalar is nonnegative. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 ≤ periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization
      H N hN beta hbeta := by
  have hnorm :
      0 ≤ ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ :=
    le_of_lt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta)
  unfold periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization
  exact mul_nonneg
    (pow_nonneg (inv_nonneg.mpr hnorm) _)
    (Real.sqrt_nonneg _)

/-- A Gauss-law one-slice state represented in the completed finite endpoint
OS Hilbert space after the exact transfer normalization.

The square root is forced by Hilbert geometry: scaling both entries by
`sqrt c_H` multiplies their inner product by `c_H`, where
`c_H = ||T||^{-(H+1)} sqrt Z`. -/
noncomputable def periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointHilbert
      H N hN beta hbeta :=
  Real.sqrt
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization
        H N hN beta hbeta) •
    periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
      H N hN beta hbeta ⟨f⟩

/-- The Hilbert inner product of transfer-normalized endpoint states is exactly
the transfer-normalized canonical OS endpoint coefficient from the concrete
closure path integral.

This theorem is the bridge from the scalar/path statement of the preceding
unit to an actual completed finite OS Hilbert carrier. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState_inner_eq_transferNormalizedCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState
        H N hN beta hbeta f)
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState
        H N hN beta hbeta g) =
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient
        H N hN beta hbeta f g := by
  let c :=
    periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization
      H N hN beta hbeta
  let F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta := ⟨f⟩
  let G : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta := ⟨g⟩
  have hc : 0 ≤ c := by
    simpa [c] using
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization_nonneg
        H N hN beta hbeta
  change inner ℝ
      (Real.sqrt c •
        periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
          H N hN beta hbeta F)
      (Real.sqrt c •
        periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
          H N hN beta hbeta G) =
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient
      H N hN beta hbeta f g
  calc
    inner ℝ
        (Real.sqrt c •
          periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
            H N hN beta hbeta F)
        (Real.sqrt c •
          periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
            H N hN beta hbeta G) =
      (Real.sqrt c) ^ 2 *
        inner ℝ
          (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
            H N hN beta hbeta F)
          (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState
            H N hN beta hbeta G) := by
      simp [inner_smul_left, inner_smul_right, pow_two, mul_assoc]
    _ = c * inner ℝ F G := by
      rw [Real.sq_sqrt hc]
      rw [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalState_inner]
    _ = c *
        (∫ z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
            (Matrix.specialUnitaryGroup (Fin N) ℂ),
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H N hN beta hbeta z.1 z.2 *
            (f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                H N z).1 0) *
            (g : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                H N z).1
                (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)) := by
      rw [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier_inner_eq_integral]
    _ =
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient
        H N hN beta hbeta f g := by
      unfold c
      unfold periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization
      unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient
      simp only [mul_assoc]

/-- Equivalently, the completed endpoint OS Hilbert inner product is literally
the matrix coefficient of the norm-one physical positive-half transfer. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState_inner_eq_normalizedPhysicalTransfer
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState
        H N hN beta hbeta f)
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState
        H N hN beta hbeta g) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta f) g := by
  rw [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState_inner_eq_transferNormalizedCoefficient]
  exact
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient_eq_normalizedPhysicalTransfer
      H N hN beta hbeta f g

/-- The squared norm of a represented endpoint state in the completed,
transfer-normalized OS Hilbert geometry is the canonical transfer-normalized
OS quadratic coefficient. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState_norm_sq_eq
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState
        H N hN beta hbeta f‖ ^ 2 =
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient
        H N hN beta hbeta f f := by
  rw [← real_inner_self_eq_norm_sq]
  exact
    periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState_inner_eq_transferNormalizedCoefficient
      H N hN beta hbeta f f

/-- On the full top-eigenspace orthogonal sector, the completed endpoint OS
Hilbert inner product is exactly the physical excitation-transfer matrix
coefficient. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState_excitation_inner_eq
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    inner ℝ
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState
        H N hN beta hbeta
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState
        H N hN beta hbeta
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)) =
      inner ℝ
        (((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator
          H N hN beta hbeta f :
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
              H N hN beta hbeta) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) := by
  rw [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState_inner_eq_transferNormalizedCoefficient]
  exact
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient_excitation_eq
      H N hN beta hbeta f g

/-- The excitation matrix coefficients now decay exponentially as literal
inner products in the completed finite endpoint OS Hilbert space.

This upgrades the preceding scalar/path-integral statement to the quotient and
completion carrier produced by Mathlib's `SeparationQuotient` and uniform
completion.  It remains a finite-volume statement at the exact geometric time
`H+1`; no uniform-in-volume or continuum gap is asserted. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState_excitation_inner_norm_le_exp
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖inner ℝ
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState
        H N hN beta hbeta
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState
        H N hN beta hbeta
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))‖ ≤
      (Real.exp
        (-(periodicHypercubicEvenPositiveHalfCylinderSlabCount H : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) * ‖f‖) * ‖g‖ := by
  rw [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState_inner_eq_transferNormalizedCoefficient]
  exact
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_GaussEndpoint_transferNormalizedCoefficient_excitation_norm_le_exp
      H N hN beta hbeta f g

end

end MathlibAnalytic
end MGAP4D
