import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSGaussEndpointHilbertExcitationDecay
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance osGaussEndpointNormalizedDenseCoreSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osGaussEndpointNormalizedDenseCoreSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osGaussEndpointNormalizedDenseCoreSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osGaussEndpointNormalizedDenseCoreSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osGaussEndpointNormalizedDenseCoreSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osGaussEndpointNormalizedDenseCoreSpatialSliceVertexFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance osGaussEndpointNormalizedDenseCoreSpatialSliceLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The exact scalar used to transfer-normalize the represented endpoint OS
states is strictly positive.

This combines two already concrete finite-volume facts: the physical one-slab
transfer has strictly positive operator norm and the compact Wilson partition
function is strictly positive. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization_pos
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 < periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization
      H N hN beta hbeta := by
  have hT :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta
  have hZ :
      0 <
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction :=
    compact_oriented_partitionFunction_pos
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base
      (continuous_compact_oriented_boltzmannIntegrable
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta))
  unfold periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization
  exact mul_pos
    (pow_pos (inv_pos.mpr hT) _)
    (Real.sqrt_pos.2 hZ)

/-- Consequently the Hilbert-state normalization factor itself is strictly
positive and in particular nonzero. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization_sqrt_pos
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 < Real.sqrt
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization
        H N hN beta hbeta) :=
  Real.sqrt_pos.2
    (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization_pos
      H N hN beta hbeta)

/-- The transfer-normalized endpoint representation, bundled as a linear map
from the canonical endpoint carrier into the already completed finite OS
Hilbert space.

It is only a nonzero scalar multiple of the canonical dense endpoint-state
map.  Thus no new quotient or completion is introduced here. -/
noncomputable def periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
        H N hN beta hbeta →ₗ[ℝ]
      PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointHilbert
        H N hN beta hbeta :=
  Real.sqrt
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization
        H N hN beta hbeta) •
    periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalStateLinearMap
      H N hN beta hbeta

@[simp] theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap_apply
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap
        H N hN beta hbeta F =
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState
        H N hN beta hbeta F.state := by
  rfl

/-- Transfer normalization does not change the OS null space.  Hence the
normalized dense representation descends through exactly the same canonical
`SeparationQuotient` as the original endpoint construction. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap_ker
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    LinearMap.ker
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap
        H N hN beta hbeta) =
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointNullSubmodule
        H N hN beta hbeta := by
  rw [← periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalStateLinearMap_ker]
  ext F
  let a : ℝ :=
    Real.sqrt
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization
        H N hN beta hbeta)
  have ha : a ≠ 0 :=
    ne_of_gt
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization_sqrt_pos
        H N hN beta hbeta)
  change
    a • periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalStateLinearMap
        H N hN beta hbeta F = 0 ↔
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalStateLinearMap
        H N hN beta hbeta F = 0
  simp [ha]

/-- A nonzero scalar normalization preserves the range of the represented
endpoint map exactly.  The proof is constructive: one inclusion uses the
preimage `a • F`, the reverse inclusion uses `a⁻¹ • F`. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap_range
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Set.range
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap
        H N hN beta hbeta) =
      Set.range
        (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalStateLinearMap
          H N hN beta hbeta) := by
  let a : ℝ :=
    Real.sqrt
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization
        H N hN beta hbeta)
  have ha : a ≠ 0 :=
    ne_of_gt
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization_sqrt_pos
        H N hN beta hbeta)
  ext y
  constructor
  · rintro ⟨F, rfl⟩
    refine ⟨a • F, ?_⟩
    simp [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap,
      a]
  · rintro ⟨F, rfl⟩
    refine ⟨a⁻¹ • F, ?_⟩
    simp [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap,
      a, ha]

/-- The transfer-normalized represented endpoint states remain dense in the
completed finite endpoint OS Hilbert space. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap_denseRange
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    DenseRange
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap
        H N hN beta hbeta) := by
  change Dense
    (Set.range
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap
        H N hN beta hbeta))
  rw [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap_range]
  exact
    periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalStateLinearMap_denseRange
      H N hN beta hbeta

/-- On a represented Gauss-law state, the bundled normalized dense map is the
state used by the completed-Hilbert transfer identification of the preceding
unit. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap_inner_eq_normalizedPhysicalTransfer
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F G : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta) :
    inner ℝ
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap
        H N hN beta hbeta F)
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap
        H N hN beta hbeta G) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta F.state) G.state := by
  rw [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap_apply]
  rw [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap_apply]
  exact
    periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState_inner_eq_normalizedPhysicalTransfer
      H N hN beta hbeta F.state G.state

/-- The excitation estimate can now be read as a squared-norm decay statement
for the canonical dense endpoint representation itself. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState_excitation_norm_sq_le_exp
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState
        H N hN beta hbeta
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)‖ ^ 2 ≤
      Real.exp
        (-(periodicHypercubicEvenPositiveHalfCylinderSlabCount H : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) * ‖f‖ ^ 2 := by
  have h :=
    periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalState_excitation_inner_norm_le_exp
      H N hN beta hbeta f f
  simpa [real_inner_self_eq_norm_sq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    pow_two, mul_assoc] using h

/-- Audit-visible receipt: the transfer-normalized endpoint representation has
strictly positive normalization, the same null kernel, dense range, exact
normalized-transfer inner product, and finite-volume excitation decay. -/
structure PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointNormalizedDenseCorePackage
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  normalizationPositive :
    0 < periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization
      H N hN beta hbeta
  sameKernel :
    LinearMap.ker
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap
        H N hN beta hbeta) =
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointNullSubmodule
        H N hN beta hbeta
  denseRange :
    DenseRange
      (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap
        H N hN beta hbeta)
  normalizedTransferInner :
    ∀ F G : PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointCarrier
      H N hN beta hbeta,
      inner ℝ
        (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap
          H N hN beta hbeta F)
        (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap
          H N hN beta hbeta G) =
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator
            H N hN beta hbeta F.state) G.state

/-- Construct the normalized dense endpoint-core package. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointNormalizedDenseCorePackage
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointNormalizedDenseCorePackage
      H N hN beta hbeta :=
  { normalizationPositive :=
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalization_pos
        H N hN beta hbeta
    sameKernel :=
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap_ker
        H N hN beta hbeta
    denseRange :=
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap_denseRange
        H N hN beta hbeta
    normalizedTransferInner :=
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointTransferNormalizedPhysicalStateLinearMap_inner_eq_normalizedPhysicalTransfer
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
