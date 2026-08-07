import MGAP4D.MathlibAnalytic.FiniteDimensionalSymmetricPositiveContractionGroundLiftedDefectDecomposition
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeInvariantCoarseEmbedding
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeIntertwiningObstructionDecomposition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- Actual spectral projector onto the eigenvalue-one sector of the
Gauss-invariant geometric one-slab transfer. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).groundSpectralProjector

/-- The actual ground spectral projector is symmetric. -/
theorem finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector_isSymmetric
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).groundSpectralProjector_isSymmetric

/-- Exact model-facing decomposition of the actual ground-lifted defect into
identity minus the actual Gauss-invariant one-slab transfer plus the actual
transfer-fixed spectral projector. -/
theorem finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_apply_decomposition
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ hEnergy x =
      x -
        finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy x +
        finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
          H β energyIdentity energyNontrivial hβ hEnergy x := by
  simpa [finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect,
    finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector,
    finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData] using
    FiniteDimensionalSymmetricPositiveContractionData.groundLiftedDefect_apply_eq_sub_operator_add_groundSpectralProjector
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        H β energyIdentity energyNontrivial hβ hEnergy) x

/-- One-step actual transfer intertwining residual on invariant configuration
Hilbert carriers. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H) :=
  ((finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.comp
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H).toLinearMap) -
  ((finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H).toLinearMap.comp
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap)

@[simp] theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap_apply
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f =
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f) -
        finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H
          (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
            H β energyIdentity energyNontrivial hβ hEnergy f) :=
  rfl

/-- One-step actual eigenvalue-one ground-projector intertwining residual. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidualLinearMap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H) :=
  ((finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.comp
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H).toLinearMap) -
  ((finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H).toLinearMap.comp
    (finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap)

@[simp] theorem finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidualLinearMap_apply
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f =
      finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f) -
        finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H
          (finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
            H β energyIdentity energyNontrivial hβ hEnergy f) :=
  rfl

/-- One-step actual ground-lifted-defect intertwining residual, now written
entirely on the Gauss-invariant configuration Hilbert carriers. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidualLinearMap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H) :=
  ((finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.comp
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H).toLinearMap) -
  ((finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H).toLinearMap.comp
    (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap)

@[simp] theorem finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidualLinearMap_apply
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f =
      finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f) -
        finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H
          (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
            H β energyIdentity energyNontrivial hβ hEnergy f) :=
  rfl

/-- Exact geometric decomposition of the one-step lifted-defect residual:

`R_defect = R_ground - R_transfer`.

Thus exact cross-volume intertwining of the lifted defect is neither silently
identified with transfer intertwining nor with ground-sector compatibility; it
is their exact signed combination. -/
theorem finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidual_decomposition
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy =
      finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy -
        finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy := by
  apply LinearMap.ext
  intro f
  change
    finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
        (finiteEvenFourTorusDoubleRefinement H)
        β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f) -
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H
        (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ hEnergy f) =
    (finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
        (finiteEvenFourTorusDoubleRefinement H)
        β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f) -
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H
        (finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
          H β energyIdentity energyNontrivial hβ hEnergy f)) -
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        (finiteEvenFourTorusDoubleRefinement H)
        β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f) -
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy f))
  rw [finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_apply_decomposition]
  rw [finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_apply_decomposition]
  rw [map_add, map_sub]
  module

/-- Exact one-step cancellation criterion on actual invariant carriers. -/
theorem finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidual_eq_zero_iff_transfer_eq_ground
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy =
        finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy := by
  rw [finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidual_decomposition]
  constructor
  · intro h
    have hsub :
        finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidualLinearMap
            H β energyIdentity energyNontrivial hβ hEnergy -
          finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
            H β energyIdentity energyNontrivial hβ hEnergy = 0 := h
    exact (sub_eq_zero.mp hsub).symm
  · intro h
    exact sub_eq_zero.mpr h.symm

/-- Orbit-space Package-E obstruction evaluated on a configuration-carrier
vector is exactly the fine orbit identification of the invariant-carrier
residual. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_apply_forward_eq_forward_invariantResidual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy
        ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f) =
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
        (finiteEvenFourTorusDoubleRefinement H)).forward
        (finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy f) := by
  change
    finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
        (finiteEvenFourTorusDoubleRefinement H)
        β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H
          ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f)) -
      finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ hEnergy
          ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f)) = _
  rw [← finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_forward_eq_orbitPullback]
  rw [finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect_intertwines]
  rw [finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect_intertwines]
  rw [← finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_forward_eq_orbitPullback]
  rw [finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidualLinearMap_apply]
  rw [map_sub]

/-- Vanishing of the Package-E one-step orbit obstruction is exactly vanishing
of the actual invariant-configuration residual. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_iff_invariantResidual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 := by
  constructor
  · intro hOrbit
    apply LinearMap.ext
    intro f
    have hf := LinearMap.congr_fun hOrbit
      ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f)
    rw [finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_apply_forward_eq_forward_invariantResidual]
      at hf
    exact
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
        (finiteEvenFourTorusDoubleRefinement H)).forward.injective
        (by simpa using hf)
  · intro hInvariant
    apply LinearMap.ext
    intro y
    let f := (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).inverse y
    have hy :
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f = y :=
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward_inverse y
    rw [← hy]
    rw [finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_apply_forward_eq_forward_invariantResidual]
    have hf := LinearMap.congr_fun hInvariant f
    rw [hf]
    simp

/-- Exact actual one-step geometric criterion: the orbit obstruction vanishes
iff the transfer residual and the eigenvalue-one ground-projector residual
coincide. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_iff_transfer_eq_ground
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy =
        finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy := by
  rw [finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_iff_invariantResidual]
  exact
    finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidual_eq_zero_iff_transfer_eq_ground
      H β energyIdentity energyNontrivial hβ hEnergy

/-- A stronger sufficient condition kept explicit: separate transfer
intertwining and ground-projector intertwining imply exact lifted-defect
intertwining.  The converse is deliberately not asserted because exact
cancellation of nonzero residuals is logically possible. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_of_transfer_and_ground_zero
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (hTransfer :
      finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0)
    (hGround :
      finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0) :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 := by
  apply
    (finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_iff_transfer_eq_ground
      H β energyIdentity energyNontrivial hβ hEnergy).2
  rw [hTransfer, hGround]

/-- Two-step actual transfer residual on invariant configuration carriers. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) :=
  ((finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.comp
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H).toLinearMap) -
  ((finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H).toLinearMap.comp
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap)

/-- Two-step actual ground-projector residual. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidualLinearMap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) :=
  ((finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.comp
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H).toLinearMap) -
  ((finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H).toLinearMap.comp
    (finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap)

/-- Two-step lifted-defect residual on invariant configuration carriers. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundLiftedDefectIntertwiningResidualLinearMap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) :=
  ((finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.comp
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H).toLinearMap) -
  ((finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H).toLinearMap.comp
    (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap)

@[simp] theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundLiftedDefectIntertwiningResidualLinearMap_apply
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundLiftedDefectIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f =
      finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H f) -
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H
          (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
            H β energyIdentity energyNontrivial hβ hEnergy f) :=
  rfl

/-- Exact two-step geometric decomposition of the lifted-defect residual. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundLiftedDefectIntertwiningResidual_decomposition
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundLiftedDefectIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy -
        finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy := by
  apply LinearMap.ext
  intro f
  change
    finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H f) -
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H
        (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ hEnergy f) =
    (finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H f) -
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H
        (finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
          H β energyIdentity energyNontrivial hβ hEnergy f)) -
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H f) -
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy f))
  rw [finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_apply_decomposition]
  rw [finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_apply_decomposition]
  rw [map_add, map_sub]
  module

/-- Exact two-step cancellation criterion on actual invariant carriers. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundLiftedDefectIntertwiningResidual_eq_zero_iff_transfer_eq_ground
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundLiftedDefectIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy =
        finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy := by
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundLiftedDefectIntertwiningResidual_decomposition]
  constructor
  · intro h
    exact (sub_eq_zero.mp h).symm
  · intro h
    exact sub_eq_zero.mpr h.symm

/-- Two-step Package-D/E orbit obstruction is exactly the forward image of the
two-step invariant-configuration residual. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_apply_forward_eq_forward_invariantResidual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy
        ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f) =
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))).forward
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundLiftedDefectIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy f) := by
  change
    finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseL2PullbackLinearIsometry H
          ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f)) -
      finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseL2PullbackLinearIsometry H
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ hEnergy
          ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f)) = _
  rw [← finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbedding_forward_eq_orbitPullback]
  rw [finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect_intertwines]
  rw [finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect_intertwines]
  rw [← finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbedding_forward_eq_orbitPullback]
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundLiftedDefectIntertwiningResidualLinearMap_apply]
  rw [map_sub]

/-- Exact two-step orbit/invariant residual equivalence. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_iff_invariantResidual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundLiftedDefectIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 := by
  constructor
  · intro hOrbit
    apply LinearMap.ext
    intro f
    have hf := LinearMap.congr_fun hOrbit
      ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f)
    rw [finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_apply_forward_eq_forward_invariantResidual]
      at hf
    exact
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))).forward.injective
        (by simpa using hf)
  · intro hInvariant
    apply LinearMap.ext
    intro y
    let f := (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).inverse y
    have hy :
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f = y :=
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward_inverse y
    rw [← hy]
    rw [finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_apply_forward_eq_forward_invariantResidual]
    have hf := LinearMap.congr_fun hInvariant f
    rw [hf]
    simp

/-- Exact actual two-step geometric criterion. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_iff_transfer_eq_ground
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy =
        finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy := by
  rw [finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_iff_invariantResidual]
  exact
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundLiftedDefectIntertwiningResidual_eq_zero_iff_transfer_eq_ground
      H β energyIdentity energyNontrivial hβ hEnergy

/-- Audit-visible Package F: actual invariant coarse embeddings, actual
transfer-fixed projectors, and one/two-step reduction of the previously
abstract strong obstruction to concrete transfer and ground-sector geometry. -/
structure Z2FiniteEvenFourTorusCrossVolumeGeometricOperatorCompatibilityPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  oneStepEmbedding :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗᵢ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H)
  oneStepEmbedding_eq : oneStepEmbedding =
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H
  twoStepEmbedding :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗᵢ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
  twoStepEmbedding_eq : twoStepEmbedding =
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H
  embeddingCocycle : ∀ f,
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry
        (finiteEvenFourTorusDoubleRefinement H) (oneStepEmbedding f) =
      twoStepEmbedding f
  coarseGroundProjector :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H
  coarseGroundProjector_eq : coarseGroundProjector =
    finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
      H β energyIdentity energyNontrivial hβ hEnergy
  coarseDefectDecomposition : ∀ f,
    finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ hEnergy f =
      f - finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy f +
        coarseGroundProjector f
  oneStepDefectResidual :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H)
  oneStepResidualDecomposition :
    oneStepDefectResidual =
      finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy -
        finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy
  oneStepOrbitCriterion :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy =
        finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy
  twoStepDefectResidual :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
  twoStepResidualDecomposition :
    twoStepDefectResidual =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy -
        finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy
  twoStepOrbitCriterion :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy =
        finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy

/-- Construct the complete actual Package-F compatibility receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeGeometricOperatorCompatibilityPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeGeometricOperatorCompatibilityPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  oneStepEmbedding :=
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H
  oneStepEmbedding_eq := rfl
  twoStepEmbedding :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H
  twoStepEmbedding_eq := rfl
  embeddingCocycle :=
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_twoStep_cocycle H
  coarseGroundProjector :=
    finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
      H β energyIdentity energyNontrivial hβ hEnergy
  coarseGroundProjector_eq := rfl
  coarseDefectDecomposition :=
    finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_apply_decomposition
      H β energyIdentity energyNontrivial hβ hEnergy
  oneStepDefectResidual :=
    finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidualLinearMap
      H β energyIdentity energyNontrivial hβ hEnergy
  oneStepResidualDecomposition :=
    finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidual_decomposition
      H β energyIdentity energyNontrivial hβ hEnergy
  oneStepOrbitCriterion :=
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_iff_transfer_eq_ground
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStepDefectResidual :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundLiftedDefectIntertwiningResidualLinearMap
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStepResidualDecomposition :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundLiftedDefectIntertwiningResidual_decomposition
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStepOrbitCriterion :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_iff_transfer_eq_ground
      H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D
