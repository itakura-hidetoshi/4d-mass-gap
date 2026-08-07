import MGAP4D.MathlibAnalytic.FiniteIdempotentPositiveContractionGroundProjector
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeBetaZeroNormalizedTransferIntertwining
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- At `β = 0`, the actual normalized invariant transfer is an idempotent
uniform-averaging operator. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_beta_zero_idempotent
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy f) =
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy f := by
  apply Subtype.ext
  ext A
  rw [finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_apply_coe_beta_zero]
  simp_rw [finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_apply_coe_beta_zero]
  rw [finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_apply_coe_beta_zero]
  have hcard :
      (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [hcard]

/-- Therefore the canonical Mathlib eigenvalue-one spectral projector of the
actual `β = 0` transfer is exactly the normalized transfer itself. -/
theorem finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector_beta_zero_eq_transfer
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy =
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy := by
  unfold finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
  let D := finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy
  have hIdem : ∀ f,
      D.operator (D.operator f) = D.operator f := by
    intro f
    change
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy
          (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
            H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy f) =
        finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy f
    exact finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_beta_zero_idempotent
      H energyIdentity energyNontrivial hEnergy f
  have hProj := D.groundSpectralProjector_eq_operator_of_idempotent hIdem
  simpa [D, finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData] using hProj

/-- At zero coupling the ground-lifted defect itself collapses to the identity:
`I - T + P_ground = I` because `P_ground = T`. -/
theorem finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_beta_zero_apply
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy f = f := by
  rw [finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_apply_decomposition]
  rw [finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector_beta_zero_eq_transfer]
  module

/-- The canonical one-step ground spectral projectors intertwine exactly at
`β = 0`. -/
theorem finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidual_beta_zero_eq_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy = 0 := by
  apply LinearMap.ext
  intro f
  rw [finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidualLinearMap_apply]
  rw [finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector_beta_zero_eq_transfer]
  rw [finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector_beta_zero_eq_transfer]
  have hTransfer := LinearMap.congr_fun
    (finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_beta_zero_eq_zero
      H energyIdentity energyNontrivial hEnergy) f
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap_apply]
    at hTransfer
  exact hTransfer

/-- The direct two-step ground spectral projectors also intertwine exactly at
zero coupling. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidual_beta_zero_eq_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy = 0 := by
  apply LinearMap.ext
  intro f
  change
    finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        0 energyIdentity energyNontrivial (le_refl 0) hEnergy
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H f) -
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H
        (finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy f) = 0
  rw [finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector_beta_zero_eq_transfer]
  rw [finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector_beta_zero_eq_transfer]
  have hTransfer := LinearMap.congr_fun
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_beta_zero_eq_zero
      H energyIdentity energyNontrivial hEnergy) f
  exact hTransfer

/-- The actual one-step ground-lifted defect residual vanishes at `β = 0`.
Here the conclusion is stronger than a cancellation between nonzero components:
both transfer and ground-projector residuals vanish separately. -/
theorem finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidual_beta_zero_eq_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy = 0 := by
  rw [finiteEvenFourTorusZ2GaugeInvariantGroundLiftedDefectIntertwiningResidual_decomposition]
  rw [finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidual_beta_zero_eq_zero]
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_beta_zero_eq_zero]
  simp

/-- Consequently the canonical orbit-probability ground-lifted obstruction also
vanishes at one refinement step. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_beta_zero_eq_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy = 0 := by
  apply
    (finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_iff_transfer_eq_ground
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy).2
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_beta_zero_eq_zero]
  rw [finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidual_beta_zero_eq_zero]

/-- The direct two-step orbit-probability ground-lifted obstruction vanishes as
well. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_beta_zero_eq_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy = 0 := by
  apply
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_iff_transfer_eq_ground
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy).2
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_beta_zero_eq_zero]
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidual_beta_zero_eq_zero]

/-- Audit-visible β=0 closure: raw transfer compatibility fails, exact
operator-norm-normalized transfer compatibility succeeds, the canonical ground
projector is the normalized transfer, and the resulting one-step/direct-two-step
ground-lifted obstructions vanish. -/
structure Z2FiniteEvenFourTorusCrossVolumeBetaZeroGroundLiftedPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  normalizedTransfer :
    Z2FiniteEvenFourTorusCrossVolumeBetaZeroNormalizedTransferPackage
      H energyIdentity energyNontrivial hEnergy
  transferIdempotent : ∀ f,
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy f) =
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy f
  groundProjectorEqTransfer :
    finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy =
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy
  groundLiftedDefectIsIdentity : ∀ f,
    finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy f = f
  oneStepGroundResidualZero :
    finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy = 0
  twoStepGroundResidualZero :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy = 0
  oneStepGroundLiftedZero :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy = 0
  twoStepGroundLiftedZero :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy = 0

/-- Construct the complete β=0 normalized/ground-lifted closure package. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeBetaZeroGroundLiftedPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeBetaZeroGroundLiftedPackage
      H energyIdentity energyNontrivial hEnergy where
  normalizedTransfer :=
    z2FiniteEvenFourTorusCrossVolumeBetaZeroNormalizedTransferPackage
      H energyIdentity energyNontrivial hEnergy
  transferIdempotent :=
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_beta_zero_idempotent
      H energyIdentity energyNontrivial hEnergy
  groundProjectorEqTransfer :=
    finiteEvenFourTorusZ2GeometricDoobGroundSpectralProjector_beta_zero_eq_transfer
      H energyIdentity energyNontrivial hEnergy
  groundLiftedDefectIsIdentity :=
    finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect_beta_zero_apply
      H energyIdentity energyNontrivial hEnergy
  oneStepGroundResidualZero :=
    finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidual_beta_zero_eq_zero
      H energyIdentity energyNontrivial hEnergy
  twoStepGroundResidualZero :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidual_beta_zero_eq_zero
      H energyIdentity energyNontrivial hEnergy
  oneStepGroundLiftedZero :=
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_beta_zero_eq_zero
      H energyIdentity energyNontrivial hEnergy
  twoStepGroundLiftedZero :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_beta_zero_eq_zero
      H energyIdentity energyNontrivial hEnergy

end

end MathlibAnalytic
end MGAP4D
