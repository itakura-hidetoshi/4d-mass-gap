import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeOneSlabNontriviality
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The residue class of one is nonzero in every spatial modulus occurring in
an even four-torus. -/
theorem finiteEvenFourTorusSpatialModulus_one_ne_zero
    (H : ℕ) :
    (1 : ZMod ((2 * H + 1) + 1)) ≠ 0 := by
  intro h
  have horder := congrArg addOrderOf h
  have hmod : (2 * H + 1) + 1 = 1 := by
    simpa using horder
  omega

/-- Canonical time-zero vertex used uniformly at every finite side parameter. -/
def finiteEvenFourTorusZ2AllVolumeWitnessVertex
    (H : ℕ) : FiniteEvenFourTorusSpatialVertex H :=
  ⟨fun _ => 0, rfl⟩

/-- Uniform distinguished spatial plaquette. -/
def finiteEvenFourTorusZ2AllVolumeWitnessPlaquette
    (H : ℕ) : FiniteEvenFourTorusSpatialPlaquette H :=
  (finiteEvenFourTorusZ2AllVolumeWitnessVertex H,
    ⟨(finiteEvenFourTorusZ2GaussWitnessDirectionOne,
       finiteEvenFourTorusZ2GaussWitnessDirectionTwo), by decide⟩)

/-- Uniform distinguished first edge of the witness plaquette. -/
def finiteEvenFourTorusZ2AllVolumeWitnessLink
    (H : ℕ) : FiniteEvenFourTorusSpatialLink H :=
  (finiteEvenFourTorusZ2AllVolumeWitnessVertex H,
    finiteEvenFourTorusZ2GaussWitnessDirectionOne)

/-- A spatial unit step in the second witness direction moves the zero vertex
at every finite side parameter. -/
theorem finiteEvenFourTorusZ2AllVolumeWitnessVertex_step_two_ne
    (H : ℕ) :
    finiteEvenFourTorusSpatialVertexStep H
        (finiteEvenFourTorusZ2AllVolumeWitnessVertex H)
        finiteEvenFourTorusZ2GaussWitnessDirectionTwo ≠
      finiteEvenFourTorusZ2AllVolumeWitnessVertex H := by
  intro h
  have hcoord := congrArg
    (fun v : FiniteEvenFourTorusSpatialVertex H =>
      v.1 finiteEvenFourTorusZ2GaussWitnessDirectionTwo.1) h
  have hone :
      (1 : ZMod ((2 * H + 1) + 1)) = 0 := by
    simpa [finiteEvenFourTorusSpatialVertexStep,
      finiteFourTorusStep, finiteFourTorusUnitStep,
      finiteEvenFourTorusZ2AllVolumeWitnessVertex] using hcoord
  exact finiteEvenFourTorusSpatialModulus_one_ne_zero H hone

/-- The identity slice has trivial witness-plaquette holonomy at every finite
side parameter. -/
theorem finiteEvenFourTorusZ2AllVolumeWitness_identity_holonomy
    (H : ℕ) :
    finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H
      (finiteEvenFourTorusZ2IdentitySlice H)
      (finiteEvenFourTorusZ2AllVolumeWitnessPlaquette H) = 1 := by
  simp [finiteEvenFourTorusZ2SpatialPlaquetteHolonomy,
    finiteEvenFourTorusZ2IdentitySlice]

/-- Exciting the first edge changes the witness plaquette holonomy at every
finite side parameter. -/
theorem finiteEvenFourTorusZ2AllVolumeWitness_excitation_holonomy
    (H : ℕ) :
    finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H
      (finiteEvenFourTorusZ2SingleLinkExcitation H
        (finiteEvenFourTorusZ2AllVolumeWitnessLink H))
      (finiteEvenFourTorusZ2AllVolumeWitnessPlaquette H) =
        z2GaugeNontrivial := by
  have hdir :
      finiteEvenFourTorusZ2GaussWitnessDirectionTwo ≠
        finiteEvenFourTorusZ2GaussWitnessDirectionOne := by decide
  have hstep :=
    finiteEvenFourTorusZ2AllVolumeWitnessVertex_step_two_ne H
  simp [finiteEvenFourTorusZ2SpatialPlaquetteHolonomy,
    finiteEvenFourTorusZ2SingleLinkExcitation,
    finiteEvenFourTorusZ2AllVolumeWitnessPlaquette,
    finiteEvenFourTorusZ2AllVolumeWitnessLink,
    hdir, hstep]

/-- The identity slice and the one-edge excitation lie in distinct residual
slice-gauge orbits for every finite side parameter. -/
theorem finiteEvenFourTorusZ2AllVolumeWitness_not_gauge_related
    (H : ℕ) :
    ∀ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
      g • finiteEvenFourTorusZ2IdentitySlice H ≠
        finiteEvenFourTorusZ2SingleLinkExcitation H
          (finiteEvenFourTorusZ2AllVolumeWitnessLink H) := by
  intro g h
  have hhol := congrArg
    (fun A : FiniteEvenFourTorusZ2SliceConfiguration H =>
      finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H A
        (finiteEvenFourTorusZ2AllVolumeWitnessPlaquette H)) h
  change
    finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H
        (g • finiteEvenFourTorusZ2IdentitySlice H)
        (finiteEvenFourTorusZ2AllVolumeWitnessPlaquette H) =
      finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H
        (finiteEvenFourTorusZ2SingleLinkExcitation H
          (finiteEvenFourTorusZ2AllVolumeWitnessLink H))
        (finiteEvenFourTorusZ2AllVolumeWitnessPlaquette H) at hhol
  rw [finiteEvenFourTorusZ2SpatialPlaquetteHolonomy_smul,
    finiteEvenFourTorusZ2AllVolumeWitness_identity_holonomy,
    finiteEvenFourTorusZ2AllVolumeWitness_excitation_holonomy] at hhol
  exact (by native_decide : (1 : Z2Gauge) ≠ z2GaugeNontrivial) hhol

/-- Gauge-invariant orbit state of the identity boundary slice at arbitrary
finite side parameter. -/
noncomputable def finiteEvenFourTorusZ2AllVolumeWitnessIdentityState
    (H : ℕ) : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
  finiteGroupInvariantOrbitIndicator
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2IdentitySlice H)

/-- Gauge-invariant orbit state of the plaquette-excited boundary slice. -/
noncomputable def finiteEvenFourTorusZ2AllVolumeWitnessExcitationState
    (H : ℕ) : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
  finiteGroupInvariantOrbitIndicator
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2SingleLinkExcitation H
      (finiteEvenFourTorusZ2AllVolumeWitnessLink H))

/-- The two all-volume gauge-invariant witness states are orthogonal. -/
theorem finiteEvenFourTorusZ2AllVolumeWitnessStates_orthogonal
    (H : ℕ) :
    inner ℝ (finiteEvenFourTorusZ2AllVolumeWitnessIdentityState H)
      (finiteEvenFourTorusZ2AllVolumeWitnessExcitationState H) = 0 :=
  finiteGroupOrbitIndicator_inner_eq_zero_of_not_related
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2IdentitySlice H)
    (finiteEvenFourTorusZ2SingleLinkExcitation H
      (finiteEvenFourTorusZ2AllVolumeWitnessLink H))
    (finiteEvenFourTorusZ2AllVolumeWitness_not_gauge_related H)

/-- The temporal-link averaged normalized transfer has a strictly positive
matrix entry between the two all-volume orbit states. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_allVolume_witness_matrix_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    0 < inner ℝ
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2AllVolumeWitnessIdentityState H))
      (finiteEvenFourTorusZ2AllVolumeWitnessExcitationState H) := by
  change 0 < inner ℝ
    (finiteKernelNormalizedOperator
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy)
      (finiteGroupOrbitIndicator
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2IdentitySlice H)))
    (finiteGroupOrbitIndicator
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (finiteEvenFourTorusZ2SingleLinkExcitation H
        (finiteEvenFourTorusZ2AllVolumeWitnessLink H)))
  exact finiteKernelNormalizedOperator_orbitIndicator_matrixElement_pos
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer_ne_zero
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_pos
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2IdentitySlice H)
    (finiteEvenFourTorusZ2SingleLinkExcitation H
      (finiteEvenFourTorusZ2AllVolumeWitnessLink H))

/-- The exact temporal-link averaged invariant transfer is nonidentity at every
finite side parameter. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_allVolume_ne_identity
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy ≠ 1 := by
  intro hId
  have hmatrix := congrArg
    (fun T : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →L[ℝ]
        FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H =>
      inner ℝ (T (finiteEvenFourTorusZ2AllVolumeWitnessIdentityState H))
        (finiteEvenFourTorusZ2AllVolumeWitnessExcitationState H)) hId
  have hpos :=
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_allVolume_witness_matrix_pos
      H β energyIdentity energyNontrivial hβ hEnergy
  change inner ℝ
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2AllVolumeWitnessIdentityState H))
      (finiteEvenFourTorusZ2AllVolumeWitnessExcitationState H) =
    inner ℝ (finiteEvenFourTorusZ2AllVolumeWitnessIdentityState H)
      (finiteEvenFourTorusZ2AllVolumeWitnessExcitationState H) at hmatrix
  rw [finiteEvenFourTorusZ2AllVolumeWitnessStates_orthogonal] at hmatrix
  rw [hmatrix] at hpos
  exact (lt_irrefl 0) hpos

end

end MathlibAnalytic
end MGAP4D
