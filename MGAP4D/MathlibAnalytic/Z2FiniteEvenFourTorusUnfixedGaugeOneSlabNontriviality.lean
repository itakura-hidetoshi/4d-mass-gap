import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGaussProjectedOneSlabNontriviality
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeOneSlabTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- The normalized unfixed-gauge transfer has a strictly positive matrix entry
between the two plaquette-separated gauge-invariant orbit states. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_witness_matrix_pos
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    0 < inner ℝ
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        0 β energyIdentity energyNontrivial hβ hEnergy
        finiteEvenFourTorusZ2GaussWitnessIdentityState)
      finiteEvenFourTorusZ2GaussWitnessExcitationState := by
  change 0 < inner ℝ
    (finiteKernelNormalizedOperator
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        0 β energyIdentity energyNontrivial hβ hEnergy)
      (finiteGroupOrbitIndicator
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup 0)
        (FiniteEvenFourTorusZ2SliceConfiguration 0)
        (finiteEvenFourTorusZ2IdentitySlice 0)))
    (finiteGroupOrbitIndicator
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup 0)
      (FiniteEvenFourTorusZ2SliceConfiguration 0)
      (finiteEvenFourTorusZ2SingleLinkExcitation 0
        finiteEvenFourTorusZ2GaussWitnessLink))
  exact finiteKernelNormalizedOperator_orbitIndicator_matrixElement_pos
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup 0)
    (FiniteEvenFourTorusZ2SliceConfiguration 0)
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
      0 β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer_ne_zero
      0 β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_pos
      0 β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2IdentitySlice 0)
    (finiteEvenFourTorusZ2SingleLinkExcitation 0
      finiteEvenFourTorusZ2GaussWitnessLink)

/-- The exact temporal-link averaged transfer is explicitly nonidentity on the
plaquette-separated gauge-invariant sector. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_ne_identity
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        0 β energyIdentity energyNontrivial hβ hEnergy ≠ 1 := by
  intro hId
  have hmatrix := congrArg
    (fun T : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0 →L[ℝ]
        FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0 =>
      inner ℝ (T finiteEvenFourTorusZ2GaussWitnessIdentityState)
        finiteEvenFourTorusZ2GaussWitnessExcitationState) hId
  have hpos :=
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_witness_matrix_pos
      β energyIdentity energyNontrivial hβ hEnergy
  change inner ℝ
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        0 β energyIdentity energyNontrivial hβ hEnergy
        finiteEvenFourTorusZ2GaussWitnessIdentityState)
      finiteEvenFourTorusZ2GaussWitnessExcitationState =
    inner ℝ finiteEvenFourTorusZ2GaussWitnessIdentityState
      finiteEvenFourTorusZ2GaussWitnessExcitationState at hmatrix
  rw [finiteEvenFourTorusZ2GaussWitnessStates_orthogonal] at hmatrix
  rw [hmatrix] at hpos
  exact (lt_irrefl 0) hpos

end

end MathlibAnalytic
end MGAP4D
