import MGAP4D.MathlibAnalytic.FiniteDimensionalPositiveSpectralSupportNontriviality
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeOneSlabNontriviality
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- Generic finite-dimensional positive-contraction data carried by the actual
Gauss-invariant unfixed-gauge finite `Z₂` one-slab transfer. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteDimensionalSymmetricPositiveContractionData
      (FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :=
  { operator :=
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy
    symmetric :=
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_isSymmetric
        H β energyIdentity energyNontrivial hβ hEnergy
    quadratic_nonneg :=
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_quadratic_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy
    norm_apply_le :=
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_norm_apply_le
        H β energyIdentity energyNontrivial hβ hEnergy }

/-- Actual finite-volume invariant transfer spectral dimension. -/
def finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralDimension
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : ℕ :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).dimension

/-- Canonical Mathlib eigenbasis of the actual invariant unfixed transfer. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeInvariantEigenbasis
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    OrthonormalBasis
      (Fin (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralDimension
        H β energyIdentity energyNontrivial hβ hEnergy))
      ℝ (FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).eigenbasis

/-- Canonical real transfer eigenvalue attached to the actual Mathlib basis. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeInvariantEigenvalue
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (i : Fin (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralDimension
      H β energyIdentity energyNontrivial hβ hEnergy)) : ℝ :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).eigenvalue i

/-- Every actual invariant unfixed-transfer eigenvalue lies in `[0,1]`. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantEigenvalue_mem_unitInterval
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (i : Fin (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralDimension
      H β energyIdentity energyNontrivial hβ hEnergy)) :
    finiteEvenFourTorusZ2UnfixedGaugeInvariantEigenvalue
        H β energyIdentity energyNontrivial hβ hEnergy i ∈
      Set.Icc (0 : ℝ) 1 :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).eigenvalue_mem_unitInterval i

/-- Positive spectral-support indices of the actual invariant unfixed transfer. -/
abbrev FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralIndex
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Type :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).PositiveSpectralIndex

/-- Positive spectral-support Hilbert space of the actual transfer. -/
abbrev FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Type :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).PositiveSpectralSpace

/-- The side-two actual invariant unfixed transfer is nonzero. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_ne_zero
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        0 β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  intro hzero
  have hpos :=
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_witness_matrix_pos
      β energyIdentity energyNontrivial hβ hEnergy
  rw [hzero] at hpos
  simpa using hpos

/-- Consequently, the side-two actual transfer has nonempty strictly positive
spectral support. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralIndex_nonempty
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralIndex
        0 β energyIdentity energyNontrivial hβ hEnergy) :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    0 β energyIdentity energyNontrivial hβ hEnergy).nonempty_positiveSpectralIndex_of_operator_ne_zero
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_ne_zero
        β energyIdentity energyNontrivial hβ hEnergy)

end

end MathlibAnalytic
end MGAP4D
