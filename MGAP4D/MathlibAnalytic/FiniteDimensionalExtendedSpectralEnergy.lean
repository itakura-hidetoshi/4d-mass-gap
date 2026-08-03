import MGAP4D.MathlibAnalytic.FiniteDimensionalFullSpectralNaturalTime
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Extended finite-volume spectral energy.  Positive transfer eigenvalues
carry the finite energy `-log λ`; transfer zero modes are represented by a
separate infinite-energy constructor rather than by a false real number. -/
inductive ExtendedSpectralEnergy where
  | finite (value : ℝ)
  | infinite
  deriving DecidableEq

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- Extended energy of a complete canonical transfer mode. -/
def extendedSpectralEnergy
    (i : Fin D.dimension) : ExtendedSpectralEnergy :=
  if D.eigenvalue i = 0 then
    ExtendedSpectralEnergy.infinite
  else
    ExtendedSpectralEnergy.finite (-Real.log (D.eigenvalue i))

/-- A mode has infinite extended energy exactly when it is a transfer zero
mode. -/
theorem extendedSpectralEnergy_eq_infinite_iff
    (i : Fin D.dimension) :
    D.extendedSpectralEnergy i = ExtendedSpectralEnergy.infinite ↔
      D.eigenvalue i = 0 := by
  simp [extendedSpectralEnergy]

/-- A mode has a finite extended energy exactly when its transfer eigenvalue
is nonzero. -/
theorem exists_extendedSpectralEnergy_eq_finite_iff
    (i : Fin D.dimension) :
    (∃ energy : ℝ,
        D.extendedSpectralEnergy i =
          ExtendedSpectralEnergy.finite energy) ↔
      D.eigenvalue i ≠ 0 := by
  constructor
  · rintro ⟨energy, henergy⟩ hz
    simp [extendedSpectralEnergy, hz] at henergy
  · intro hnz
    refine ⟨-Real.log (D.eigenvalue i), ?_⟩
    simp [extendedSpectralEnergy, hnz]

/-- Every finite extended spectral energy is nonnegative. -/
theorem extendedSpectralEnergy_finite_nonneg
    (i : Fin D.dimension)
    (energy : ℝ)
    (henergy : D.extendedSpectralEnergy i =
      ExtendedSpectralEnergy.finite energy) :
    0 ≤ energy := by
  have hnz : D.eigenvalue i ≠ 0 := by
    intro hz
    simp [extendedSpectralEnergy, hz] at henergy
  have hpos : 0 < D.eigenvalue i :=
    lt_of_le_of_ne (D.eigenvalue_nonneg i) (Ne.symm hnz)
  have hvalue : energy = -Real.log (D.eigenvalue i) := by
    simpa [extendedSpectralEnergy, hnz] using henergy.symm
  rw [hvalue]
  exact neg_nonneg.mpr
    (Real.log_nonpos (le_of_lt hpos) (D.eigenvalue_le_one i))

/-- Every ground mode has finite extended energy exactly zero. -/
theorem extendedSpectralEnergy_ground
    (i : D.GroundSpectralIndex) :
    D.extendedSpectralEnergy i.1 =
      ExtendedSpectralEnergy.finite 0 := by
  simp [extendedSpectralEnergy, i.2]

/-- Every strictly excited mode has its positive support energy as finite
extended energy. -/
theorem extendedSpectralEnergy_excited
    (i : D.ExcitedSpectralIndex) :
    D.extendedSpectralEnergy i.1 =
      ExtendedSpectralEnergy.finite
        (D.positiveSpectralEnergy i.toPositive) := by
  have hnz : D.eigenvalue i.1 ≠ 0 := ne_of_gt i.2.1
  simp [extendedSpectralEnergy, positiveSpectralEnergy,
    positiveEigenvalue, hnz]

/-- The finite extended energy of every strictly excited mode is strictly
positive. -/
theorem extendedSpectralEnergy_excited_pos
    (i : D.ExcitedSpectralIndex) :
    0 < D.positiveSpectralEnergy i.toPositive :=
  D.excitedSpectralEnergy_pos i

/-- Every null mode has infinite extended energy. -/
theorem extendedSpectralEnergy_null
    (i : D.NullSpectralIndex) :
    D.extendedSpectralEnergy i.1 =
      ExtendedSpectralEnergy.infinite := by
  simp [extendedSpectralEnergy, i.2]

/-- Complete energy classification of every canonical transfer mode. -/
theorem extendedSpectralEnergy_trichotomy
    (i : Fin D.dimension) :
    (D.extendedSpectralEnergy i =
        ExtendedSpectralEnergy.finite 0 ∧
      D.eigenvalue i = 1) ∨
    (∃ energy : ℝ,
      D.extendedSpectralEnergy i =
        ExtendedSpectralEnergy.finite energy ∧
      0 < energy ∧
      0 < D.eigenvalue i ∧ D.eigenvalue i < 1) ∨
    (D.extendedSpectralEnergy i =
        ExtendedSpectralEnergy.infinite ∧
      D.eigenvalue i = 0) := by
  rcases D.eigenvalue_trichotomy i with hz | he | hg
  · exact Or.inr (Or.inr ⟨by simp [extendedSpectralEnergy, hz], hz⟩)
  · let j : D.ExcitedSpectralIndex := ⟨i, he⟩
    refine Or.inr (Or.inl ⟨D.positiveSpectralEnergy j.toPositive, ?_,
      D.excitedSpectralEnergy_pos j, he⟩)
    exact D.extendedSpectralEnergy_excited j
  · exact Or.inl ⟨by simp [extendedSpectralEnergy, hg], hg⟩

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
