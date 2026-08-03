import MGAP4D.MathlibAnalytic.FiniteDimensionalGroundExcitationNullSpectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- Extend ground coordinates by zero inside the positive spectral support. -/
noncomputable def groundPositiveExtension :
    D.GroundSpectralSpace →ₗ[ℝ] D.PositiveSpectralSpace where
  toFun := fun x =>
    WithLp.toLp 2 (fun i =>
      if h : D.eigenvalue i.1 = 1 then x ⟨i.1, h⟩ else 0)
  map_add' := by
    intro x y
    ext i
    by_cases h : D.eigenvalue i.1 = 1 <;> simp [h]
  map_smul' := by
    intro c x
    ext i
    by_cases h : D.eigenvalue i.1 = 1 <;> simp [h]

/-- Extend strictly excited coordinates by zero inside the positive support. -/
noncomputable def excitedPositiveExtension :
    D.ExcitedSpectralSpace →ₗ[ℝ] D.PositiveSpectralSpace where
  toFun := fun x =>
    WithLp.toLp 2 (fun i =>
      if h : 0 < D.eigenvalue i.1 ∧ D.eigenvalue i.1 < 1 then
        x ⟨i.1, h⟩
      else 0)
  map_add' := by
    intro x y
    ext i
    by_cases h : 0 < D.eigenvalue i.1 ∧ D.eigenvalue i.1 < 1 <;> simp [h]
  map_smul' := by
    intro c x
    ext i
    by_cases h : 0 < D.eigenvalue i.1 ∧ D.eigenvalue i.1 < 1 <;> simp [h]

/-- Restrict positive-support coordinates to the ground indices. -/
noncomputable def positiveGroundCoordinates :
    D.PositiveSpectralSpace →ₗ[ℝ] D.GroundSpectralSpace where
  toFun := fun x =>
    WithLp.toLp 2 (fun i => x i.toPositive)
  map_add' := by
    intro x y
    ext i
    simp
  map_smul' := by
    intro c x
    ext i
    simp

/-- Restrict positive-support coordinates to the strictly excited indices. -/
noncomputable def positiveExcitedCoordinates :
    D.PositiveSpectralSpace →ₗ[ℝ] D.ExcitedSpectralSpace where
  toFun := fun x =>
    WithLp.toLp 2 (fun i => x i.toPositive)
  map_add' := by
    intro x y
    ext i
    simp
  map_smul' := by
    intro c x
    ext i
    simp

@[simp] theorem positiveGroundCoordinates_groundPositiveExtension
    (x : D.GroundSpectralSpace) :
    D.positiveGroundCoordinates (D.groundPositiveExtension x) = x := by
  ext i
  simp [positiveGroundCoordinates, groundPositiveExtension, i.2]

@[simp] theorem positiveExcitedCoordinates_excitedPositiveExtension
    (x : D.ExcitedSpectralSpace) :
    D.positiveExcitedCoordinates (D.excitedPositiveExtension x) = x := by
  ext i
  simp [positiveExcitedCoordinates, excitedPositiveExtension, i.2]

/-- Every positive-support vector is the exact sum of its ground and excited
coordinate sectors. -/
theorem positiveSpectral_ground_add_excited
    (x : D.PositiveSpectralSpace) :
    D.groundPositiveExtension (D.positiveGroundCoordinates x) +
        D.excitedPositiveExtension (D.positiveExcitedCoordinates x) = x := by
  ext i
  by_cases hg : D.eigenvalue i.1 = 1
  · have hne : ¬(0 < D.eigenvalue i.1 ∧ D.eigenvalue i.1 < 1) :=
      D.ground_not_excited i.1 hg
    simp [groundPositiveExtension, excitedPositiveExtension,
      positiveGroundCoordinates, positiveExcitedCoordinates, hg, hne]
  · have he : 0 < D.eigenvalue i.1 ∧ D.eigenvalue i.1 < 1 := by
      exact ⟨i.2, lt_of_le_of_ne (D.eigenvalue_le_one i.1) hg⟩
    simp [groundPositiveExtension, excitedPositiveExtension,
      positiveGroundCoordinates, positiveExcitedCoordinates, hg, he]

/-- The ground and excited coordinate ranges are orthogonal inside the positive
spectral support. -/
theorem groundPositiveExtension_orthogonal_excitedPositiveExtension
    (x : D.GroundSpectralSpace)
    (y : D.ExcitedSpectralSpace) :
    inner ℝ (D.groundPositiveExtension x) (D.excitedPositiveExtension y) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  by_cases hg : D.eigenvalue i.1 = 1
  · have hne : ¬(0 < D.eigenvalue i.1 ∧ D.eigenvalue i.1 < 1) :=
      D.ground_not_excited i.1 hg
    simp [groundPositiveExtension, excitedPositiveExtension, hg, hne]
  · simp [groundPositiveExtension, excitedPositiveExtension, hg]

/-- Ground coordinates are fixed by the positive-support transfer. -/
theorem positiveSpectralTransfer_groundPositiveExtension
    (x : D.GroundSpectralSpace) :
    D.positiveSpectralTransfer (D.groundPositiveExtension x) =
      D.groundPositiveExtension x := by
  ext i
  by_cases hg : D.eigenvalue i.1 = 1
  · simp [groundPositiveExtension, positiveSpectralTransfer_apply,
      positiveEigenvalue, hg]
  · simp [groundPositiveExtension, positiveSpectralTransfer_apply, hg]

/-- The support Hamiltonian vanishes identically on the ground sector. -/
theorem positiveSpectralHamiltonian_groundPositiveExtension
    (x : D.GroundSpectralSpace) :
    D.positiveSpectralHamiltonian (D.groundPositiveExtension x) = 0 := by
  ext i
  by_cases hg : D.eigenvalue i.1 = 1
  · simp [groundPositiveExtension, positiveSpectralHamiltonian_apply,
      positiveSpectralEnergy, positiveEigenvalue, hg]
  · simp [groundPositiveExtension, positiveSpectralHamiltonian_apply, hg]

/-- Every excited coordinate has strictly positive support energy. -/
theorem excitedSpectralEnergy_pos
    (i : D.ExcitedSpectralIndex) :
    0 < D.positiveSpectralEnergy i.toPositive := by
  unfold positiveSpectralEnergy positiveEigenvalue
  exact neg_pos.mpr (Real.log_neg i.2.1 i.2.2)

/-- A positive-support vector is fixed by the transfer exactly when all of its
excited coordinates vanish. -/
theorem positiveSpectralTransfer_eq_self_iff
    (x : D.PositiveSpectralSpace) :
    D.positiveSpectralTransfer x = x ↔
      ∀ i : D.ExcitedSpectralIndex, x i.toPositive = 0 := by
  constructor
  · intro h i
    have hi := congrArg (fun z : D.PositiveSpectralSpace => z i.toPositive) h
    rw [D.positiveSpectralTransfer_apply] at hi
    change D.eigenvalue i.1 * x i.toPositive = x i.toPositive at hi
    nlinarith [i.2.2]
  · intro h
    ext i
    by_cases hg : D.eigenvalue i.1 = 1
    · simp [D.positiveSpectralTransfer_apply, positiveEigenvalue, hg]
    · have he : 0 < D.eigenvalue i.1 ∧ D.eigenvalue i.1 < 1 :=
        ⟨i.2, lt_of_le_of_ne (D.eigenvalue_le_one i.1) hg⟩
      have hz := h ⟨i.1, he⟩
      simpa [D.positiveSpectralTransfer_apply, positiveEigenvalue, hz]

/-- The kernel of the support Hamiltonian consists exactly of vectors with no
excited coordinates. -/
theorem positiveSpectralHamiltonian_eq_zero_iff
    (x : D.PositiveSpectralSpace) :
    D.positiveSpectralHamiltonian x = 0 ↔
      ∀ i : D.ExcitedSpectralIndex, x i.toPositive = 0 := by
  constructor
  · intro h i
    have hi := congrArg (fun z : D.PositiveSpectralSpace => z i.toPositive) h
    rw [D.positiveSpectralHamiltonian_apply] at hi
    change D.positiveSpectralEnergy i.toPositive * x i.toPositive = 0 at hi
    exact (mul_eq_zero.mp hi).resolve_left (ne_of_gt (D.excitedSpectralEnergy_pos i))
  · intro h
    ext i
    by_cases hg : D.eigenvalue i.1 = 1
    · simp [D.positiveSpectralHamiltonian_apply,
        positiveSpectralEnergy, positiveEigenvalue, hg]
    · have he : 0 < D.eigenvalue i.1 ∧ D.eigenvalue i.1 < 1 :=
        ⟨i.2, lt_of_le_of_ne (D.eigenvalue_le_one i.1) hg⟩
      have hz := h ⟨i.1, he⟩
      simpa [D.positiveSpectralHamiltonian_apply, hz]

/-- Fixed points of the positive-support transfer are precisely zero-energy
vectors of the support Hamiltonian. -/
theorem positiveSpectralTransfer_eq_self_iff_hamiltonian_eq_zero
    (x : D.PositiveSpectralSpace) :
    D.positiveSpectralTransfer x = x ↔
      D.positiveSpectralHamiltonian x = 0 := by
  rw [D.positiveSpectralTransfer_eq_self_iff,
    D.positiveSpectralHamiltonian_eq_zero_iff]

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
