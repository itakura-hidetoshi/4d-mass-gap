import MGAP4D.MathlibAnalytic.FiniteDimensionalFullGroundExcitationNullDecomposition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- The unique canonical ground index when the ground spectral sector is
inhabited and subsingleton. -/
noncomputable def canonicalGroundIndex
    [Nonempty D.GroundSpectralIndex] : D.GroundSpectralIndex :=
  Classical.choice inferInstance

/-- The canonical normalized ground vector selected from the Mathlib
orthonormal eigenbasis. -/
noncomputable def canonicalGroundVector
    [Nonempty D.GroundSpectralIndex] : E :=
  D.eigenbasis D.canonicalGroundIndex.1

@[simp] theorem norm_canonicalGroundVector
    [Nonempty D.GroundSpectralIndex] :
    ‖D.canonicalGroundVector‖ = 1 := by
  simp [canonicalGroundVector]

/-- The canonical ground vector is fixed by the positive contraction. -/
theorem operator_canonicalGroundVector
    [Nonempty D.GroundSpectralIndex] :
    D.operator D.canonicalGroundVector = D.canonicalGroundVector := by
  rw [canonicalGroundVector, D.operator_apply_eigenbasis,
    D.canonicalGroundIndex.2, one_smul]

/-- Exact Rayleigh expansion of a finite-dimensional symmetric positive
contraction in the coordinate system of its canonical orthonormal eigenbasis. -/
theorem operator_rayleigh_eigenbasis_coordinates
    (x : E) :
    inner ℝ (D.operator x) x =
      ∑ i : Fin D.dimension,
        D.eigenvalue i * (D.eigenbasis.repr x i) ^ 2 := by
  have hDiagonal (i : Fin D.dimension) :
      D.eigenbasis.repr (D.operator x) i =
        D.eigenvalue i * D.eigenbasis.repr x i := by
    simpa [eigenbasis, eigenvalue] using
      D.symmetric.eigenvectorBasis_apply_self_apply (by rfl) x i
  calc
    inner ℝ (D.operator x) x =
        inner ℝ (D.eigenbasis.repr (D.operator x))
          (D.eigenbasis.repr x) := by
      exact (D.eigenbasis.repr.inner_map_map (D.operator x) x).symm
    _ = ∑ i : Fin D.dimension,
        D.eigenvalue i * (D.eigenbasis.repr x i) ^ 2 := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hDiagonal i]
      change
        D.eigenbasis.repr x i *
            (D.eigenvalue i * D.eigenbasis.repr x i) =
          D.eigenvalue i * (D.eigenbasis.repr x i) ^ 2
      ring

/-- Parseval identity for the canonical eigenbasis in coordinate form. -/
theorem sum_sq_eigenbasis_coordinates
    (x : E) :
    ∑ i : Fin D.dimension, (D.eigenbasis.repr x i) ^ 2 = ‖x‖ ^ 2 := by
  rw [← EuclideanSpace.real_norm_sq_eq]
  rw [D.eigenbasis.repr.norm_map]

/-- A common upper bound on all strictly excited eigenvalues implies a
basis-free Rayleigh contraction on states with vanishing ground coordinates,
provided the null sector is absent. -/
theorem operator_quadraticForm_le_of_groundCoordinates_eq_zero_of_excited_cap
    (hnull : ¬ Nonempty D.NullSpectralIndex)
    (rate : ℝ)
    (hcap : ∀ i : D.ExcitedSpectralIndex,
      D.eigenvalue i.1 ≤ rate)
    (x : E)
    (hx : D.groundCoordinates x = 0) :
    inner ℝ (D.operator x) x ≤ rate * ‖x‖ ^ 2 := by
  rw [D.operator_rayleigh_eigenbasis_coordinates x]
  calc
    (∑ i : Fin D.dimension,
        D.eigenvalue i * (D.eigenbasis.repr x i) ^ 2) ≤
      ∑ i : Fin D.dimension,
        rate * (D.eigenbasis.repr x i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      rcases D.eigenvalue_trichotomy i with hz | he | hg
      · exact False.elim (hnull ⟨⟨i, hz⟩⟩)
      · exact mul_le_mul_of_nonneg_right
          (hcap ⟨i, he⟩) (sq_nonneg _)
      · have hcoord := congrArg
          (fun y : D.GroundSpectralSpace => y ⟨i, hg⟩) hx
        change D.eigenbasis.repr x i = 0 at hcoord
        simp [hg, hcoord]
    _ = rate * ‖x‖ ^ 2 := by
      rw [← Finset.mul_sum, D.sum_sq_eigenbasis_coordinates x]

/-- Conversely, a basis-free Rayleigh contraction on the zero-ground-coordinate
sector bounds every strictly excited transfer eigenvalue by the same rate. -/
theorem excited_eigenvalue_le_of_operator_quadraticForm_le_of_groundCoordinates_eq_zero
    (rate : ℝ)
    (hRayleigh : ∀ x : E,
      D.groundCoordinates x = 0 →
        inner ℝ (D.operator x) x ≤ rate * ‖x‖ ^ 2)
    (i : D.ExcitedSpectralIndex) :
    D.eigenvalue i.1 ≤ rate := by
  have hcenter : D.groundCoordinates (D.eigenbasis i.1) = 0 := by
    ext j
    change D.eigenbasis.repr (D.eigenbasis i.1) j.1 = 0
    have hne : j.1 ≠ i.1 := by
      intro hji
      have hground : D.eigenvalue i.1 = 1 := by
        simpa [hji] using j.2
      exact (ne_of_lt i.2.2) hground
    simp [hne]
  have hbound := hRayleigh (D.eigenbasis i.1) hcenter
  calc
    D.eigenvalue i.1 =
        inner ℝ (D.operator (D.eigenbasis i.1)) (D.eigenbasis i.1) := by
      rw [D.operator_apply_eigenbasis i.1, inner_smul_left,
        real_inner_self_eq_norm_sq]
      simp
    _ ≤ rate * ‖D.eigenbasis i.1‖ ^ 2 := hbound
    _ = rate := by simp

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
