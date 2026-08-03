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
contraction in its canonical orthonormal eigenbasis. -/
theorem operator_rayleigh_eigenbasis
    (x : E) :
    inner ℝ (D.operator x) x =
      ∑ i : Fin D.dimension,
        (inner ℝ (D.eigenbasis i) x) ^ 2 * D.eigenvalue i := by
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
    _ = ∑ i : Fin D.dimension,
        (inner ℝ (D.eigenbasis i) x) ^ 2 * D.eigenvalue i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [D.eigenbasis.repr_apply]
      ring

/-- Parseval identity for the canonical eigenbasis, in the coefficient form
used by the centered Rayleigh comparison. -/
theorem sum_sq_inner_eigenbasis
    (x : E) :
    ∑ i : Fin D.dimension,
        (inner ℝ (D.eigenbasis i) x) ^ 2 = ‖x‖ ^ 2 := by
  simpa using OrthonormalBasis.sum_sq_inner_right D.eigenbasis x

/-- A common upper bound on all strictly excited eigenvalues implies the
basis-free Rayleigh contraction on the orthogonal complement of the unique
ground vector, provided the null sector is absent. -/
theorem operator_quadraticForm_le_on_canonicalGroundOrthogonal_of_excited_cap
    [Nonempty D.GroundSpectralIndex]
    [Subsingleton D.GroundSpectralIndex]
    (hnull : ¬ Nonempty D.NullSpectralIndex)
    (rate : ℝ)
    (hrate_nonneg : 0 ≤ rate)
    (hcap : ∀ i : D.ExcitedSpectralIndex,
      D.eigenvalue i.1 ≤ rate)
    (x : E)
    (hx : inner ℝ D.canonicalGroundVector x = 0) :
    inner ℝ (D.operator x) x ≤ rate * ‖x‖ ^ 2 := by
  rw [D.operator_rayleigh_eigenbasis x]
  calc
    (∑ i : Fin D.dimension,
        (inner ℝ (D.eigenbasis i) x) ^ 2 * D.eigenvalue i) ≤
      ∑ i : Fin D.dimension,
        rate * (inner ℝ (D.eigenbasis i) x) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      rcases D.eigenvalue_trichotomy i with hz | he | hg
      · exact False.elim (hnull ⟨⟨i, hz⟩⟩)
      · have hi := hcap ⟨i, he⟩
        nlinarith [sq_nonneg (inner ℝ (D.eigenbasis i) x)]
      · have hground :
            (⟨i, hg⟩ : D.GroundSpectralIndex) =
              D.canonicalGroundIndex :=
          Subsingleton.elim _ _
        have hindex : i = D.canonicalGroundIndex.1 :=
          congrArg Subtype.val hground
        have hcoeff : inner ℝ (D.eigenbasis i) x = 0 := by
          simpa [canonicalGroundVector, hindex] using hx
        simp [hcoeff, hrate_nonneg]
    _ = rate * ‖x‖ ^ 2 := by
      rw [← Finset.mul_sum, D.sum_sq_inner_eigenbasis x]

/-- Conversely, a basis-free Rayleigh contraction on the canonical
vacuum-orthogonal sector bounds every strictly excited transfer eigenvalue by
the same rate. -/
theorem excited_eigenvalue_le_of_operator_quadraticForm_le_on_canonicalGroundOrthogonal
    [Nonempty D.GroundSpectralIndex]
    (rate : ℝ)
    (hRayleigh : ∀ x : E,
      inner ℝ D.canonicalGroundVector x = 0 →
        inner ℝ (D.operator x) x ≤ rate * ‖x‖ ^ 2)
    (i : D.ExcitedSpectralIndex) :
    D.eigenvalue i.1 ≤ rate := by
  have hne : D.canonicalGroundIndex.1 ≠ i.1 := by
    intro h
    have hground : D.eigenvalue i.1 = 1 := by
      simpa [h] using D.canonicalGroundIndex.2
    exact (ne_of_lt i.2.2) hground
  have horth :
      inner ℝ D.canonicalGroundVector (D.eigenbasis i.1) = 0 := by
    simp [canonicalGroundVector, hne]
  have hbound := hRayleigh (D.eigenbasis i.1) horth
  rw [D.operator_apply_eigenbasis i.1] at hbound
  simpa using hbound

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
