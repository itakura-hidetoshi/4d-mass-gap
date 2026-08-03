import MGAP4D.MathlibAnalytic.FiniteDimensionalExcitationGap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- Ground synthesis consists of exact fixed vectors of the original
operator. -/
theorem operator_groundSpectralSynthesis
    (x : D.GroundSpectralSpace) :
    D.operator (D.groundSpectralSynthesis x) =
      D.groundSpectralSynthesis x := by
  apply D.eigenbasis.repr.injective
  ext j
  have hdiag :
      D.eigenbasis.repr
          (D.operator (D.groundSpectralSynthesis x)) j =
        D.eigenvalue j *
          D.eigenbasis.repr (D.groundSpectralSynthesis x) j := by
    simpa [eigenbasis, eigenvalue] using
      D.symmetric.eigenvectorBasis_apply_self_apply
        (by rfl) (D.groundSpectralSynthesis x) j
  rw [hdiag]
  by_cases hg : D.eigenvalue j = 1
  · simp [groundSpectralSynthesis, groundSpectralExtension, hg]
  · simp [groundSpectralSynthesis, groundSpectralExtension, hg]

/-- Null synthesis is annihilated in one transfer step. -/
theorem operator_nullSpectralSynthesis
    (x : D.NullSpectralSpace) :
    D.operator (D.nullSpectralSynthesis x) = 0 := by
  apply D.eigenbasis.repr.injective
  ext j
  have hdiag :
      D.eigenbasis.repr
          (D.operator (D.nullSpectralSynthesis x)) j =
        D.eigenvalue j *
          D.eigenbasis.repr (D.nullSpectralSynthesis x) j := by
    simpa [eigenbasis, eigenvalue] using
      D.symmetric.eigenvectorBasis_apply_self_apply
        (by rfl) (D.nullSpectralSynthesis x) j
  rw [hdiag]
  by_cases hz : D.eigenvalue j = 0
  · simp [nullSpectralSynthesis, nullSpectralExtension, hz]
  · simp [nullSpectralSynthesis, nullSpectralExtension, hz]

/-- A nonzero ground coordinate synthesizes to a nonzero fixed vector. -/
theorem exists_nonzero_fixedVector_of_nonempty_ground
    [Nonempty D.GroundSpectralIndex] :
    ∃ v : E, v ≠ 0 ∧ D.operator v = v := by
  let i : D.GroundSpectralIndex := Classical.choice inferInstance
  let x : D.GroundSpectralSpace :=
    WithLp.toLp 2 (Pi.single i (1 : ℝ))
  refine ⟨D.groundSpectralSynthesis x, ?_, D.operator_groundSpectralSynthesis x⟩
  intro hx
  have hzero := D.groundSpectralSynthesis_injective hx
  have hi := congrArg (fun z : D.GroundSpectralSpace => z i) hzero
  simpa [x] using hi

/-- If neither excited nor null modes exist, every canonical eigenvalue is one. -/
theorem eigenvalue_eq_one_of_no_excited_no_null
    (hExcited : ¬ Nonempty D.ExcitedSpectralIndex)
    (hNull : ¬ Nonempty D.NullSpectralIndex)
    (i : Fin D.dimension) :
    D.eigenvalue i = 1 := by
  rcases D.eigenvalue_trichotomy i with hz | he | hg
  · exact False.elim (hNull ⟨⟨i, hz⟩⟩)
  · exact False.elim (hExcited ⟨⟨i, he⟩⟩)
  · exact hg

/-- Absence of both excited and null modes forces the operator to be the
identity. -/
theorem operator_eq_one_of_no_excited_no_null
    (hExcited : ¬ Nonempty D.ExcitedSpectralIndex)
    (hNull : ¬ Nonempty D.NullSpectralIndex) :
    D.operator = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply D.eigenbasis.repr.injective
  ext i
  have hdiag :
      D.eigenbasis.repr (D.operator x) i =
        D.eigenvalue i * D.eigenbasis.repr x i := by
    simpa [eigenbasis, eigenvalue] using
      D.symmetric.eigenvectorBasis_apply_self_apply (by rfl) x i
  rw [hdiag, D.eigenvalue_eq_one_of_no_excited_no_null hExcited hNull]
  simp

/-- Every nonidentity positive contraction has a strictly excited mode or a
null mode.  The theorem deliberately does not choose between the two. -/
theorem nonempty_excited_or_null_of_operator_ne_one
    (hne : D.operator ≠ 1) :
    Nonempty D.ExcitedSpectralIndex ∨
      Nonempty D.NullSpectralIndex := by
  by_contra h
  push Not at h
  exact hne (D.operator_eq_one_of_no_excited_no_null h.1 h.2)

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
