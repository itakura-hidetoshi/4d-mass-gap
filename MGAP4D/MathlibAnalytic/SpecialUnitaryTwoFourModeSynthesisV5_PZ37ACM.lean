import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoFourModeHaarV5_PZ37ACK

/-!
# P4-Q2-PZ37ACM — exact four-coordinate synthesis in the original SU(2)

The four genuine quaternion character coordinates from ACK exhaust the real
unit sphere. An explicit two-by-two matrix has both unitary adjoint and
determinant one whenever its four real coordinates have squared sum one.
The resulting element is in the SAME original special-unitary group.

The unconditional original real character orbit identity also expands every
left-translated Wilson character in those four coordinates. The orientation
is fixed throughout: the coordinate of a translating element `a` is
`fourModeCharacter j (a⁻¹)`.

This algebraic leaf adds no physical receiver, posterior, boundary law,
Perron representative, positivity hypothesis, or alternative Haar measure.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
local notation "χ" => p4Q2PZ35C_originalOneLinkCharacter
local notation "q" => p4Q2PZ35B_quaternionFamily
local notation "φ" => p4Q2PZ37ACK_fourModeCharacter

private theorem p4Q2PZ37ACM_character_conjugate (c x : G) :
    χ (c⁻¹ * x * c) = χ x := by
  unfold p4Q2PZ35C_originalOneLinkCharacter
  rw [p4Q2PZ35D5_originalEnergy_conjugate]

/-- Every genuine left translate of the original Wilson character has this
exact four-mode expansion, with the translating coordinate evaluated at a⁻¹. -/
theorem p4Q2PZ37ACM_fourModeCharacter_translate (a g : G) :
    χ (a * g) = ∑ j : Fin 4, φ j (a⁻¹) * φ j g := by
  have hTerm (j : Fin 4) :
      χ ((q j * g)⁻¹ * (a * g)) = φ j (a⁻¹) := by
    have hGroup : (q j * g)⁻¹ * (a * g) =
        g⁻¹ * ((q j)⁻¹ * a) * g := by group
    rw [hGroup, p4Q2PZ37ACM_character_conjugate]
    change χ ((q j)⁻¹ * a) = χ (q j * a⁻¹)
    calc
      χ ((q j)⁻¹ * a) = χ (((q j)⁻¹ * a)⁻¹) :=
        (p4Q2PZ35D5_originalCharacter_inv ((q j)⁻¹ * a)).symm
      _ = χ (a⁻¹ * q j) := by rw [mul_inv_rev, inv_inv]
      _ = χ (q j * a⁻¹) := p4Q2PZ35D5_originalCharacter_mul_comm a⁻¹ (q j)
  calc
    χ (a * g) =
        ∑ j : Fin 4, χ (q j * g) * χ ((q j * g)⁻¹ * (a * g)) :=
      (p4Q2PZ35D4_originalRealCharacterOrbit (a * g) g).symm
    _ = ∑ j : Fin 4, φ j (a⁻¹) * φ j g := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hTerm]
      exact mul_comm (φ j g) (φ j (a⁻¹))

/-! The matrix below represents x₀ I − x₁ J − x₂ K − x₃ L. Its inverse
is the translating SU(2) element whose inverse-character coordinates are x. -/

private def p4Q2PZ37ACM_synthesisMatrix (x : Fin 4 → ℝ) : Mat :=
  !![(x 0 : ℂ) - (x 2 : ℂ) * Complex.I,
      (x 1 : ℂ) - (x 3 : ℂ) * Complex.I;
    -(x 1 : ℂ) - (x 3 : ℂ) * Complex.I,
      (x 0 : ℂ) + (x 2 : ℂ) * Complex.I]

private theorem p4Q2PZ37ACM_synthesisMatrix_mem
    (x : Fin 4 → ℝ) (hx : (∑ j : Fin 4, (x j) ^ 2) = 1) :
    p4Q2PZ37ACM_synthesisMatrix x ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hx4 : (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2 = 1 := by
    simpa [Fin.sum_univ_four, add_assoc] using hx
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    change p4Q2PZ37ACM_synthesisMatrix x *
      (p4Q2PZ37ACM_synthesisMatrix x).conjTranspose = (1 : Mat)
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      simp [p4Q2PZ37ACM_synthesisMatrix, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_two,
        Complex.mul_re, Complex.mul_im] <;>
      nlinarith [hx4]
  · apply Complex.ext <;>
      simp [p4Q2PZ37ACM_synthesisMatrix, Matrix.det_fin_two,
        Complex.mul_re, Complex.mul_im] <;>
      nlinarith [hx4]

/-- Every real unit four-vector is realized by an ACTUAL original SU(2)
translating element, in precisely the orientation used by character transport. -/
theorem p4Q2PZ37ACM_exists_fourModeCharacter_coordinates
    (x : Fin 4 → ℝ) (hx : (∑ j : Fin 4, (x j) ^ 2) = 1) :
    ∃ a : G, ∀ j : Fin 4, φ j (a⁻¹) = x j := by
  let u : G := ⟨p4Q2PZ37ACM_synthesisMatrix x,
    p4Q2PZ37ACM_synthesisMatrix_mem x hx⟩
  refine ⟨u⁻¹, ?_⟩
  intro j
  rw [inv_inv]
  change χ (q j * u) = x j
  have hComplex : ((χ (q j * u) : ℝ) : ℂ) = (x j : ℂ) := by
    rw [p4Q2PZ35D2_originalCharacter_complex_coe]
    change Matrix.trace (((q j : G) : Mat) * p4Q2PZ37ACM_synthesisMatrix x) / 2 =
      (x j : ℂ)
    rw [p4Q2PZ35B_quaternionFamily_coe]
    fin_cases j <;>
      apply Complex.ext <;>
      norm_num [p4Q2PZ37ACM_synthesisMatrix,
        p4Q2PZ35A_pauliQ0, p4Q2PZ35A_pauliQ1,
        p4Q2PZ35A_pauliQ2, p4Q2PZ35A_pauliQ3,
        Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
        Complex.mul_re, Complex.mul_im] <;>
      ring_nf <;> rfl
  exact_mod_cast hComplex

end

end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ACM_fourModeCharacter_translate
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ACM_exists_fourModeCharacter_coordinates
