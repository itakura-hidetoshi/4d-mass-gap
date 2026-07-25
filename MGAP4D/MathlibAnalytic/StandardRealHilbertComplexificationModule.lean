import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

/-- The algebraic standard complexification of a real vector space.  A dedicated wrapper avoids
installing a complex scalar action directly on the product type `H × H`. -/
def StandardRealHilbertComplexification (H : Type*) := H × H

namespace StandardRealHilbertComplexification

variable {H : Type*}

instance [Zero H] : Zero (StandardRealHilbertComplexification H) :=
  inferInstanceAs (Zero (H × H))

instance [Add H] : Add (StandardRealHilbertComplexification H) :=
  inferInstanceAs (Add (H × H))

instance [Neg H] : Neg (StandardRealHilbertComplexification H) :=
  inferInstanceAs (Neg (H × H))

instance [Sub H] : Sub (StandardRealHilbertComplexification H) :=
  inferInstanceAs (Sub (H × H))

instance [AddCommGroup H] : AddCommGroup (StandardRealHilbertComplexification H) :=
  inferInstanceAs (AddCommGroup (H × H))

instance [AddCommGroup H] [Module ℝ H] : SMul ℝ (StandardRealHilbertComplexification H) :=
  inferInstanceAs (SMul ℝ (H × H))

instance [AddCommGroup H] [Module ℝ H] : Module ℝ (StandardRealHilbertComplexification H) :=
  inferInstanceAs (Module ℝ (H × H))

/-- Real coordinates of the standard complexification. -/
def coordinates (H : Type*) : StandardRealHilbertComplexification H ≃ H × H :=
  Equiv.refl _

@[simp]
theorem coordinates_apply (z : StandardRealHilbertComplexification H) :
    coordinates H z = z :=
  rfl

@[simp]
theorem coordinates_symm_apply (z : H × H) :
    (coordinates H).symm z = z :=
  rfl

/-- Complex scalar multiplication in real coordinates:
`(a + ib) • (x,y) = (a • x - b • y, b • x + a • y)`. -/
def complexSMul [AddCommGroup H] [Module ℝ H]
    (c : ℂ) (z : StandardRealHilbertComplexification H) :
    StandardRealHilbertComplexification H :=
  (c.re • z.1 - c.im • z.2, c.im • z.1 + c.re • z.2)

instance [AddCommGroup H] [Module ℝ H] : SMul ℂ (StandardRealHilbertComplexification H) :=
  ⟨complexSMul⟩

@[simp]
theorem complex_smul_re [AddCommGroup H] [Module ℝ H]
    (c : ℂ) (z : StandardRealHilbertComplexification H) :
    (c • z).1 = c.re • z.1 - c.im • z.2 :=
  rfl

@[simp]
theorem complex_smul_im [AddCommGroup H] [Module ℝ H]
    (c : ℂ) (z : StandardRealHilbertComplexification H) :
    (c • z).2 = c.im • z.1 + c.re • z.2 :=
  rfl

instance [AddCommGroup H] [Module ℝ H] : Module ℂ (StandardRealHilbertComplexification H) where
  one_smul z := by
    apply Prod.ext <;> simp
  mul_smul c d z := by
    apply Prod.ext <;>
      simp only [complex_smul_re, complex_smul_im, Complex.mul_re, Complex.mul_im,
        smul_sub, smul_add, sub_smul, add_smul, mul_smul]
    all_goals module
  smul_add c z w := by
    apply Prod.ext <;> simp [smul_add]
  add_smul c d z := by
    apply Prod.ext <;> simp [add_smul, sub_eq_add_neg]
  zero_smul z := by
    apply Prod.ext <;> simp
  smul_zero c := by
    apply Prod.ext <;> simp

@[simp]
theorem I_smul [AddCommGroup H] [Module ℝ H]
    (z : StandardRealHilbertComplexification H) :
    Complex.I • z = (-z.2, z.1) := by
  apply Prod.ext <;> simp

/-- The canonical embedding of the real vector space. -/
def ofReal [Zero H] (x : H) : StandardRealHilbertComplexification H :=
  (x, 0)

@[simp]
theorem ofReal_re [Zero H] (x : H) : (ofReal x).1 = x :=
  rfl

@[simp]
theorem ofReal_im [Zero H] (x : H) : (ofReal x).2 = 0 :=
  rfl

/-- Standard conjugation. -/
def conjugation [Neg H] (z : StandardRealHilbertComplexification H) :
    StandardRealHilbertComplexification H :=
  (z.1, -z.2)

@[simp]
theorem conjugation_re [Neg H] (z : StandardRealHilbertComplexification H) :
    (conjugation z).1 = z.1 :=
  rfl

@[simp]
theorem conjugation_im [Neg H] (z : StandardRealHilbertComplexification H) :
    (conjugation z).2 = -z.2 :=
  rfl

@[simp]
theorem conjugation_conjugation [AddGroup H]
    (z : StandardRealHilbertComplexification H) :
    conjugation (conjugation z) = z := by
  apply Prod.ext <;> simp [conjugation]

@[simp]
theorem conjugation_ofReal [AddGroup H] (x : H) :
    conjugation (ofReal x) = ofReal x := by
  apply Prod.ext <;> simp [conjugation, ofReal]

/-- Coordinate form of the canonical real/imaginary decomposition. -/
theorem decompose [AddCommGroup H] [Module ℝ H]
    (z : StandardRealHilbertComplexification H) :
    z = ofReal z.1 + Complex.I • ofReal z.2 := by
  apply Prod.ext <;> simp [ofReal]

end StandardRealHilbertComplexification

end MathlibAnalytic
end MGAP4D
