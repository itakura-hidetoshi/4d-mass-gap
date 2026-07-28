import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPositiveTimeOS
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Two positive-time cylinder observables admit a common finite future horizon. -/
theorem linearMarkovPositiveTimeCylinder_pair_finiteRepresentable
    (F G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    ∃ n : ℕ,
      ∃ H K : LinearMarkovPositiveTimeFuturePath Ω n → ℝ,
        (F : (ℕ → Ω) → ℝ) =
            H ∘ linearMarkovPositiveTimeFuturePrefix n ∧
          (G : (ℕ → Ω) → ℝ) =
            K ∘ linearMarkovPositiveTimeFuturePrefix n := by
  rcases linearMarkovPositiveTimeCylinder_finiteRepresentable F with
    ⟨n, H, hF⟩
  rcases linearMarkovPositiveTimeCylinder_finiteRepresentable G with
    ⟨m, K, hG⟩
  refine ⟨n + m,
    H ∘ linearMarkovPositiveTimeFutureRestrictLeft n m,
    K ∘ linearMarkovPositiveTimeFutureRestrictRight n m, ?_, ?_⟩
  · rw [hF]
    funext path
    simp [Function.comp_apply]
  · rw [hG]
    funext path
    simp [Function.comp_apply]

/-- Three positive-time cylinder observables admit one common finite future
horizon. -/
theorem linearMarkovPositiveTimeCylinder_triple_finiteRepresentable
    (F G K : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    ∃ n : ℕ,
      ∃ H J Q : LinearMarkovPositiveTimeFuturePath Ω n → ℝ,
        (F : (ℕ → Ω) → ℝ) =
            H ∘ linearMarkovPositiveTimeFuturePrefix n ∧
          (G : (ℕ → Ω) → ℝ) =
            J ∘ linearMarkovPositiveTimeFuturePrefix n ∧
          (K : (ℕ → Ω) → ℝ) =
            Q ∘ linearMarkovPositiveTimeFuturePrefix n := by
  rcases linearMarkovPositiveTimeCylinder_pair_finiteRepresentable F G with
    ⟨n, H, J, hF, hG⟩
  rcases linearMarkovPositiveTimeCylinder_finiteRepresentable K with
    ⟨m, Q, hK⟩
  refine ⟨n + m,
    H ∘ linearMarkovPositiveTimeFutureRestrictLeft n m,
    J ∘ linearMarkovPositiveTimeFutureRestrictLeft n m,
    Q ∘ linearMarkovPositiveTimeFutureRestrictRight n m, ?_, ?_, ?_⟩
  · rw [hF]
    funext path
    simp [Function.comp_apply]
  · rw [hG]
    funext path
    simp [Function.comp_apply]
  · rw [hK]
    funext path
    simp [Function.comp_apply]

/-- The full two-sided integer-path Osterwalder--Schrader bilinear form on the
generated strictly-positive-time cylinder algebra. -/
def linearMarkovTwoSidedIntegerPathOSForm
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) : ℝ :=
  ∫ path,
    ((F : (ℕ → Ω) → ℝ)
      (linearMarkovIntegerPathNonnegativeRestriction
        (linearMarkovIntegerPathReflection path))) *
    ((G : (ℕ → Ω) → ℝ)
      (linearMarkovIntegerPathNonnegativeRestriction path))
    ∂linearMarkovTwoSidedIntegerPathMeasure initial transition hdb

/-- If both cylinder observables are represented on one common finite future,
the full path-space OS form is exactly the existing finite temporal OS form. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_eq_finite_of_commonRepresentation
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω))
    (n : ℕ)
    (H K : LinearMarkovPositiveTimeFuturePath Ω n → ℝ)
    (hF : (F : (ℕ → Ω) → ℝ) =
      H ∘ linearMarkovPositiveTimeFuturePrefix n)
    (hG : (G : (ℕ → Ω) → ℝ) =
      K ∘ linearMarkovPositiveTimeFuturePrefix n) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G =
      linearMarkovPositiveTimeOSForm initial transition n H K := by
  unfold linearMarkovTwoSidedIntegerPathOSForm
  rw [hF, hG]
  simp only [Function.comp_apply]
  exact
    linearMarkovTwoSidedIntegerPathMeasure_finite_reflectedProduct_integral_eq_OSForm
      initial transition hdb n H K

/-- Every full path-space OS pairing is represented by one finite temporal OS
Gram form. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_eq_finite
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    ∃ n : ℕ,
      ∃ H K : LinearMarkovPositiveTimeFuturePath Ω n → ℝ,
        linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G =
          linearMarkovPositiveTimeOSForm initial transition n H K := by
  rcases linearMarkovPositiveTimeCylinder_pair_finiteRepresentable F G with
    ⟨n, H, K, hF, hG⟩
  exact ⟨n, H, K,
    linearMarkovTwoSidedIntegerPathOSForm_eq_finite_of_commonRepresentation
      initial transition hdb F G n H K hF hG⟩

/-- Additivity of the finite temporal OS form in its reflected slot. -/
theorem linearMarkovPositiveTimeOSForm_add_left
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (n : ℕ)
    (F G K : LinearMarkovPositiveTimeFuturePath Ω n → ℝ) :
    linearMarkovPositiveTimeOSForm initial transition n (F + G) K =
      linearMarkovPositiveTimeOSForm initial transition n F K +
        linearMarkovPositiveTimeOSForm initial transition n G K := by
  classical
  unfold linearMarkovPositiveTimeOSForm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro left _hleft
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro right _hright
  ring

/-- Real scalar linearity of the finite temporal OS form in its reflected
slot. -/
theorem linearMarkovPositiveTimeOSForm_smul_left
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (n : ℕ) (c : ℝ)
    (F G : LinearMarkovPositiveTimeFuturePath Ω n → ℝ) :
    linearMarkovPositiveTimeOSForm initial transition n (c • F) G =
      c * linearMarkovPositiveTimeOSForm initial transition n F G := by
  classical
  unfold linearMarkovPositiveTimeOSForm
  change
    (∑ left, ∑ right,
      (c * F left) *
        linearMarkovPositiveTimeOSKernel initial transition n left right *
        G right) =
      c * (∑ left, ∑ right,
        F left *
          linearMarkovPositiveTimeOSKernel initial transition n left right *
          G right)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro left _hleft
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _hright
  ring

/-- Symmetry of the full path-space OS bilinear form, obtained through the common
finite Gram representation. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_symmetric
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G =
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb G F := by
  rcases linearMarkovPositiveTimeCylinder_pair_finiteRepresentable F G with
    ⟨n, H, K, hF, hG⟩
  calc
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G =
        linearMarkovPositiveTimeOSForm initial transition n H K :=
      linearMarkovTwoSidedIntegerPathOSForm_eq_finite_of_commonRepresentation
        initial transition hdb F G n H K hF hG
    _ = linearMarkovPositiveTimeOSForm initial transition n K H :=
      linearMarkovPositiveTimeOSForm_symmetric initial transition n H K
    _ = linearMarkovTwoSidedIntegerPathOSForm initial transition hdb G F := by
      symm
      exact
        linearMarkovTwoSidedIntegerPathOSForm_eq_finite_of_commonRepresentation
          initial transition hdb G F n K H hG hF

/-- Additivity of the full path-space OS form in its reflected slot. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_add_left
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F G K : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb (F + G) K =
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F K +
        linearMarkovTwoSidedIntegerPathOSForm initial transition hdb G K := by
  rcases linearMarkovPositiveTimeCylinder_triple_finiteRepresentable F G K with
    ⟨n, H, J, Q, hF, hG, hK⟩
  have hFG :
      (((F + G :
        linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
          (ℕ → Ω) → ℝ)) =
        (H + J) ∘ linearMarkovPositiveTimeFuturePrefix n := by
    funext path
    change
      (F : (ℕ → Ω) → ℝ) path + (G : (ℕ → Ω) → ℝ) path =
        H (linearMarkovPositiveTimeFuturePrefix n path) +
          J (linearMarkovPositiveTimeFuturePrefix n path)
    rw [congrFun hF path, congrFun hG path]
    rfl
  calc
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb (F + G) K =
        linearMarkovPositiveTimeOSForm initial transition n (H + J) Q :=
      linearMarkovTwoSidedIntegerPathOSForm_eq_finite_of_commonRepresentation
        initial transition hdb (F + G) K n (H + J) Q hFG hK
    _ = linearMarkovPositiveTimeOSForm initial transition n H Q +
        linearMarkovPositiveTimeOSForm initial transition n J Q :=
      linearMarkovPositiveTimeOSForm_add_left initial transition n H J Q
    _ = linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F K +
        linearMarkovTwoSidedIntegerPathOSForm initial transition hdb G K := by
      rw [←
        linearMarkovTwoSidedIntegerPathOSForm_eq_finite_of_commonRepresentation
          initial transition hdb F K n H Q hF hK]
      rw [←
        linearMarkovTwoSidedIntegerPathOSForm_eq_finite_of_commonRepresentation
          initial transition hdb G K n J Q hG hK]

/-- Additivity of the full path-space OS form in its unreflected slot. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_add_right
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F G K : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F (G + K) =
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G +
        linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F K := by
  calc
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F (G + K) =
        linearMarkovTwoSidedIntegerPathOSForm initial transition hdb (G + K) F :=
      linearMarkovTwoSidedIntegerPathOSForm_symmetric
        initial transition hdb F (G + K)
    _ = linearMarkovTwoSidedIntegerPathOSForm initial transition hdb G F +
        linearMarkovTwoSidedIntegerPathOSForm initial transition hdb K F :=
      linearMarkovTwoSidedIntegerPathOSForm_add_left
        initial transition hdb G K F
    _ = linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G +
        linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F K := by
      rw [linearMarkovTwoSidedIntegerPathOSForm_symmetric
        initial transition hdb G F]
      rw [linearMarkovTwoSidedIntegerPathOSForm_symmetric
        initial transition hdb K F]

/-- Real scalar linearity of the full path-space OS form in its reflected slot. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_smul_left
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (c : ℝ)
    (F G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb (c • F) G =
      c * linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G := by
  rcases linearMarkovPositiveTimeCylinder_pair_finiteRepresentable F G with
    ⟨n, H, K, hF, hG⟩
  have hcF :
      (((c • F :
        linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
          (ℕ → Ω) → ℝ)) =
        (c • H) ∘ linearMarkovPositiveTimeFuturePrefix n := by
    funext path
    change
      c * (F : (ℕ → Ω) → ℝ) path =
        c * H (linearMarkovPositiveTimeFuturePrefix n path)
    rw [congrFun hF path]
    rfl
  calc
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb (c • F) G =
        linearMarkovPositiveTimeOSForm initial transition n (c • H) K :=
      linearMarkovTwoSidedIntegerPathOSForm_eq_finite_of_commonRepresentation
        initial transition hdb (c • F) G n (c • H) K hcF hG
    _ = c * linearMarkovPositiveTimeOSForm initial transition n H K :=
      linearMarkovPositiveTimeOSForm_smul_left
        initial transition n c H K
    _ = c * linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G := by
      rw [linearMarkovTwoSidedIntegerPathOSForm_eq_finite_of_commonRepresentation
        initial transition hdb F G n H K hF hG]

/-- Real scalar linearity of the full path-space OS form in its unreflected
slot. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_smul_right
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (c : ℝ)
    (F G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F (c • G) =
      c * linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G := by
  calc
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F (c • G) =
        linearMarkovTwoSidedIntegerPathOSForm initial transition hdb (c • G) F :=
      linearMarkovTwoSidedIntegerPathOSForm_symmetric
        initial transition hdb F (c • G)
    _ = c * linearMarkovTwoSidedIntegerPathOSForm initial transition hdb G F :=
      linearMarkovTwoSidedIntegerPathOSForm_smul_left
        initial transition hdb c G F
    _ = c * linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G := by
      rw [linearMarkovTwoSidedIntegerPathOSForm_symmetric
        initial transition hdb G F]

/-- The zero observable is OS-orthogonal in the reflected slot. -/
@[simp] theorem linearMarkovTwoSidedIntegerPathOSForm_zero_left
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb 0 G = 0 := by
  simpa using
    (linearMarkovTwoSidedIntegerPathOSForm_smul_left
      initial transition hdb 0
      (0 : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) G)

/-- The zero observable is OS-orthogonal in the unreflected slot. -/
@[simp] theorem linearMarkovTwoSidedIntegerPathOSForm_zero_right
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F 0 = 0 := by
  rw [linearMarkovTwoSidedIntegerPathOSForm_symmetric
    initial transition hdb F 0]
  exact linearMarkovTwoSidedIntegerPathOSForm_zero_left
    initial transition hdb F

/-- Negation in the reflected slot. -/
@[simp] theorem linearMarkovTwoSidedIntegerPathOSForm_neg_left
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb (-F) G =
      -linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G := by
  simpa using
    (linearMarkovTwoSidedIntegerPathOSForm_smul_left
      initial transition hdb (-1) F G)

/-- Negation in the unreflected slot. -/
@[simp] theorem linearMarkovTwoSidedIntegerPathOSForm_neg_right
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F (-G) =
      -linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G := by
  simpa using
    (linearMarkovTwoSidedIntegerPathOSForm_smul_right
      initial transition hdb (-1) F G)

/-- Subtraction in the reflected slot. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_sub_left
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F G K : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb (F - G) K =
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F K -
        linearMarkovTwoSidedIntegerPathOSForm initial transition hdb G K := by
  rw [sub_eq_add_neg,
    linearMarkovTwoSidedIntegerPathOSForm_add_left,
    linearMarkovTwoSidedIntegerPathOSForm_neg_left]
  rfl

/-- Subtraction in the unreflected slot. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_sub_right
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F G K : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F (G - K) =
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G -
        linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F K := by
  rw [sub_eq_add_neg,
    linearMarkovTwoSidedIntegerPathOSForm_add_right,
    linearMarkovTwoSidedIntegerPathOSForm_neg_right]
  rfl

/-- Diagonal nonnegativity of the full path-space OS form. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_nonneg
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    0 ≤ linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F := by
  unfold linearMarkovTwoSidedIntegerPathOSForm
  exact
    linearMarkovTwoSidedIntegerPathMeasure_positiveTime_reflection_nonneg
      initial transition hdb F

/-- Quadratic expansion needed for the semidefinite Cauchy--Schwarz argument. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_quadratic_sub_smul
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (a b : ℝ)
    (F G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb
        (a • F - b • G) (a • F - b • G) =
      a ^ 2 * linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F -
        2 * a * b *
          linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G +
        b ^ 2 * linearMarkovTwoSidedIntegerPathOSForm initial transition hdb G G := by
  simp only [linearMarkovTwoSidedIntegerPathOSForm_sub_left,
    linearMarkovTwoSidedIntegerPathOSForm_sub_right,
    linearMarkovTwoSidedIntegerPathOSForm_smul_left,
    linearMarkovTwoSidedIntegerPathOSForm_smul_right]
  rw [linearMarkovTwoSidedIntegerPathOSForm_symmetric
    initial transition hdb G F]
  ring

/-- Cauchy--Schwarz inequality for the full path-space positive semidefinite OS
form. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_cauchy_schwarz
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    (linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G) ^ 2 ≤
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F *
        linearMarkovTwoSidedIntegerPathOSForm initial transition hdb G G := by
  let A :=
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F
  let B :=
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G
  let C :=
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb G G
  have hA : 0 ≤ A := by
    dsimp [A]
    exact linearMarkovTwoSidedIntegerPathOSForm_nonneg
      initial transition hdb F
  have hC : 0 ≤ C := by
    dsimp [C]
    exact linearMarkovTwoSidedIntegerPathOSForm_nonneg
      initial transition hdb G
  by_cases hC0 : C = 0
  · have hz :=
      linearMarkovTwoSidedIntegerPathOSForm_nonneg
        initial transition hdb (B • F - (A + 1) • G)
    rw [linearMarkovTwoSidedIntegerPathOSForm_quadratic_sub_smul] at hz
    change
      0 ≤ B ^ 2 * A - 2 * B * (A + 1) * B + (A + 1) ^ 2 * C at hz
    change B ^ 2 ≤ A * C
    rw [hC0] at hz ⊢
    nlinarith [sq_nonneg B]
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have hz :=
      linearMarkovTwoSidedIntegerPathOSForm_nonneg
        initial transition hdb (C • F - B • G)
    rw [linearMarkovTwoSidedIntegerPathOSForm_quadratic_sub_smul] at hz
    change 0 ≤ C ^ 2 * A - 2 * C * B * B + B ^ 2 * C at hz
    change B ^ 2 ≤ A * C
    nlinarith [sq_nonneg B, sq_nonneg C]

/-- A null vector is OS-orthogonal to every positive-time cylinder observable. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_eq_zero_of_left_null
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω))
    (hF : linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F = 0)
    (G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G = 0 := by
  have hcs :=
    linearMarkovTwoSidedIntegerPathOSForm_cauchy_schwarz
      initial transition hdb F G
  rw [hF, zero_mul] at hcs
  nlinarith [sq_nonneg
    (linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G)]

/-- The OS null space of the positive-time cylinder algebra. -/
def linearMarkovTwoSidedIntegerPathOSNull
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition) :
    Submodule ℝ
      (linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) where
  carrier := {F |
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F = 0}
  zero_mem' := by
    exact linearMarkovTwoSidedIntegerPathOSForm_zero_left
      initial transition hdb 0
  add_mem' := by
    intro F G hF hG
    change
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F = 0 at hF
    change
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb G G = 0 at hG
    change
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb
        (F + G) (F + G) = 0
    rw [linearMarkovTwoSidedIntegerPathOSForm_add_left,
      linearMarkovTwoSidedIntegerPathOSForm_add_right,
      linearMarkovTwoSidedIntegerPathOSForm_add_right,
      hF, hG,
      linearMarkovTwoSidedIntegerPathOSForm_eq_zero_of_left_null
        initial transition hdb F hF G,
      linearMarkovTwoSidedIntegerPathOSForm_eq_zero_of_left_null
        initial transition hdb G hG F]
    norm_num
  smul_mem' := by
    intro c F hF
    change
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F = 0 at hF
    change
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb
        (c • F) (c • F) = 0
    rw [linearMarkovTwoSidedIntegerPathOSForm_smul_left,
      linearMarkovTwoSidedIntegerPathOSForm_smul_right, hF]
    ring

@[simp] theorem mem_linearMarkovTwoSidedIntegerPathOSNull_iff
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    F ∈ linearMarkovTwoSidedIntegerPathOSNull initial transition hdb ↔
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F = 0 :=
  Iff.rfl

/-- Membership in the OS null space is equivalent to orthogonality against every
positive-time cylinder observable. -/
theorem mem_linearMarkovTwoSidedIntegerPathOSNull_iff_forall_orthogonal
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    F ∈ linearMarkovTwoSidedIntegerPathOSNull initial transition hdb ↔
      ∀ G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω),
        linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G = 0 := by
  constructor
  · intro hF G
    exact linearMarkovTwoSidedIntegerPathOSForm_eq_zero_of_left_null
      initial transition hdb F hF G
  · intro hF
    exact hF F

end

end MathlibAnalytic
end MGAP4D
