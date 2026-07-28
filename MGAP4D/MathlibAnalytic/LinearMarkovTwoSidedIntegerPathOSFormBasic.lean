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
  simp only [Pi.add_apply]
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
  unfold linearMarkovTwoSidedIntegerPathOSForm
  simp

/-- The zero observable is OS-orthogonal in the unreflected slot. -/
@[simp] theorem linearMarkovTwoSidedIntegerPathOSForm_zero_right
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F 0 = 0 := by
  unfold linearMarkovTwoSidedIntegerPathOSForm
  simp

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

end

end MathlibAnalytic
end MGAP4D
