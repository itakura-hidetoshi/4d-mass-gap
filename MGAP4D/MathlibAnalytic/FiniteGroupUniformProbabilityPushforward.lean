import MGAP4D.MathlibAnalytic.FiniteStrictProbabilityL2MeasurePreservingPullback
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A chosen preimage of each target point of a surjective group homomorphism. -/
noncomputable def finiteSurjectiveGroupHomSection
    {G H : Type}
    [Group G]
    [Group H]
    (φ : G →* H)
    (hφ : Function.Surjective φ)
    (y : H) : G :=
  Classical.choose (hφ y)

@[simp] theorem finiteSurjectiveGroupHomSection_map
    {G H : Type}
    [Group G]
    [Group H]
    (φ : G →* H)
    (hφ : Function.Surjective φ)
    (y : H) :
    φ (finiteSurjectiveGroupHomSection φ hφ y) = y :=
  Classical.choose_spec (hφ y)

/-- Fibre of a group homomorphism over one target element. -/
abbrev FiniteGroupHomFiber
    {G H : Type}
    [Group G]
    [Group H]
    (φ : G →* H)
    (y : H) : Type :=
  {x : G // φ x = y}

/-- Every fibre of a surjective group homomorphism is canonically equivalent,
once a section point is chosen, to the kernel. -/
noncomputable def finiteSurjectiveGroupHomFiberEquivKer
    {G H : Type}
    [Group G]
    [Group H]
    (φ : G →* H)
    (hφ : Function.Surjective φ)
    (y : H) :
    FiniteGroupHomFiber φ y ≃ φ.ker where
  toFun x :=
    ⟨x.1 * (finiteSurjectiveGroupHomSection φ hφ y)⁻¹, by
      change φ (x.1 * (finiteSurjectiveGroupHomSection φ hφ y)⁻¹) = 1
      rw [map_mul, map_inv, x.2,
        finiteSurjectiveGroupHomSection_map]
      simp⟩
  invFun k :=
    ⟨k.1 * finiteSurjectiveGroupHomSection φ hφ y, by
      change φ (k.1 * finiteSurjectiveGroupHomSection φ hφ y) = y
      rw [map_mul, k.2, finiteSurjectiveGroupHomSection_map]
      simp⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv k := by
    apply Subtype.ext
    simp [mul_assoc]

/-- A surjective finite group homomorphism has the usual set-level product
decomposition into its kernel and target.  No homomorphic section is claimed. -/
noncomputable def finiteSurjectiveGroupHomEquivKerProd
    {G H : Type}
    [Group G]
    [Group H]
    (φ : G →* H)
    (hφ : Function.Surjective φ) :
    G ≃ φ.ker × H where
  toFun x :=
    (⟨x * (finiteSurjectiveGroupHomSection φ hφ (φ x))⁻¹, by
        change φ (x * (finiteSurjectiveGroupHomSection φ hφ (φ x))⁻¹) = 1
        rw [map_mul, map_inv, finiteSurjectiveGroupHomSection_map]
        simp⟩,
      φ x)
  invFun ky :=
    ky.1.1 * finiteSurjectiveGroupHomSection φ hφ ky.2
  left_inv x := by
    simp [mul_assoc]
  right_inv ky := by
    rcases ky with ⟨k, y⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [mul_assoc]
    · simp

/-- Cardinality decomposition for a surjective homomorphism of finite groups. -/
theorem finiteSurjectiveGroupHom_card_eq_card_ker_mul_card
    {G H : Type}
    [Group G]
    [Group H]
    [Fintype G]
    [Fintype H]
    (φ : G →* H)
    (hφ : Function.Surjective φ) :
    Fintype.card G = Fintype.card φ.ker * Fintype.card H := by
  rw [← Fintype.card_prod]
  exact Fintype.card_congr (finiteSurjectiveGroupHomEquivKerProd φ hφ)

/-- Every fibre of a surjective homomorphism of finite groups has exactly the
kernel cardinality. -/
theorem finiteSurjectiveGroupHom_fiber_card
    {G H : Type}
    [Group G]
    [Group H]
    [Fintype G]
    [Fintype H]
    (φ : G →* H)
    (hφ : Function.Surjective φ)
    (y : H) :
    Fintype.card (FiniteGroupHomFiber φ y) = Fintype.card φ.ker :=
  Fintype.card_congr (finiteSurjectiveGroupHomFiberEquivKer φ hφ y)

/-- Uniform probability on a finite group is pushed forward exactly to uniform
probability by every surjective group homomorphism. -/
theorem finiteSurjectiveGroupHom_uniform_pushforward_weight
    {G H : Type}
    [Group G]
    [Group H]
    [Fintype G]
    [Fintype H]
    (φ : G →* H)
    (hφ : Function.Surjective φ)
    (y : H) :
    finiteProbabilityPushforwardWeight
        (finiteUniformProbabilityL2Data G) φ y =
      (finiteUniformProbabilityL2Data H).weight y := by
  classical
  unfold finiteProbabilityPushforwardWeight
  rw [← Fintype.sum_subtype]
  change
    (∑ _x : FiniteGroupHomFiber φ y,
        (Fintype.card G : ℝ)⁻¹) =
      (Fintype.card H : ℝ)⁻¹
  rw [Fintype.sum_const]
  simp only [nsmul_eq_mul]
  rw [finiteSurjectiveGroupHom_fiber_card φ hφ y]
  have hcard := finiteSurjectiveGroupHom_card_eq_card_ker_mul_card φ hφ
  have hker : (Fintype.card φ.ker : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hH : (Fintype.card H : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcardR :
      (Fintype.card G : ℝ) =
        (Fintype.card φ.ker : ℝ) * (Fintype.card H : ℝ) := by
    exact_mod_cast hcard
  rw [hcardR]
  field_simp

/-- Bundled exact finite probability map induced by a surjective homomorphism
between finite groups equipped with their uniform laws. -/
noncomputable def finiteSurjectiveGroupHomUniformProbabilityMap
    {G H : Type}
    [Group G]
    [Group H]
    [Fintype G]
    [Fintype H]
    (φ : G →* H)
    (hφ : Function.Surjective φ) :
    FiniteStrictProbabilityMap G H
      (finiteUniformProbabilityL2Data G)
      (finiteUniformProbabilityL2Data H) where
  toFun := φ
  weight_pushforward :=
    finiteSurjectiveGroupHom_uniform_pushforward_weight φ hφ

/-- The uniform finite-group probability pullback is therefore a canonical
real-linear `L²` isometry. -/
noncomputable def finiteSurjectiveGroupHomUniformL2PullbackLinearIsometry
    {G H : Type}
    [Group G]
    [Group H]
    [Fintype G]
    [Fintype H]
    (φ : G →* H)
    (hφ : Function.Surjective φ) :
    FiniteProbabilityL2Carrier H →ₗᵢ[ℝ]
      FiniteProbabilityL2Carrier G :=
  (finiteSurjectiveGroupHomUniformProbabilityMap φ hφ).l2PullbackLinearIsometry

end

end MathlibAnalytic
end MGAP4D
