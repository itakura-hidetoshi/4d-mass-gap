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

/-- A finite ambient group gives the kernel of any group homomorphism a
noncomputable finite enumeration without exposing a decidable membership
predicate in theorem statements. -/
noncomputable instance finiteGroupHomKerFintype
    {G H : Type}
    [Group G]
    [Group H]
    [Fintype G]
    (φ : G →* H) : Fintype φ.ker :=
  Fintype.ofFinite _

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
    change
      (x * (finiteSurjectiveGroupHomSection φ hφ (φ x))⁻¹) *
          finiteSurjectiveGroupHomSection φ hφ (φ x) = x
    simp [mul_assoc]
  right_inv ky := by
    rcases ky with ⟨k, y⟩
    have hk : φ k.1 = 1 := k.2
    have hmap :
        φ (k.1 * finiteSurjectiveGroupHomSection φ hφ y) = y := by
      rw [map_mul, hk, finiteSurjectiveGroupHomSection_map]
      simp
    apply Prod.ext
    · apply Subtype.ext
      change
        (k.1 * finiteSurjectiveGroupHomSection φ hφ y) *
            (finiteSurjectiveGroupHomSection φ hφ
              (φ (k.1 * finiteSurjectiveGroupHomSection φ hφ y)))⁻¹ =
          k.1
      rw [hmap]
      simp [mul_assoc]
    · exact hmap

/-- The second component of the product decomposition is exactly the image
under the original homomorphism. -/
@[simp] theorem finiteSurjectiveGroupHomEquivKerProd_snd
    {G H : Type}
    [Group G]
    [Group H]
    (φ : G →* H)
    (hφ : Function.Surjective φ)
    (x : G) :
    (finiteSurjectiveGroupHomEquivKerProd φ hφ x).2 = φ x :=
  rfl

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
  change
    (∑ x : G,
      if φ x = y then (Fintype.card G : ℝ)⁻¹ else 0) =
      (Fintype.card H : ℝ)⁻¹
  let E := finiteSurjectiveGroupHomEquivKerProd φ hφ
  calc
    (∑ x : G,
      if φ x = y then (Fintype.card G : ℝ)⁻¹ else 0) =
      ∑ ky : φ.ker × H,
        if ky.2 = y then (Fintype.card G : ℝ)⁻¹ else 0 := by
      exact Fintype.sum_equiv E _ _ (fun x => by rfl)
    _ = ∑ k : φ.ker, ∑ z : H,
        if z = y then (Fintype.card G : ℝ)⁻¹ else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ _k : φ.ker, (Fintype.card G : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k _hk
      simp
    _ = (Fintype.card φ.ker : ℝ) * (Fintype.card G : ℝ)⁻¹ := by
      simp
    _ = (Fintype.card H : ℝ)⁻¹ := by
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
      field_simp [hker, hH]

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
