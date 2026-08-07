import MGAP4D.MathlibAnalytic.FiniteGroupEquivariantFiberPushforwardOrbitEvaluation
import MGAP4D.MathlibAnalytic.FiniteSurjectiveGroupHomFiberMultiplicity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Multiplicity-normalized fibre pushforward through a surjective finite group
homomorphism.  Unlike the raw fibre sum, this divides by the exact cardinality
of the kernel and is therefore an honest uniform fibre average. -/
noncomputable def finiteSurjectiveGroupHomFiberAverage
    {G H : Type}
    [Group G]
    [Group H]
    [Fintype G]
    [Fintype H]
    (φ : G →* H)
    (w : G → ℝ)
    (y : H) : ℝ :=
  (Fintype.card φ.ker : ℝ)⁻¹ *
    finiteFiberPushforwardCoefficient φ w y

/-- Kernel cardinality is a nonzero real scalar. -/
theorem finiteSurjectiveGroupHom_card_ker_real_ne_zero
    {G H : Type}
    [Group G]
    [Group H]
    [Fintype G]
    (φ : G →* H) :
    (Fintype.card φ.ker : ℝ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

/-- Fibre averaging preserves the constant-one function exactly. -/
theorem finiteSurjectiveGroupHomFiberAverage_one
    {G H : Type}
    [Group G]
    [Group H]
    [Fintype G]
    [Fintype H]
    (φ : G →* H)
    (hφ : Function.Surjective φ)
    (y : H) :
    finiteSurjectiveGroupHomFiberAverage φ (fun _ => (1 : ℝ)) y = 1 := by
  classical
  unfold finiteSurjectiveGroupHomFiberAverage finiteFiberPushforwardCoefficient
  rw [finiteSurjectiveGroupHom_fiber_count φ hφ y]
  field_simp [finiteSurjectiveGroupHom_card_ker_real_ne_zero φ]

/-- Fibre pushforward commutes with multiplication by a constant scalar. -/
theorem finiteFiberPushforwardCoefficient_const_mul
    {α β : Type}
    [Fintype α]
    [Fintype β]
    (C : β → α)
    (c : ℝ)
    (w : β → ℝ)
    (x : α) :
    finiteFiberPushforwardCoefficient C (fun z => c * w z) x =
      c * finiteFiberPushforwardCoefficient C w x := by
  classical
  unfold finiteFiberPushforwardCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _hz
  by_cases hzx : C z = x
  · simp [hzx]
  · simp [hzx]

/-- Kernel cardinalities multiply under composition of surjective finite group
homomorphisms. -/
theorem finiteSurjectiveGroupHom_card_ker_comp
    {G H K : Type}
    [Group G]
    [Group H]
    [Group K]
    [Fintype G]
    [Fintype H]
    [Fintype K]
    (ψ : G →* H)
    (φ : H →* K)
    (hψ : Function.Surjective ψ)
    (hφ : Function.Surjective φ) :
    Fintype.card (φ.comp ψ).ker =
      Fintype.card ψ.ker * Fintype.card φ.ker := by
  have hcomp : Function.Surjective (φ.comp ψ) := hφ.comp hψ
  have hψcard := finiteSurjectiveGroupHom_card_eq_card_ker_mul_card ψ hψ
  have hφcard := finiteSurjectiveGroupHom_card_eq_card_ker_mul_card φ hφ
  have hcompcard :=
    finiteSurjectiveGroupHom_card_eq_card_ker_mul_card (φ.comp ψ) hcomp
  have hEq :
      Fintype.card (φ.comp ψ).ker * Fintype.card K =
        (Fintype.card ψ.ker * Fintype.card φ.ker) * Fintype.card K := by
    calc
      Fintype.card (φ.comp ψ).ker * Fintype.card K =
          Fintype.card G := hcompcard.symm
      _ = Fintype.card ψ.ker * Fintype.card H := hψcard
      _ = Fintype.card ψ.ker *
          (Fintype.card φ.ker * Fintype.card K) := by rw [hφcard]
      _ = (Fintype.card ψ.ker * Fintype.card φ.ker) *
          Fintype.card K := by simp [Nat.mul_assoc]
  exact Nat.mul_right_cancel hEq

/-- Exact tower law for multiplicity-normalized fibre averaging. -/
theorem finiteSurjectiveGroupHomFiberAverage_comp
    {G H K : Type}
    [Group G]
    [Group H]
    [Group K]
    [Fintype G]
    [Fintype H]
    [Fintype K]
    (ψ : G →* H)
    (φ : H →* K)
    (hψ : Function.Surjective ψ)
    (hφ : Function.Surjective φ)
    (w : G → ℝ)
    (z : K) :
    finiteSurjectiveGroupHomFiberAverage (φ.comp ψ) w z =
      finiteSurjectiveGroupHomFiberAverage φ
        (finiteSurjectiveGroupHomFiberAverage ψ w) z := by
  classical
  unfold finiteSurjectiveGroupHomFiberAverage
  rw [finiteSurjectiveGroupHom_card_ker_comp ψ φ hψ hφ]
  rw [finiteFiberPushforwardCoefficient_const_mul]
  rw [finiteFiberPushforwardCoefficient_comp]
  have hψker : (Fintype.card ψ.ker : ℝ) ≠ 0 :=
    finiteSurjectiveGroupHom_card_ker_real_ne_zero ψ
  have hφker : (Fintype.card φ.ker : ℝ) ≠ 0 :=
    finiteSurjectiveGroupHom_card_ker_real_ne_zero φ
  push_cast
  field_simp [hψker, hφker]
  ring

/-- Audit-visible generic multiplicity-normalized fibre-average package. -/
structure FiniteSurjectiveGroupHomFiberAveragePackage
    {G H : Type}
    [Group G]
    [Group H]
    [Fintype G]
    [Fintype H]
    (φ : G →* H)
    (hφ : Function.Surjective φ) where
  average : (G → ℝ) → H → ℝ
  average_eq : average = finiteSurjectiveGroupHomFiberAverage φ
  preservesOne : ∀ y, average (fun _ => 1) y = 1

/-- Construct the generic fibre-average receipt. -/
noncomputable def finiteSurjectiveGroupHomFiberAveragePackage
    {G H : Type}
    [Group G]
    [Group H]
    [Fintype G]
    [Fintype H]
    (φ : G →* H)
    (hφ : Function.Surjective φ) :
    FiniteSurjectiveGroupHomFiberAveragePackage φ hφ where
  average := finiteSurjectiveGroupHomFiberAverage φ
  average_eq := rfl
  preservesOne := finiteSurjectiveGroupHomFiberAverage_one φ hφ

end

end MathlibAnalytic
end MGAP4D
