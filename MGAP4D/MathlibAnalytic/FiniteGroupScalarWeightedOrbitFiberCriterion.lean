import MGAP4D.MathlibAnalytic.FiniteGroupInvariantOrbitFiberKernelCriterion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A global scalar commutes with finite fibre pushforward. -/
theorem finiteFiberPushforwardCoefficient_smul
    {α β : Type}
    [Fintype α]
    [Fintype β]
    (C : β → α)
    (a : ℝ)
    (w : β → ℝ)
    (x : α) :
    finiteFiberPushforwardCoefficient C (fun z => a * w z) x =
      a * finiteFiberPushforwardCoefficient C w x := by
  classical
  unfold finiteFiberPushforwardCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _hz
  by_cases hzx : C z = x
  · simp [hzx]
  · simp [hzx]

/-- A global scalar commutes with finite orbit aggregation. -/
theorem finiteGroupOrbitAggregateCoefficient_smul
    (G α : Type)
    [Group G]
    [Fintype α]
    [MulAction G α]
    (a : ℝ)
    (v : α → ℝ)
    (q : FiniteGroupOrbitQuotient G α) :
    finiteGroupOrbitAggregateCoefficient G α (fun x => a * v x) q =
      a * finiteGroupOrbitAggregateCoefficient G α v q := by
  classical
  unfold finiteGroupOrbitAggregateCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hxq : finiteGroupOrbitClass G α x = q
  · simp [hxq]
  · simp [hxq]

/-- A global scalar commutes with finite orbit-fibre aggregation. -/
theorem finiteGroupOrbitFiberCoefficient_smul
    (G α : Type)
    {β : Type}
    [Group G]
    [Fintype α]
    [Fintype β]
    [MulAction G α]
    (C : β → α)
    (a : ℝ)
    (w : β → ℝ)
    (q : FiniteGroupOrbitQuotient G α) :
    finiteGroupOrbitFiberCoefficient G α C (fun z => a * w z) q =
      a * finiteGroupOrbitFiberCoefficient G α C w q := by
  classical
  unfold finiteGroupOrbitFiberCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _hz
  by_cases hzq : finiteGroupOrbitClass G α (C z) = q
  · simp [hzq]
  · simp [hzq]

/-- Equality of independently scalar-rescaled fine/coarse invariant finite
functionals is exactly equality of the correspondingly rescaled orbit-fibre
coefficients.  No equality between the two scalars is assumed. -/
theorem finiteGroupInvariant_scaledCrossSum_eq_iff_scaledOrbitFiberSums
    (G α : Type)
    {β : Type}
    [Group G]
    [Fintype α]
    [Fintype β]
    [MulAction G α]
    (C : β → α)
    (af ac : ℝ)
    (w : β → ℝ)
    (v : α → ℝ) :
    (∀ f : finiteGroupInvariantSubmodule G α,
      af * (∑ z : β, w z * f.1 (C z)) =
        ac * (∑ x : α, v x * f.1 x)) ↔
      ∀ q : FiniteGroupOrbitQuotient G α,
        af * finiteGroupOrbitFiberCoefficient G α C w q =
          ac * finiteGroupOrbitAggregateCoefficient G α v q := by
  have hGeneric :=
    finiteGroupInvariant_crossSum_eq_iff_orbitFiberSums
      G α C (fun z => af * w z) (fun x => ac * v x)
  constructor
  · intro h
    have hScaled :
        ∀ f : finiteGroupInvariantSubmodule G α,
          (∑ z : β, (af * w z) * f.1 (C z)) =
            ∑ x : α, (ac * v x) * f.1 x := by
      intro f
      calc
        (∑ z : β, (af * w z) * f.1 (C z)) =
            af * (∑ z : β, w z * f.1 (C z)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z _hz
          ring
        _ = ac * (∑ x : α, v x * f.1 x) := h f
        _ = ∑ x : α, (ac * v x) * f.1 x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _hx
          ring
    have hOrbit := hGeneric.mp hScaled
    intro q
    rw [finiteGroupOrbitFiberCoefficient_smul,
      finiteGroupOrbitAggregateCoefficient_smul] at hOrbit
    exact hOrbit q
  · intro h
    have hScaledOrbit :
        ∀ q : FiniteGroupOrbitQuotient G α,
          finiteGroupOrbitFiberCoefficient G α C (fun z => af * w z) q =
            finiteGroupOrbitAggregateCoefficient G α (fun x => ac * v x) q := by
      intro q
      rw [finiteGroupOrbitFiberCoefficient_smul,
        finiteGroupOrbitAggregateCoefficient_smul]
      exact h q
    have hFunctional := hGeneric.mpr hScaledOrbit
    intro f
    have hf := hFunctional f
    calc
      af * (∑ z : β, w z * f.1 (C z)) =
          ∑ z : β, (af * w z) * f.1 (C z) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _hz
        ring
      _ = ∑ x : α, (ac * v x) * f.1 x := hf
      _ = ac * (∑ x : α, v x * f.1 x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _hx
        ring

end

end MathlibAnalytic
end MGAP4D
