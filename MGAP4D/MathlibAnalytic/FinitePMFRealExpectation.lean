import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Real expectation of an observable under a probability mass function on a
finite type. -/
def finitePMFExpectationReal
    {α : Type*} [Fintype α]
    (p : PMF α) (f : α → ℝ) : ℝ :=
  ∑ a : α, (p a).toReal * f a

/-- Real expectation commutes with pushing a finite PMF forward along a map. -/
theorem finite_pmfExpectationReal_map
    {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (φ : α → β) (f : β → ℝ) :
    finitePMFExpectationReal (p.map φ) f =
      finitePMFExpectationReal p (fun a => f (φ a)) := by
  classical
  unfold finitePMFExpectationReal
  simp_rw [PMF.map_apply, tsum_fintype]
  calc
    ∑ b : β,
        (∑ a : α, if b = φ a then p a else 0).toReal * f b =
      ∑ b : β,
        (∑ a : α, if b = φ a then (p a).toReal else 0) * f b := by
        apply Finset.sum_congr rfl
        intro b _hb
        rw [ENNReal.toReal_sum]
        · apply congrArg (fun r : ℝ => r * f b)
          apply Finset.sum_congr rfl
          intro a _ha
          split_ifs <;> simp
        · intro a _ha
          split_ifs
          · exact p.apply_ne_top a
          · simp
    _ = ∑ a : α, (p a).toReal * f (φ a) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp

/-- Real expectation under a finite PMF bind is the iterated real
expectation. -/
theorem finite_pmfExpectationReal_bind
    {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    finitePMFExpectationReal (p.bind q) f =
      finitePMFExpectationReal p
        (fun a => finitePMFExpectationReal (q a) f) := by
  classical
  unfold finitePMFExpectationReal
  simp_rw [PMF.bind_apply, tsum_fintype]
  calc
    ∑ b : β, (∑ a : α, p a * q a b).toReal * f b =
      ∑ b : β,
        (∑ a : α, (p a).toReal * (q a b).toReal) * f b := by
        apply Finset.sum_congr rfl
        intro b _hb
        rw [ENNReal.toReal_sum]
        · apply congrArg (fun r : ℝ => r * f b)
          apply Finset.sum_congr rfl
          intro a _ha
          rw [ENNReal.toReal_mul]
        · intro a _ha
          exact ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b)
    _ = ∑ a : α,
        (p a).toReal * ∑ b : β, (q a b).toReal * f b := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _hb
      ring

end

end MathlibAnalytic
end MGAP4D
