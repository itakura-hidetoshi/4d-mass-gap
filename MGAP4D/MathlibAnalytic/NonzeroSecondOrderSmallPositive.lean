import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set TopologicalSpace

noncomputable section

/-- A second-order Peano expansion at zero, written in the exact non-factorial
second-variation convention used by the ground-lifted lane.

The first two fields record `f(0)=0` and `f'(0)=0`.  The last field is the
actual second-order realization statement:

`f(β) / β² → d₂ / 2`

from the positive side.  Thus `d₂` is the ordinary, non-factorial second
variation.  We keep this asymptotic statement explicit rather than pretending
that the still-open operator-norm / moving-projector differentiability bridge
has already been proved. -/
structure HasSecondOrderExpansionAtZero (f : ℝ → ℝ) (d₂ : ℝ) : Prop where
  value_eq_zero : f 0 = 0
  firstVariation : HasDerivAt f 0 0
  quadraticQuotient :
    Tendsto (fun β : ℝ => f β / β ^ 2)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (d₂ / (2 : ℝ)))

/-- If the positive-side quadratic quotient tends to a nonzero coefficient,
then the function is eventually nonzero on the punctured positive
neighborhood of zero. -/
theorem Tendsto.eventually_ne_zero_right_of_quadraticQuotient_ne_zero
    {f : ℝ → ℝ}
    {q : ℝ}
    (hlim :
      Tendsto (fun β : ℝ => f β / β ^ 2)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds q))
    (hq : q ≠ 0) :
    ∀ᶠ β in nhdsWithin (0 : ℝ) (Ioi 0), f β ≠ 0 := by
  have hnhds : ({0}ᶜ : Set ℝ) ∈ nhds q := by
    exact IsOpen.mem_nhds isOpen_compl_singleton (by simpa using hq)
  have hquot := hlim hnhds
  filter_upwards [hquot] with β hβ
  have hratio : f β / β ^ 2 ≠ 0 := by
    simpa only [mem_compl_iff, mem_singleton_iff] using hβ
  intro hf
  apply hratio
  simp [hf]

/-- Quantitative interval form of the quadratic-quotient criterion. -/
theorem Tendsto.exists_pos_forall_pos_lt_ne_zero_of_quadraticQuotient_ne_zero
    {f : ℝ → ℝ}
    {q : ℝ}
    (hlim :
      Tendsto (fun β : ℝ => f β / β ^ 2)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds q))
    (hq : q ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ β : ℝ, 0 < β → β < ε → f β ≠ 0 := by
  have hEvent :=
    Tendsto.eventually_ne_zero_right_of_quadraticQuotient_ne_zero hlim hq
  change {β : ℝ | f β ≠ 0} ∈ nhdsWithin (0 : ℝ) (Ioi 0) at hEvent
  rcases (mem_nhdsGT_iff_exists_Ioo_subset).1 hEvent with ⟨ε, hε, hsub⟩
  refine ⟨ε, hε, ?_⟩
  intro β hβ hβε
  exact hsub ⟨hβ, hβε⟩

/-- Second-order analogue of Package Q's first-derivative lemma:

`f(0)=0`, `f'(0)=0`, and a realized nonzero second variation force `f` to be
nonzero throughout some sufficiently small positive interval. -/
theorem HasSecondOrderExpansionAtZero.exists_pos_forall_pos_lt_ne_zero_of_secondVariation_ne_zero
    {f : ℝ → ℝ}
    {d₂ : ℝ}
    (h : HasSecondOrderExpansionAtZero f d₂)
    (hd₂ : d₂ ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ β : ℝ, 0 < β → β < ε → f β ≠ 0 := by
  apply Tendsto.exists_pos_forall_pos_lt_ne_zero_of_quadraticQuotient_ne_zero
    h.quadraticQuotient
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  exact div_ne_zero hd₂ htwo

/-- Contrapositive accumulation form: under a realized second-order expansion,
zeros arbitrarily close to zero from the positive side force the second
variation to vanish. -/
theorem HasSecondOrderExpansionAtZero.secondVariation_eq_zero_of_forall_exists_pos_lt_eq_zero
    {f : ℝ → ℝ}
    {d₂ : ℝ}
    (h : HasSecondOrderExpansionAtZero f d₂)
    (haccum : ∀ ε : ℝ, 0 < ε → ∃ β : ℝ, 0 < β ∧ β < ε ∧ f β = 0) :
    d₂ = 0 := by
  by_contra hd₂
  rcases
      h.exists_pos_forall_pos_lt_ne_zero_of_secondVariation_ne_zero hd₂ with
    ⟨ε, hε, hnonzero⟩
  rcases haccum ε hε with ⟨β, hβ, hβε, hβzero⟩
  exact (hnonzero β hβ hβε) hβzero

end

end MathlibAnalytic
end MGAP4D
