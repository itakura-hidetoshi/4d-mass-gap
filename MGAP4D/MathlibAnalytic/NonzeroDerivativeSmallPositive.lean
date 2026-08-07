import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set TopologicalSpace

noncomputable section

/-- A real function which vanishes at zero but has nonzero derivative there is
nonzero eventually on the punctured right neighborhood of zero.  No
continuity of the derivative is assumed. -/
theorem HasDerivAt.eventually_ne_zero_right_of_eq_zero_of_ne_zero
    {f : ℝ → ℝ}
    {d : ℝ}
    (hderiv : HasDerivAt f d 0)
    (hzero : f 0 = 0)
    (hd : d ≠ 0) :
    ∀ᶠ β in nhdsWithin (0 : ℝ) (Ioi 0), f β ≠ 0 := by
  have hnhds : ({0}ᶜ : Set ℝ) ∈ 𝓝 d := by
    exact IsOpen.mem_nhds isOpen_compl_singleton (by simpa using hd)
  have hslope := hderiv.tendsto_slope_zero_right hnhds
  filter_upwards [hslope] with β hβ
  have hslope_ne : β⁻¹ • (f (0 + β) - f 0) ≠ 0 := by
    simpa only [mem_compl_iff, mem_singleton_iff] using hβ
  intro hfβ
  apply hslope_ne
  simp [hfβ, hzero]

/-- Quantitative interval form of the nonzero-derivative criterion: if
`f(0)=0` and `f'(0)≠0`, then there is an actual positive epsilon such that
`f(β)≠0` for every `0<β<epsilon`. -/
theorem HasDerivAt.exists_pos_forall_pos_lt_ne_zero_of_eq_zero_of_ne_zero
    {f : ℝ → ℝ}
    {d : ℝ}
    (hderiv : HasDerivAt f d 0)
    (hzero : f 0 = 0)
    (hd : d ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ β : ℝ, 0 < β → β < ε → f β ≠ 0 := by
  have hEvent :=
    hderiv.eventually_ne_zero_right_of_eq_zero_of_ne_zero hzero hd
  change {β : ℝ | f β ≠ 0} ∈ nhdsWithin (0 : ℝ) (Ioi 0) at hEvent
  rcases (mem_nhdsGT_iff_exists_Ioo_subset).1 hEvent with ⟨ε, hε, hsub⟩
  refine ⟨ε, hε, ?_⟩
  intro β hβ hβε
  exact hsub ⟨hβ, hβε⟩

/-- Contrapositive form useful for exact compatibility statements: if a
function vanishes at zero and also vanishes arbitrarily close to zero from the
right, then its derivative at zero cannot be nonzero. -/
theorem HasDerivAt.eq_zero_of_eq_zero_of_forall_exists_pos_lt_eq_zero
    {f : ℝ → ℝ}
    {d : ℝ}
    (hderiv : HasDerivAt f d 0)
    (hzero : f 0 = 0)
    (haccum : ∀ ε : ℝ, 0 < ε → ∃ β : ℝ, 0 < β ∧ β < ε ∧ f β = 0) :
    d = 0 := by
  by_contra hd
  rcases hderiv.exists_pos_forall_pos_lt_ne_zero_of_eq_zero_of_ne_zero hzero hd with
    ⟨ε, hε, hnonzero⟩
  rcases haccum ε hε with ⟨β, hβ, hβε, hβzero⟩
  exact (hnonzero β hβ hβε) hβzero

end

end MathlibAnalytic
end MGAP4D