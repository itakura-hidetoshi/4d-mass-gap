import Mathlib.Tactic

/-!
# Finite normed response decomposition to one-sided scalar profiles

This file packages the volume-free algebra needed after a hybrid/trajectory
construction has produced a normed response decomposition

  state_t = local_t + sum_s response_{t,s}.

If the local vector is bounded by a scalar local profile and each source
response vector is bounded by K(t,s) times the source state norm, then the
scalar norm profile automatically satisfies

  ||state_t|| <= localProfile_t + sum_s K(t,s) ||state_s||.

Only the triangle inequality and the norm bound for a finite sum are used.
There is no finite-cardinality Cauchy--Schwarz factor.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace FiniteNormedResponseOneSidedProfile

/-- A finite normed vector decomposition gives the exact scalar one-sided
profile recurrence without any cardinality loss. -/
theorem norm_profile_le_local_add_matrix
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    (matrix : ι → ι → ℝ)
    (state local : ι → E)
    (response : ι → ι → E)
    (localProfile : ι → ℝ)
    (hDecomp : ∀ target,
      state target = local target + ∑ source, response target source)
    (hLocal : ∀ target, ‖local target‖ ≤ localProfile target)
    (hResponse : ∀ target source,
      ‖response target source‖ ≤ matrix target source * ‖state source‖)
    (target : ι) :
    ‖state target‖ ≤
      localProfile target +
        ∑ source, matrix target source * ‖state source‖ := by
  calc
    ‖state target‖ =
        ‖local target + ∑ source, response target source‖ := by
          rw [hDecomp target]
    _ ≤ ‖local target‖ + ‖∑ source, response target source‖ :=
      norm_add_le _ _
    _ ≤ ‖local target‖ + ∑ source, ‖response target source‖ := by
      exact add_le_add_left
        (by
          simpa using
            norm_sum_le (Finset.univ : Finset ι)
              (fun source => response target source))
        ‖local target‖
    _ ≤ localProfile target +
        ∑ source, matrix target source * ‖state source‖ := by
      exact add_le_add
        (hLocal target)
        (Finset.sum_le_sum fun source _ => hResponse target source)

/-- Functional form: the norm profile of the state family satisfies the
one-sided recurrence at every index. -/
theorem norm_profile_oneSided
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    (matrix : ι → ι → ℝ)
    (state local : ι → E)
    (response : ι → ι → E)
    (localProfile : ι → ℝ)
    (hDecomp : ∀ target,
      state target = local target + ∑ source, response target source)
    (hLocal : ∀ target, ‖local target‖ ≤ localProfile target)
    (hResponse : ∀ target source,
      ‖response target source‖ ≤ matrix target source * ‖state source‖) :
    ∀ target,
      ‖state target‖ ≤
        localProfile target +
          ∑ source, matrix target source * ‖state source‖ := by
  intro target
  exact
    norm_profile_le_local_add_matrix
      matrix state local response localProfile
      hDecomp hLocal hResponse target

end FiniteNormedResponseOneSidedProfile

end

end MGAP4D.MathlibAnalytic
