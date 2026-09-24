import Mathlib.Tactic

/-!
# Dependent normed-response families and transpose one-sided profiles

In the physical application, the response associated with a fixed source link
naturally lives in an L2 space built from that source's own pair/background
law.  Different source links therefore need not share one common normed
carrier.

This file packages the exact finite-dimensional algebra for a dependent family
of normed additive groups E(source).  For each source, all target-response
vectors live in E(source), so the finite triangle inequality applies inside
that one space:

  state_source
    = local_source + sum_target response_source,target.

If

  ||local_source|| <= ell_source
  ||response_source,target||
    <= K(target,source) * ||state_target||,

then the scalar norm profile satisfies the transpose recurrence

  ||state_source||
    <= ell_source
       + sum_target K(target,source) * ||state_target||.

No identification between the source-dependent vector spaces is required and
no finite-cardinality Cauchy--Schwarz factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace FiniteDependentNormedTransposeResponseProfile

/-- A dependent family of finite normed response decompositions gives the
transpose-oriented scalar norm recurrence without any cardinality loss. -/
theorem norm_profile_le_local_add_transpose_matrix
    {ι : Type*} [Fintype ι]
    (E : ι → Type*)
    [∀ i, NormedAddCommGroup (E i)]
    (matrix : ι → ι → ℝ)
    (state localPart : ∀ i, E i)
    (response : ∀ source target, E source)
    (localProfile : ι → ℝ)
    (hDecomp : ∀ source,
      state source = localPart source + ∑ target, response source target)
    (hLocal : ∀ source, ‖localPart source‖ ≤ localProfile source)
    (hResponse : ∀ source target,
      ‖response source target‖ ≤
        matrix target source * ‖state target‖)
    (source : ι) :
    ‖state source‖ ≤
      localProfile source +
        ∑ target, matrix target source * ‖state target‖ := by
  calc
    ‖state source‖ =
        ‖localPart source + ∑ target, response source target‖ := by
      rw [hDecomp source]
    _ ≤ ‖localPart source‖ + ‖∑ target, response source target‖ :=
      norm_add_le _ _
    _ ≤ ‖localPart source‖ + ∑ target, ‖response source target‖ := by
      exact add_le_add
        (le_refl ‖localPart source‖)
        (by
          simpa using
            norm_sum_le (Finset.univ : Finset ι)
              (fun target => response source target))
    _ ≤ localProfile source +
        ∑ target, matrix target source * ‖state target‖ := by
      exact add_le_add
        (hLocal source)
        (Finset.sum_le_sum fun target _ => hResponse source target)

/-- Functional form of the dependent transpose recurrence. -/
theorem norm_profile_transpose_oneSided
    {ι : Type*} [Fintype ι]
    (E : ι → Type*)
    [∀ i, NormedAddCommGroup (E i)]
    (matrix : ι → ι → ℝ)
    (state localPart : ∀ i, E i)
    (response : ∀ source target, E source)
    (localProfile : ι → ℝ)
    (hDecomp : ∀ source,
      state source = localPart source + ∑ target, response source target)
    (hLocal : ∀ source, ‖localPart source‖ ≤ localProfile source)
    (hResponse : ∀ source target,
      ‖response source target‖ ≤
        matrix target source * ‖state target‖) :
    ∀ source,
      ‖state source‖ ≤
        localProfile source +
          ∑ target, matrix target source * ‖state target‖ := by
  intro source
  exact
    norm_profile_le_local_add_transpose_matrix
      E matrix state localPart response localProfile
      hDecomp hLocal hResponse source

end FiniteDependentNormedTransposeResponseProfile

end

end MGAP4D.MathlibAnalytic
