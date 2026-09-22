import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferFixedContourRieszIdempotence
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-!
# Rank persistence for norm-close idempotents

This file isolates the functional-analytic mechanism needed to pass from
fixed-contour Riesz idempotence to rank-one persistence.

If two bounded complex-linear endomorphisms `Q` and `P` satisfy

* `Q * Q = Q`;
* `‖Q - P‖ < 1`;

then restriction of `P` to `range Q` is injective.  Consequently, whenever
`range P` is finite-dimensional, `range Q` is finite-dimensional and has
finrank at most that of `range P`.

No spectral input is used here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexConjugate

/-- An idempotent `Q` lying at operator-norm distance strictly less than one
from `P` has injective `P`-restriction on `range Q`. -/
theorem continuousLinearMap_rangeRestriction_injective_of_idempotent_norm_sub_lt_one
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (Q P : E →L[ℂ] E)
    (hQidem : Q * Q = Q)
    (hclose : ‖Q - P‖ < 1) :
    Function.Injective
      (fun x : Q.range =>
        (⟨P x.1, ⟨x.1, rfl⟩⟩ : P.range)) := by
  intro x y hxy
  apply Subtype.ext
  let z : E := x.1 - y.1
  have hQx : Q x.1 = x.1 := by
    rcases x.2 with ⟨u, hu⟩
    have happ := congrArg (fun T : E →L[ℂ] E => T u) hQidem
    change Q (Q u) = Q u at happ
    calc
      Q x.1 = Q (Q u) := by rw [hu]
      _ = Q u := happ
      _ = x.1 := hu
  have hQy : Q y.1 = y.1 := by
    rcases y.2 with ⟨u, hu⟩
    have happ := congrArg (fun T : E →L[ℂ] E => T u) hQidem
    change Q (Q u) = Q u at happ
    calc
      Q y.1 = Q (Q u) := by rw [hu]
      _ = Q u := happ
      _ = y.1 := hu
  have hPxy : P x.1 = P y.1 := by
    exact congrArg Subtype.val hxy
  have hQz : Q z = z := by
    dsimp [z]
    rw [Q.map_sub, hQx, hQy]
  have hPz : P z = 0 := by
    dsimp [z]
    rw [P.map_sub, hPxy, sub_self]
  have hzEq : z = (Q - P) z := by
    calc
      z = Q z := hQz.symm
      _ = Q z - P z := by rw [hPz, sub_zero]
      _ = (Q - P) z := by rw [ContinuousLinearMap.sub_apply]
  -- The printed norm expressions can hide different inherited instance paths.
  -- Unfold instances locally, without changing the ambient norm or hypotheses.
  have hbound :
      ‖(Q - P) z‖ ≤ ‖Q - P‖ * ‖z‖ := by
    with_reducible_and_instances
      exact ContinuousLinearMap.le_opNorm (Q - P) z
  have hnorm :
      ‖z‖ ≤ ‖Q - P‖ * ‖z‖ := by
    -- Rewrite only the left norm; rewriting z globally changes the right side too.
    calc
      ‖z‖ = ‖(Q - P) z‖ := by
        with_reducible_and_instances
          exact congrArg (fun v : E => ‖v‖) hzEq
      _ ≤ ‖Q - P‖ * ‖z‖ := hbound
  have hz : z = 0 := by
    by_cases hz0 : z = 0
    · exact hz0
    · have hnormPos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hstrict : ‖Q - P‖ * ‖z‖ < ‖z‖ := by
        calc
          ‖Q - P‖ * ‖z‖ < 1 * ‖z‖ :=
            mul_lt_mul_of_pos_right hclose hnormPos
          _ = ‖z‖ := one_mul ‖z‖
      exact False.elim ((not_lt_of_ge hnorm) hstrict)
  exact sub_eq_zero.mp hz

/-- Finrank cannot increase across a norm-<1 perturbation from an idempotent:
the range of `Q` injects linearly into the finite-dimensional range of `P`. -/
theorem continuousLinearMap_finrank_range_le_of_idempotent_norm_sub_lt_one
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (Q P : E →L[ℂ] E)
    (hQidem : Q * Q = Q)
    (hclose : ‖Q - P‖ < 1)
    [FiniteDimensional ℂ P.range] :
    Module.finrank ℂ Q.range ≤ Module.finrank ℂ P.range := by
  let f : Q.range →ₗ[ℂ] P.range :=
    { toFun := fun x => ⟨P x.1, ⟨x.1, rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact P.map_add x.1 y.1
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact P.map_smul c x.1 }
  have hf : Function.Injective f := by
    change Function.Injective
      (fun x : Q.range =>
        (⟨P x.1, ⟨x.1, rfl⟩⟩ : P.range))
    exact
      continuousLinearMap_rangeRestriction_injective_of_idempotent_norm_sub_lt_one
        Q P hQidem hclose
  letI : FiniteDimensional ℂ Q.range :=
    FiniteDimensional.of_injective f hf
  exact LinearMap.finrank_le_finrank_of_injective (f := f) hf

/-- In particular, if the comparison projection has finrank at most one, so
does the norm-close idempotent. -/
theorem continuousLinearMap_finrank_range_le_one_of_idempotent_norm_sub_lt_one
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (Q P : E →L[ℂ] E)
    (hQidem : Q * Q = Q)
    (hclose : ‖Q - P‖ < 1)
    [FiniteDimensional ℂ P.range]
    (hP : Module.finrank ℂ P.range ≤ 1) :
    Module.finrank ℂ Q.range ≤ 1 :=
  le_trans
    (continuousLinearMap_finrank_range_le_of_idempotent_norm_sub_lt_one
      Q P hQidem hclose)
    hP

end
end MathlibAnalytic
end MGAP4D
