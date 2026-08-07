import MGAP4D.MathlibAnalytic.FiniteGroupUniformProbabilityPushforward
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Every fibre of a surjective homomorphism between finite groups has exactly
the cardinality of its kernel. -/
theorem finiteSurjectiveGroupHom_fiber_count
    {G H : Type}
    [Group G]
    [Group H]
    [Fintype G]
    [Fintype H]
    (φ : G →* H)
    (hφ : Function.Surjective φ)
    (y : H) :
    (∑ x : G, if φ x = y then (1 : ℝ) else 0) =
      (Fintype.card φ.ker : ℝ) := by
  classical
  let E := finiteSurjectiveGroupHomEquivKerProd φ hφ
  calc
    (∑ x : G, if φ x = y then (1 : ℝ) else 0) =
      ∑ ky : φ.ker × H, if ky.2 = y then (1 : ℝ) else 0 := by
        exact Fintype.sum_equiv E _ _ (fun x => by rfl)
    _ = ∑ k : φ.ker, ∑ z : H,
        if z = y then (1 : ℝ) else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ _k : φ.ker, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _hk
      simp
    _ = (Fintype.card φ.ker : ℝ) := by simp

/-- Pulling any finite target predicate back through a surjective finite group
homomorphism multiplies its counting mass by the kernel cardinality. -/
theorem finiteSurjectiveGroupHom_predicate_count
    {G H : Type}
    [Group G]
    [Group H]
    [Fintype G]
    [Fintype H]
    (φ : G →* H)
    (hφ : Function.Surjective φ)
    (P : H → Prop)
    [DecidablePred P] :
    (∑ x : G, if P (φ x) then (1 : ℝ) else 0) =
      (Fintype.card φ.ker : ℝ) *
        ∑ y : H, if P y then (1 : ℝ) else 0 := by
  classical
  let E := finiteSurjectiveGroupHomEquivKerProd φ hφ
  calc
    (∑ x : G, if P (φ x) then (1 : ℝ) else 0) =
      ∑ ky : φ.ker × H,
        if P ky.2 then (1 : ℝ) else 0 := by
          exact Fintype.sum_equiv E _ _ (fun x => by rfl)
    _ = ∑ k : φ.ker, ∑ y : H,
        if P y then (1 : ℝ) else 0 := by
      rw [Fintype.sum_prod_type]
    _ = (Fintype.card φ.ker : ℝ) *
        ∑ y : H, if P y then (1 : ℝ) else 0 := by
      simp

/-- Orbit aggregation is a special case: the preimage of one target orbit has
kernel-cardinality times the target orbit mass. -/
theorem finiteSurjectiveGroupHom_orbit_preimage_count
    {G H K : Type}
    [Group G]
    [Group H]
    [Fintype G]
    [Fintype H]
    [Group K]
    [MulAction K H]
    (φ : G →* H)
    (hφ : Function.Surjective φ)
    (q : FiniteGroupOrbitQuotient K H) :
    (∑ x : G,
      if finiteGroupOrbitClass K H (φ x) = q then (1 : ℝ) else 0) =
      (Fintype.card φ.ker : ℝ) * finiteGroupOrbitMass K H q := by
  classical
  simpa [finiteGroupOrbitMass, eq_comm] using
    (finiteSurjectiveGroupHom_predicate_count φ hφ
      (fun y : H => finiteGroupOrbitClass K H y = q))

end

end MathlibAnalytic
end MGAP4D
