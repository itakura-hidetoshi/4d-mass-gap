import MGAP4D.MathlibAnalytic.FiniteGroupInvariantOrbitFiberKernelCriterion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A scalar coefficient on a finite acted type is invariant under the group
action when it is constant along every orbit. -/
def FiniteGroupCoefficientInvariant
    (G α : Type)
    [Group G]
    [MulAction G α]
    (a : α → ℝ) : Prop :=
  ∀ g : G, ∀ x : α, a (g • x) = a x

/-- An invariant scalar coefficient takes the representative value everywhere
on a given orbit. -/
theorem finiteGroupCoefficientInvariant_value_eq_representative
    (G α : Type)
    [Group G]
    [MulAction G α]
    (a : α → ℝ)
    (ha : FiniteGroupCoefficientInvariant G α a)
    (q : FiniteGroupOrbitQuotient G α)
    (x : α)
    (hx : finiteGroupOrbitClass G α x = q) :
    a (finiteGroupOrbitRepresentative G α q) = a x := by
  have hclass :
      finiteGroupOrbitClass G α
          (finiteGroupOrbitRepresentative G α q) =
        finiteGroupOrbitClass G α x := by
    rw [finiteGroupOrbitClass_representative, hx]
  rcases (finiteGroupOrbitClass_eq_iff G α
      (finiteGroupOrbitRepresentative G α q) x).1 hclass with ⟨g, hg⟩
  have hInv := ha g (finiteGroupOrbitRepresentative G α q)
  rw [hg] at hInv
  exact hInv.symm

/-- Orbit aggregation of an invariant coefficient is exactly orbit counting
mass times the coefficient at the chosen representative. -/
theorem finiteGroupOrbitAggregateCoefficient_eq_mass_mul_representative
    (G α : Type)
    [Group G]
    [Fintype α]
    [MulAction G α]
    (a : α → ℝ)
    (ha : FiniteGroupCoefficientInvariant G α a)
    (q : FiniteGroupOrbitQuotient G α) :
    finiteGroupOrbitAggregateCoefficient G α a q =
      finiteGroupOrbitMass G α q *
        a (finiteGroupOrbitRepresentative G α q) := by
  classical
  unfold finiteGroupOrbitAggregateCoefficient finiteGroupOrbitMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hxq : finiteGroupOrbitClass G α x = q
  · have hval :=
      finiteGroupCoefficientInvariant_value_eq_representative
        G α a ha q x hxq
    simp [hxq, hxq.symm, hval]
  · have hqne : q ≠ finiteGroupOrbitClass G α x := by
      exact fun h => hxq h.symm
    simp [hxq, hqne]

/-- For invariant coefficients, equality after orbit aggregation on every orbit
is equivalent to pointwise equality on the original finite acted type. -/
theorem finiteGroupOrbitAggregateCoefficient_eq_all_iff_of_invariant
    (G α : Type)
    [Group G]
    [Fintype α]
    [Nonempty α]
    [MulAction G α]
    (a b : α → ℝ)
    (ha : FiniteGroupCoefficientInvariant G α a)
    (hb : FiniteGroupCoefficientInvariant G α b) :
    (∀ q : FiniteGroupOrbitQuotient G α,
      finiteGroupOrbitAggregateCoefficient G α a q =
        finiteGroupOrbitAggregateCoefficient G α b q) ↔
      ∀ x : α, a x = b x := by
  constructor
  · intro h x
    let q := finiteGroupOrbitClass G α x
    have hq := h q
    rw [finiteGroupOrbitAggregateCoefficient_eq_mass_mul_representative
          G α a ha q,
        finiteGroupOrbitAggregateCoefficient_eq_mass_mul_representative
          G α b hb q] at hq
    have hmass : 0 < finiteGroupOrbitMass G α q :=
      finiteGroupOrbitMass_pos G α q
    have hrep :
        a (finiteGroupOrbitRepresentative G α q) =
          b (finiteGroupOrbitRepresentative G α q) := by
      exact mul_left_cancel₀ (ne_of_gt hmass) hq
    have haRep :=
      finiteGroupCoefficientInvariant_value_eq_representative
        G α a ha q x rfl
    have hbRep :=
      finiteGroupCoefficientInvariant_value_eq_representative
        G α b hb q x rfl
    calc
      a x = a (finiteGroupOrbitRepresentative G α q) := haRep.symm
      _ = b (finiteGroupOrbitRepresentative G α q) := hrep
      _ = b x := hbRep
  · intro h q
    unfold finiteGroupOrbitAggregateCoefficient
    apply Finset.sum_congr rfl
    intro x _hx
    rw [h x]

/-- The action of a fixed group element is a bijection. -/
theorem finiteGroup_smul_bijective
    (G α : Type)
    [Group G]
    [MulAction G α]
    (g : G) :
    Function.Bijective (fun x : α => g • x) := by
  constructor
  · intro x y hxy
    have h := congrArg (fun z : α => g⁻¹ • z) hxy
    simpa [smul_smul] using h
  · intro y
    refine ⟨g⁻¹ • y, ?_⟩
    simp [smul_smul]

/-- Fibre pushforward through an equivariant finite map preserves coefficient
invariance when the fine-to-coarse group homomorphism is surjective. -/
theorem finiteFiberPushforwardCoefficient_invariant_of_equivariant_surjective
    (Gf Gc αf αc : Type)
    [Group Gf]
    [Group Gc]
    [Fintype αf]
    [Fintype αc]
    [MulAction Gf αf]
    [MulAction Gc αc]
    (φ : Gf →* Gc)
    (C : αf → αc)
    (hφ : Function.Surjective φ)
    (hC : ∀ g : Gf, ∀ x : αf, C (g • x) = φ g • C x)
    (w : αf → ℝ)
    (hw : FiniteGroupCoefficientInvariant Gf αf w) :
    FiniteGroupCoefficientInvariant Gc αc
      (finiteFiberPushforwardCoefficient C w) := by
  classical
  intro gc y
  rcases hφ gc with ⟨gf, rfl⟩
  unfold finiteFiberPushforwardCoefficient
  let F : αf → ℝ := fun x =>
    if C x = φ gf • y then w x else 0
  have hbij : Function.Bijective (fun x : αf => gf • x) :=
    finiteGroup_smul_bijective Gf αf gf
  calc
    (∑ x : αf, if C x = φ gf • y then w x else 0) =
        ∑ x : αf, F (gf • x) := by
      exact (hbij.sum_comp F).symm
    _ = ∑ x : αf, if C x = y then w x else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      dsimp [F]
      rw [hC gf x, hw gf x]
      have hinj : Function.Injective (fun z : αc => φ gf • z) :=
        (finiteGroup_smul_bijective Gc αc (φ gf)).1
      by_cases hxy : C x = y
      · simp [hxy]
      · have hne : φ gf • C x ≠ φ gf • y := by
          exact fun h => hxy (hinj h)
        simp [hxy, hne]

/-- Generic Package-I receipt combining orbit evaluation, cancellation of orbit
mass, and invariance of equivariant fibre pushforward. -/
structure FiniteGroupEquivariantFiberPushforwardOrbitEvaluationPackage
    (Gf Gc αf αc : Type)
    [Group Gf]
    [Group Gc]
    [Fintype αf]
    [Fintype αc]
    [Nonempty αc]
    [MulAction Gf αf]
    [MulAction Gc αc]
    (φ : Gf →* Gc)
    (C : αf → αc)
    (w : αf → ℝ) where
  groupSurjective : Function.Surjective φ
  equivariant : ∀ g x, C (g • x) = φ g • C x
  fineInvariant : FiniteGroupCoefficientInvariant Gf αf w
  pushforwardInvariant :
    FiniteGroupCoefficientInvariant Gc αc
      (finiteFiberPushforwardCoefficient C w)

/-- Construct the generic Package-I receipt. -/
noncomputable def finiteGroupEquivariantFiberPushforwardOrbitEvaluationPackage
    (Gf Gc αf αc : Type)
    [Group Gf]
    [Group Gc]
    [Fintype αf]
    [Fintype αc]
    [Nonempty αc]
    [MulAction Gf αf]
    [MulAction Gc αc]
    (φ : Gf →* Gc)
    (C : αf → αc)
    (hφ : Function.Surjective φ)
    (hC : ∀ g x, C (g • x) = φ g • C x)
    (w : αf → ℝ)
    (hw : FiniteGroupCoefficientInvariant Gf αf w) :
    FiniteGroupEquivariantFiberPushforwardOrbitEvaluationPackage
      Gf Gc αf αc φ C w where
  groupSurjective := hφ
  equivariant := hC
  fineInvariant := hw
  pushforwardInvariant :=
    finiteFiberPushforwardCoefficient_invariant_of_equivariant_surjective
      Gf Gc αf αc φ C hφ hC w hw

end

end MathlibAnalytic
end MGAP4D
