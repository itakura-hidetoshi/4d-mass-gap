import MGAP4D.MathlibAnalytic.FiniteGroupOrbitProbabilityL2Realization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Orbit class is unchanged by the group action. -/
@[simp] theorem finiteGroupOrbitClass_smul
    (G α : Type)
    [Group G]
    [MulAction G α]
    (g : G)
    (x : α) :
    finiteGroupOrbitClass G α (g • x) =
      finiteGroupOrbitClass G α x := by
  symm
  exact (finiteGroupOrbitClass_eq_iff G α x (g • x)).2 ⟨g, rfl⟩

/-- Indicator of one orbit, regarded as an invariant Euclidean vector. -/
noncomputable def finiteGroupOrbitInvariantIndicator
    (G α : Type)
    [Group G]
    [Fintype α]
    [MulAction G α]
    (q : FiniteGroupOrbitQuotient G α) :
    finiteGroupInvariantSubmodule G α :=
  ⟨WithLp.toLp 2 fun x : α =>
      if finiteGroupOrbitClass G α x = q then 1 else 0,
    by
      intro g x
      change
        (if finiteGroupOrbitClass G α (g • x) = q then (1 : ℝ) else 0) =
          if finiteGroupOrbitClass G α x = q then 1 else 0
      rw [finiteGroupOrbitClass_smul G α g x]⟩

@[simp] theorem finiteGroupOrbitInvariantIndicator_apply
    (G α : Type)
    [Group G]
    [Fintype α]
    [MulAction G α]
    (q : FiniteGroupOrbitQuotient G α)
    (x : α) :
    (finiteGroupOrbitInvariantIndicator G α q).1 x =
      if finiteGroupOrbitClass G α x = q then 1 else 0 :=
  rfl

/-- Finite pushforward of scalar coefficients through a map. -/
noncomputable def finiteFiberPushforwardCoefficient
    {α β : Type}
    [Fintype α]
    [Fintype β]
    (C : β → α)
    (w : β → ℝ)
    (x : α) : ℝ :=
  ∑ z : β, if C z = x then w z else 0

/-- Aggregation of coefficients over one group orbit. -/
noncomputable def finiteGroupOrbitAggregateCoefficient
    (G α : Type)
    [Group G]
    [Fintype α]
    [MulAction G α]
    (a : α → ℝ)
    (q : FiniteGroupOrbitQuotient G α) : ℝ :=
  ∑ x : α,
    if finiteGroupOrbitClass G α x = q then a x else 0

/-- Direct orbit aggregation after mapping a second finite type into the acted
configuration type. -/
noncomputable def finiteGroupOrbitFiberCoefficient
    (G α : Type)
    {β : Type}
    [Group G]
    [Fintype α]
    [Fintype β]
    [MulAction G α]
    (C : β → α)
    (w : β → ℝ)
    (q : FiniteGroupOrbitQuotient G α) : ℝ :=
  ∑ z : β,
    if finiteGroupOrbitClass G α (C z) = q then w z else 0

/-- Ordinary fibre pushforward is characterized by testing against arbitrary
functions on the target finite type. -/
theorem finiteFiberPushforwardCoefficient_sum_mul
    {α β : Type}
    [Fintype α]
    [Fintype β]
    (C : β → α)
    (w : β → ℝ)
    (f : α → ℝ) :
    (∑ z : β, w z * f (C z)) =
      ∑ x : α, finiteFiberPushforwardCoefficient C w x * f x := by
  classical
  unfold finiteFiberPushforwardCoefficient
  calc
    (∑ z : β, w z * f (C z)) =
        ∑ z : β, ∑ x : α,
          if C z = x then w z * f x else 0 := by
      apply Finset.sum_congr rfl
      intro z _hz
      simp
    _ = ∑ x : α, ∑ z : β,
          if C z = x then w z * f x else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x : α,
          (∑ z : β, if C z = x then w z else 0) * f x := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _hz
      by_cases hzx : C z = x
      · simp [hzx]
      · simp [hzx]

/-- Fibre pushforward is functorial under composition of finite maps. -/
theorem finiteFiberPushforwardCoefficient_comp
    {α β γ : Type}
    [Fintype α]
    [Fintype β]
    [Fintype γ]
    (C₁ : β → α)
    (C₂ : γ → β)
    (w : γ → ℝ)
    (x : α) :
    finiteFiberPushforwardCoefficient C₁
        (finiteFiberPushforwardCoefficient C₂ w) x =
      finiteFiberPushforwardCoefficient (fun z => C₁ (C₂ z)) w x := by
  classical
  unfold finiteFiberPushforwardCoefficient
  calc
    (∑ y : β,
      if C₁ y = x then
        ∑ z : γ, if C₂ z = y then w z else 0
      else 0) =
        ∑ y : β, ∑ z : γ,
          if C₁ y = x then
            if C₂ z = y then w z else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro y _hy
      by_cases hyx : C₁ y = x
      · simp [hyx]
      · simp [hyx]
    _ = ∑ z : γ, ∑ y : β,
          if C₁ y = x then
            if C₂ z = y then w z else 0
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ z : γ,
          if C₁ (C₂ z) = x then w z else 0 := by
      apply Finset.sum_congr rfl
      intro z _hz
      by_cases hzx : C₁ (C₂ z) = x
      · simp [hzx]
      · have hnone : ∀ y : β,
            C₂ z = y → C₁ y ≠ x := by
          intro y hy
          subst y
          exact hzx
        simp [hzx, hnone]

/-- Orbit aggregation of an ordinary fibre pushforward is the direct sum over
fine points whose image belongs to the chosen orbit. -/
theorem finiteGroupOrbitAggregate_fiberPushforward
    (G α : Type)
    {β : Type}
    [Group G]
    [Fintype α]
    [Fintype β]
    [MulAction G α]
    (C : β → α)
    (w : β → ℝ)
    (q : FiniteGroupOrbitQuotient G α) :
    finiteGroupOrbitAggregateCoefficient G α
        (finiteFiberPushforwardCoefficient C w) q =
      finiteGroupOrbitFiberCoefficient G α C w q := by
  classical
  unfold finiteGroupOrbitAggregateCoefficient
  unfold finiteFiberPushforwardCoefficient
  unfold finiteGroupOrbitFiberCoefficient
  calc
    (∑ x : α,
      if finiteGroupOrbitClass G α x = q then
        ∑ z : β, if C z = x then w z else 0
      else 0) =
        ∑ x : α, ∑ z : β,
          if finiteGroupOrbitClass G α x = q then
            if C z = x then w z else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hxq : finiteGroupOrbitClass G α x = q
      · simp [hxq]
      · simp [hxq]
    _ = ∑ z : β, ∑ x : α,
          if finiteGroupOrbitClass G α x = q then
            if C z = x then w z else 0
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ z : β,
          if finiteGroupOrbitClass G α (C z) = q then w z else 0 := by
      apply Finset.sum_congr rfl
      intro z _hz
      by_cases hzq : finiteGroupOrbitClass G α (C z) = q
      · simp [hzq]
      · have hnone : ∀ x : α,
            C z = x → finiteGroupOrbitClass G α x ≠ q := by
          intro x hx
          subst x
          exact hzq
        simp [hzq, hnone]

/-- Weighted evaluation against an invariant vector decomposes exactly into
orbit coefficients times the representative value. -/
theorem finiteGroupInvariant_weightedCrossSum_orbit_decomposition
    (G α : Type)
    {β : Type}
    [Group G]
    [Fintype α]
    [Fintype β]
    [MulAction G α]
    (C : β → α)
    (w : β → ℝ)
    (f : finiteGroupInvariantSubmodule G α) :
    (∑ z : β, w z * f.1 (C z)) =
      ∑ q : FiniteGroupOrbitQuotient G α,
        f.1 (finiteGroupOrbitRepresentative G α q) *
          finiteGroupOrbitFiberCoefficient G α C w q := by
  classical
  unfold finiteGroupOrbitFiberCoefficient
  calc
    (∑ z : β, w z * f.1 (C z)) =
        ∑ z : β, ∑ q : FiniteGroupOrbitQuotient G α,
          if finiteGroupOrbitClass G α (C z) = q then
            w z * f.1 (C z)
          else 0 := by
      apply Finset.sum_congr rfl
      intro z _hz
      simp
    _ = ∑ q : FiniteGroupOrbitQuotient G α,
          ∑ z : β,
            if finiteGroupOrbitClass G α (C z) = q then
              w z * f.1 (C z)
            else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ q : FiniteGroupOrbitQuotient G α,
          f.1 (finiteGroupOrbitRepresentative G α q) *
            ∑ z : β,
              if finiteGroupOrbitClass G α (C z) = q then w z else 0 := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _hz
      by_cases hzq : finiteGroupOrbitClass G α (C z) = q
      · have hval :
            f.1 (finiteGroupOrbitRepresentative G α q) = f.1 (C z) :=
          finiteGroupInvariant_value_eq_representative
            G α f q (C z) hzq.symm
        simp [hzq, hval]
        ring
      · simp [hzq]

/-- Equality of two finite coefficient functionals on every invariant vector
is equivalent to equality of their coefficients after aggregation over each
orbit.  The left coefficients may live on a different finite type and are
first pulled through the map `C`. -/
theorem finiteGroupInvariant_crossSum_eq_iff_orbitFiberSums
    (G α : Type)
    {β : Type}
    [Group G]
    [Fintype α]
    [Fintype β]
    [MulAction G α]
    (C : β → α)
    (w : β → ℝ)
    (v : α → ℝ) :
    (∀ f : finiteGroupInvariantSubmodule G α,
      (∑ z : β, w z * f.1 (C z)) =
        ∑ x : α, v x * f.1 x) ↔
      ∀ q : FiniteGroupOrbitQuotient G α,
        finiteGroupOrbitFiberCoefficient G α C w q =
          finiteGroupOrbitAggregateCoefficient G α v q := by
  classical
  constructor
  · intro h q
    have hq := h (finiteGroupOrbitInvariantIndicator G α q)
    unfold finiteGroupOrbitFiberCoefficient
    unfold finiteGroupOrbitAggregateCoefficient
    simpa using hq
  · intro h f
    calc
      (∑ z : β, w z * f.1 (C z)) =
          ∑ q : FiniteGroupOrbitQuotient G α,
            f.1 (finiteGroupOrbitRepresentative G α q) *
              finiteGroupOrbitFiberCoefficient G α C w q :=
        finiteGroupInvariant_weightedCrossSum_orbit_decomposition
          G α C w f
      _ = ∑ q : FiniteGroupOrbitQuotient G α,
            f.1 (finiteGroupOrbitRepresentative G α q) *
              finiteGroupOrbitAggregateCoefficient G α v q := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [h q]
      _ = ∑ x : α, v x * f.1 x := by
        symm
        simpa [finiteGroupOrbitAggregateCoefficient,
          finiteGroupOrbitFiberCoefficient] using
          (finiteGroupInvariant_weightedCrossSum_orbit_decomposition
            G α (fun x : α => x) v f)

/-- A compact generic Package-H receipt: invariant-functional equality,
ordinary fibre pushforward, orbit aggregation, and direct orbit-fibre equality
are the same finite coarse-graining datum. -/
theorem finiteGroupInvariantOrbitFiberKernelCriterionPackage
    (G α : Type)
    {β : Type}
    [Group G]
    [Fintype α]
    [Fintype β]
    [MulAction G α]
    (C : β → α)
    (w : β → ℝ)
    (v : α → ℝ) :
    ((∀ f : finiteGroupInvariantSubmodule G α,
        (∑ z : β, w z * f.1 (C z)) =
          ∑ x : α, v x * f.1 x) ↔
      ∀ q : FiniteGroupOrbitQuotient G α,
        finiteGroupOrbitFiberCoefficient G α C w q =
          finiteGroupOrbitAggregateCoefficient G α v q) ∧
    (∀ q : FiniteGroupOrbitQuotient G α,
      finiteGroupOrbitAggregateCoefficient G α
          (finiteFiberPushforwardCoefficient C w) q =
        finiteGroupOrbitFiberCoefficient G α C w q) := by
  exact ⟨
    finiteGroupInvariant_crossSum_eq_iff_orbitFiberSums G α C w v,
    finiteGroupOrbitAggregate_fiberPushforward G α C w⟩

end

end MathlibAnalytic
end MGAP4D
