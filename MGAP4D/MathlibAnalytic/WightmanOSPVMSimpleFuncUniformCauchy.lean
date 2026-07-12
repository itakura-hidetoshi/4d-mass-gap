import MGAP4D.MathlibAnalytic.WightmanOSPVMSimpleFuncSpectralIntegral
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Filter Topology MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

/-- The common spectral carrier on which two simple functions take one fixed
ordered pair of values. -/
def pvmSimpleFuncPairFiber
    (f g : SimpleFunc ℝ ℝ) (c : (f.pair g).range) : Set ℝ :=
  (f.pair g) ⁻¹' ({(c : ℝ × ℝ)} : Set (ℝ × ℝ))

/-- Common pair fibers are measurable. -/
theorem pvmSimpleFuncPairFiber_measurable
    (f g : SimpleFunc ℝ ℝ) (c : (f.pair g).range) :
    MeasurableSet (pvmSimpleFuncPairFiber f g c) := by
  exact (f.pair g).measurableSet_fiber (c : ℝ × ℝ)

/-- Distinct values of the pair simple function have disjoint fibers. -/
theorem pvmSimpleFuncPairFiber_pairwise_disjoint
    (f g : SimpleFunc ℝ ℝ) :
    Pairwise (Function.onFun Disjoint (pvmSimpleFuncPairFiber f g)) := by
  intro a b hab
  change Disjoint (pvmSimpleFuncPairFiber f g a)
    (pvmSimpleFuncPairFiber f g b)
  rw [Set.disjoint_left]
  intro x hxa hxb
  have hqa : (f.pair g) x = (a : ℝ × ℝ) := by
    simpa [pvmSimpleFuncPairFiber] using hxa
  have hqb : (f.pair g) x = (b : ℝ × ℝ) := by
    simpa [pvmSimpleFuncPairFiber] using hxb
  apply hab
  apply Subtype.ext
  exact hqa.symm.trans hqb

/-- The common pair fibers cover the whole spectral line. -/
theorem pvmSimpleFuncPairFiber_iUnion_eq_univ
    (f g : SimpleFunc ℝ ℝ) :
    (⋃ c : (f.pair g).range, pvmSimpleFuncPairFiber f g c) = Set.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    rw [Set.mem_iUnion]
    refine ⟨⟨(f.pair g) x, SimpleFunc.mem_range_self (f.pair g) x⟩, ?_⟩
    simp [pvmSimpleFuncPairFiber]

/-- First-coordinate map from the common pair range to the range of `f`. -/
def pvmSimpleFuncPairRangeFst
    (f g : SimpleFunc ℝ ℝ) (c : (f.pair g).range) : f.range := by
  refine ⟨(c : ℝ × ℝ).1, ?_⟩
  rcases SimpleFunc.mem_range.mp c.property with ⟨x, hx⟩
  apply SimpleFunc.mem_range.mpr
  refine ⟨x, ?_⟩
  have h := congrArg Prod.fst hx
  simpa [SimpleFunc.pair_apply] using h

/-- Second-coordinate map from the common pair range to the range of `g`. -/
def pvmSimpleFuncPairRangeSnd
    (f g : SimpleFunc ℝ ℝ) (c : (f.pair g).range) : g.range := by
  refine ⟨(c : ℝ × ℝ).2, ?_⟩
  rcases SimpleFunc.mem_range.mp c.property with ⟨x, hx⟩
  apply SimpleFunc.mem_range.mpr
  refine ⟨x, ?_⟩
  have h := congrArg Prod.snd hx
  simpa [SimpleFunc.pair_apply] using h

@[simp] theorem pvmSimpleFuncPairRangeFst_val
    (f g : SimpleFunc ℝ ℝ) (c : (f.pair g).range) :
    ((pvmSimpleFuncPairRangeFst f g c : f.range) : ℝ) =
      (c : ℝ × ℝ).1 :=
  rfl

@[simp] theorem pvmSimpleFuncPairRangeSnd_val
    (f g : SimpleFunc ℝ ℝ) (c : (f.pair g).range) :
    ((pvmSimpleFuncPairRangeSnd f g c : g.range) : ℝ) =
      (c : ℝ × ℝ).2 :=
  rfl

/-- The fiber of one value of `f` is the finite disjoint union of the common
pair fibers with that first coordinate. -/
theorem pvmSimpleFuncFiber_eq_pairFiberUnion_fst
    (f g : SimpleFunc ℝ ℝ) (a : f.range) :
    pvmSimpleFuncFiber f a =
      pvmFiniteCarrierUnion
        (Finset.univ.filter
          (fun c : (f.pair g).range =>
            pvmSimpleFuncPairRangeFst f g c = a))
        (pvmSimpleFuncPairFiber f g) := by
  ext x
  constructor
  · intro hx
    let c : (f.pair g).range :=
      ⟨(f.pair g) x, SimpleFunc.mem_range_self (f.pair g) x⟩
    rw [pvmFiniteCarrierUnion, Set.mem_iUnion]
    refine ⟨c, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ c, ?_⟩
      apply Subtype.ext
      simpa [c, pvmSimpleFuncPairRangeFst, pvmSimpleFuncFiber] using hx
    · simp [pvmSimpleFuncPairFiber, c]
  · intro hx
    rw [pvmFiniteCarrierUnion] at hx
    rcases Set.mem_iUnion.mp hx with ⟨c, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hc, hxc⟩
    have hcFst :
        pvmSimpleFuncPairRangeFst f g c = a :=
      (Finset.mem_filter.mp hc).2
    have hPair : (f.pair g) x = (c : ℝ × ℝ) := by
      simpa [pvmSimpleFuncPairFiber] using hxc
    have hFst : f x = (c : ℝ × ℝ).1 := by
      have h := congrArg Prod.fst hPair
      simpa [SimpleFunc.pair_apply] using h
    have hcVal : (c : ℝ × ℝ).1 = (a : ℝ) := by
      exact congrArg Subtype.val hcFst
    simpa [pvmSimpleFuncFiber, hFst, hcVal]

/-- The analogous common-fiber decomposition for one value of `g`. -/
theorem pvmSimpleFuncFiber_eq_pairFiberUnion_snd
    (f g : SimpleFunc ℝ ℝ) (b : g.range) :
    pvmSimpleFuncFiber g b =
      pvmFiniteCarrierUnion
        (Finset.univ.filter
          (fun c : (f.pair g).range =>
            pvmSimpleFuncPairRangeSnd f g c = b))
        (pvmSimpleFuncPairFiber f g) := by
  ext x
  constructor
  · intro hx
    let c : (f.pair g).range :=
      ⟨(f.pair g) x, SimpleFunc.mem_range_self (f.pair g) x⟩
    rw [pvmFiniteCarrierUnion, Set.mem_iUnion]
    refine ⟨c, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ c, ?_⟩
      apply Subtype.ext
      simpa [c, pvmSimpleFuncPairRangeSnd, pvmSimpleFuncFiber] using hx
    · simp [pvmSimpleFuncPairFiber, c]
  · intro hx
    rw [pvmFiniteCarrierUnion] at hx
    rcases Set.mem_iUnion.mp hx with ⟨c, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hc, hxc⟩
    have hcSnd :
        pvmSimpleFuncPairRangeSnd f g c = b :=
      (Finset.mem_filter.mp hc).2
    have hPair : (f.pair g) x = (c : ℝ × ℝ) := by
      simpa [pvmSimpleFuncPairFiber] using hxc
    have hSnd : g x = (c : ℝ × ℝ).2 := by
      have h := congrArg Prod.snd hPair
      simpa [SimpleFunc.pair_apply] using h
    have hcVal : (c : ℝ × ℝ).2 = (b : ℝ) := by
      exact congrArg Subtype.val hcSnd
    simpa [pvmSimpleFuncFiber, hSnd, hcVal]

/-- Projection onto a coarse `f` fiber is the sum of the projections onto its
common pair-fiber refinement. -/
theorem orthogonalProjectionValuedSetFunction_projection_simpleFiber_eq_sum_pairFst
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f g : SimpleFunc ℝ ℝ) (a : f.range) (x : H) :
    P.projection (pvmSimpleFuncFiber f a) x =
      ∑ c ∈ Finset.univ.filter
        (fun c : (f.pair g).range =>
          pvmSimpleFuncPairRangeFst f g c = a),
        P.projection (pvmSimpleFuncPairFiber f g c) x := by
  rw [pvmSimpleFuncFiber_eq_pairFiberUnion_fst f g a]
  exact
    orthogonalProjectionValuedSetFunction_projection_finiteCarrierUnion_eq_sum
      P (pvmSimpleFuncPairFiber f g)
        (pvmSimpleFuncPairFiber_pairwise_disjoint f g)
        (Finset.univ.filter
          (fun c : (f.pair g).range =>
            pvmSimpleFuncPairRangeFst f g c = a)) x

/-- Projection onto a coarse `g` fiber is the sum of the projections onto its
common pair-fiber refinement. -/
theorem orthogonalProjectionValuedSetFunction_projection_simpleFiber_eq_sum_pairSnd
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f g : SimpleFunc ℝ ℝ) (b : g.range) (x : H) :
    P.projection (pvmSimpleFuncFiber g b) x =
      ∑ c ∈ Finset.univ.filter
        (fun c : (f.pair g).range =>
          pvmSimpleFuncPairRangeSnd f g c = b),
        P.projection (pvmSimpleFuncPairFiber f g c) x := by
  rw [pvmSimpleFuncFiber_eq_pairFiberUnion_snd f g b]
  exact
    orthogonalProjectionValuedSetFunction_projection_finiteCarrierUnion_eq_sum
      P (pvmSimpleFuncPairFiber f g)
        (pvmSimpleFuncPairFiber_pairwise_disjoint f g)
        (Finset.univ.filter
          (fun c : (f.pair g).range =>
            pvmSimpleFuncPairRangeSnd f g c = b)) x

/-- A spectral integral written on the canonical common refinement of two
simple functions. -/
def pvmSimpleFuncPairSpectralIntegralOperator
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f g : SimpleFunc ℝ ℝ)
    (coefficient : ℝ × ℝ → ℝ) : H →L[ℝ] H :=
  pvmFiniteSimpleSpectralIntegralOperator P
    (fun c : (f.pair g).range => coefficient (c : ℝ × ℝ))
    (pvmSimpleFuncPairFiber f g)

@[simp] theorem pvmSimpleFuncPairSpectralIntegralOperator_apply
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f g : SimpleFunc ℝ ℝ)
    (coefficient : ℝ × ℝ → ℝ) (x : H) :
    pvmSimpleFuncPairSpectralIntegralOperator P f g coefficient x =
      ∑ c : (f.pair g).range,
        coefficient (c : ℝ × ℝ) •
          P.projection (pvmSimpleFuncPairFiber f g c) x := by
  rw [pvmFiniteSimpleSpectralIntegralOperator_apply]
  rfl

/-- The first-coordinate common-refinement integral is the canonical integral
of `f`. -/
theorem pvmSimpleFuncPairSpectralIntegralOperator_fst_eq
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f g : SimpleFunc ℝ ℝ) :
    pvmSimpleFuncPairSpectralIntegralOperator P f g Prod.fst =
      pvmSimpleFuncSpectralIntegralOperator P f := by
  ext x
  rw [pvmSimpleFuncPairSpectralIntegralOperator_apply,
    pvmSimpleFuncSpectralIntegralOperator_apply]
  unfold pvmFiniteSimpleSpectralIntegral
  symm
  calc
    (∑ a : f.range,
        (a : ℝ) • P.projection (pvmSimpleFuncFiber f a) x) =
      ∑ a : f.range,
        (a : ℝ) •
          ∑ c ∈ Finset.univ.filter
            (fun c : (f.pair g).range =>
              pvmSimpleFuncPairRangeFst f g c = a),
            P.projection (pvmSimpleFuncPairFiber f g c) x := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [orthogonalProjectionValuedSetFunction_projection_simpleFiber_eq_sum_pairFst]
    _ = ∑ a : f.range,
        ∑ c ∈ Finset.univ.filter
          (fun c : (f.pair g).range =>
            pvmSimpleFuncPairRangeFst f g c = a),
          (a : ℝ) • P.projection (pvmSimpleFuncPairFiber f g c) x := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.smul_sum]
    _ = ∑ a : f.range,
        ∑ c ∈ Finset.univ.filter
          (fun c : (f.pair g).range =>
            pvmSimpleFuncPairRangeFst f g c = a),
          (c : ℝ × ℝ).1 •
            P.projection (pvmSimpleFuncPairFiber f g c) x := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro c hc
      have hca :=
        (Finset.mem_filter.mp hc).2
      have hval :
          (c : ℝ × ℝ).1 = (a : ℝ) := by
        exact congrArg Subtype.val hca
      rw [hval]
    _ = ∑ c : (f.pair g).range,
        (c : ℝ × ℝ).1 •
          P.projection (pvmSimpleFuncPairFiber f g c) x := by
      simpa using
        (Finset.sum_fiberwise
          (s := (Finset.univ : Finset (f.pair g).range))
          (g := pvmSimpleFuncPairRangeFst f g)
          (f := fun c : (f.pair g).range =>
            (c : ℝ × ℝ).1 •
              P.projection (pvmSimpleFuncPairFiber f g c) x))

/-- The second-coordinate common-refinement integral is the canonical integral
of `g`. -/
theorem pvmSimpleFuncPairSpectralIntegralOperator_snd_eq
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f g : SimpleFunc ℝ ℝ) :
    pvmSimpleFuncPairSpectralIntegralOperator P f g Prod.snd =
      pvmSimpleFuncSpectralIntegralOperator P g := by
  ext x
  rw [pvmSimpleFuncPairSpectralIntegralOperator_apply,
    pvmSimpleFuncSpectralIntegralOperator_apply]
  unfold pvmFiniteSimpleSpectralIntegral
  symm
  calc
    (∑ b : g.range,
        (b : ℝ) • P.projection (pvmSimpleFuncFiber g b) x) =
      ∑ b : g.range,
        (b : ℝ) •
          ∑ c ∈ Finset.univ.filter
            (fun c : (f.pair g).range =>
              pvmSimpleFuncPairRangeSnd f g c = b),
            P.projection (pvmSimpleFuncPairFiber f g c) x := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [orthogonalProjectionValuedSetFunction_projection_simpleFiber_eq_sum_pairSnd]
    _ = ∑ b : g.range,
        ∑ c ∈ Finset.univ.filter
          (fun c : (f.pair g).range =>
            pvmSimpleFuncPairRangeSnd f g c = b),
          (b : ℝ) • P.projection (pvmSimpleFuncPairFiber f g c) x := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.smul_sum]
    _ = ∑ b : g.range,
        ∑ c ∈ Finset.univ.filter
          (fun c : (f.pair g).range =>
            pvmSimpleFuncPairRangeSnd f g c = b),
          (c : ℝ × ℝ).2 •
            P.projection (pvmSimpleFuncPairFiber f g c) x := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      have hcb :=
        (Finset.mem_filter.mp hc).2
      have hval :
          (c : ℝ × ℝ).2 = (b : ℝ) := by
        exact congrArg Subtype.val hcb
      rw [hval]
    _ = ∑ c : (f.pair g).range,
        (c : ℝ × ℝ).2 •
          P.projection (pvmSimpleFuncPairFiber f g c) x := by
      simpa using
        (Finset.sum_fiberwise
          (s := (Finset.univ : Finset (f.pair g).range))
          (g := pvmSimpleFuncPairRangeSnd f g)
          (f := fun c : (f.pair g).range =>
            (c : ℝ × ℝ).2 •
              P.projection (pvmSimpleFuncPairFiber f g c) x))

/-- The difference of canonical simple-function spectral integrals is the
common-refinement integral of the pointwise coefficient difference. -/
theorem pvmSimpleFuncPairSpectralIntegralOperator_sub_eq
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f g : SimpleFunc ℝ ℝ) :
    pvmSimpleFuncPairSpectralIntegralOperator P f g
        (fun p => p.1 - p.2) =
      pvmSimpleFuncSpectralIntegralOperator P f -
        pvmSimpleFuncSpectralIntegralOperator P g := by
  calc
    pvmSimpleFuncPairSpectralIntegralOperator P f g
        (fun p => p.1 - p.2) =
      pvmSimpleFuncPairSpectralIntegralOperator P f g Prod.fst -
        pvmSimpleFuncPairSpectralIntegralOperator P f g Prod.snd := by
          ext x
          simp [pvmSimpleFuncPairSpectralIntegralOperator_apply,
            sub_smul, Finset.sum_sub_distrib]
    _ = pvmSimpleFuncSpectralIntegralOperator P f -
        pvmSimpleFuncSpectralIntegralOperator P g := by
      rw [pvmSimpleFuncPairSpectralIntegralOperator_fst_eq,
        pvmSimpleFuncPairSpectralIntegralOperator_snd_eq]

/-- A uniform pointwise bound on two simple functions bounds every coefficient
difference on their common finite refinement. -/
theorem pvmSimpleFuncPair_range_sub_abs_le
    (f g : SimpleFunc ℝ ℝ)
    (C : ℝ)
    (hBound : ∀ t : ℝ, ‖f t - g t‖ ≤ C)
    (c : (f.pair g).range) :
    |(c : ℝ × ℝ).1 - (c : ℝ × ℝ).2| ≤ C := by
  rcases SimpleFunc.mem_range.mp c.property with ⟨t, ht⟩
  have hFst : f t = (c : ℝ × ℝ).1 := by
    have h := congrArg Prod.fst ht
    simpa [SimpleFunc.pair_apply] using h
  have hSnd : g t = (c : ℝ × ℝ).2 := by
    have h := congrArg Prod.snd ht
    simpa [SimpleFunc.pair_apply] using h
  simpa [Real.norm_eq_abs, hFst, hSnd] using hBound t

/-- The spectral-integral map on simple functions is one-Lipschitz for the
uniform norm. -/
theorem pvmSimpleFuncSpectralIntegralOperator_sub_opNorm_le
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f g : SimpleFunc ℝ ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ t : ℝ, ‖f t - g t‖ ≤ C) :
    ‖pvmSimpleFuncSpectralIntegralOperator P f -
        pvmSimpleFuncSpectralIntegralOperator P g‖ ≤ C := by
  rw [← pvmSimpleFuncPairSpectralIntegralOperator_sub_eq P f g]
  exact pvmFiniteSimpleSpectralIntegralOperator_opNorm_le
    P
    (fun c : (f.pair g).range =>
      (c : ℝ × ℝ).1 - (c : ℝ × ℝ).2)
    (pvmSimpleFuncPairFiber f g)
    (pvmSimpleFuncPairFiber_pairwise_disjoint f g)
    (pvmSimpleFuncPairFiber_iUnion_eq_univ f g)
    C hC (pvmSimpleFuncPair_range_sub_abs_le f g C hBound)

/-- Uniform Cauchy convergence of a sequence of simple real functions. -/
def PVMSimpleFuncUniformCauchy
    (u : ℕ → SimpleFunc ℝ ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, N ≤ n →
      ∀ t : ℝ, ‖u m t - u n t‖ < ε

/-- A uniformly Cauchy simple-function sequence has a Cauchy sequence of PVM
spectral-integral operators in operator norm. -/
theorem pvmSimpleFuncSpectralIntegralOperator_cauchy_of_uniformCauchy
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (u : ℕ → SimpleFunc ℝ ℝ)
    (hu : PVMSimpleFuncUniformCauchy u) :
    CauchySeq
      (fun n => pvmSimpleFuncSpectralIntegralOperator P (u n)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨N, hN⟩ := hu (ε / 2) hε2
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [dist_eq_norm]
  have hOp :
      ‖pvmSimpleFuncSpectralIntegralOperator P (u m) -
          pvmSimpleFuncSpectralIntegralOperator P (u n)‖ ≤ ε / 2 :=
    pvmSimpleFuncSpectralIntegralOperator_sub_opNorm_le
      P (u m) (u n) (ε / 2) hε2.le
        (fun t => (hN m hm n hn t).le)
  exact hOp.trans_lt (half_lt_self hε)

/-- Canonical completion package produced directly from uniform Cauchy data. -/
noncomputable def pvmSimpleFuncOperatorCauchyApproximationOfUniformCauchy
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (u : ℕ → SimpleFunc ℝ ℝ)
    (hu : PVMSimpleFuncUniformCauchy u) :
    PVMSimpleFuncOperatorCauchyApproximation P where
  simple := u
  operator_cauchy :=
    pvmSimpleFuncSpectralIntegralOperator_cauchy_of_uniformCauchy P u hu

/-- The bounded operator obtained by completing a uniformly Cauchy sequence of
simple-function PVM spectral integrals. -/
noncomputable def pvmSimpleFuncCompletedOperatorOfUniformCauchy
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (u : ℕ → SimpleFunc ℝ ℝ)
    (hu : PVMSimpleFuncUniformCauchy u) : H →L[ℝ] H :=
  (pvmSimpleFuncOperatorCauchyApproximationOfUniformCauchy P u hu).completedOperator

/-- The simple-function PVM spectral integrals converge in operator norm to the
operator constructed from uniform Cauchy data. -/
theorem pvmSimpleFunc_tendsto_completedOperatorOfUniformCauchy
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (u : ℕ → SimpleFunc ℝ ℝ)
    (hu : PVMSimpleFuncUniformCauchy u) :
    Tendsto
      (fun n => pvmSimpleFuncSpectralIntegralOperator P (u n))
      atTop
      (𝓝 (pvmSimpleFuncCompletedOperatorOfUniformCauchy P u hu)) := by
  exact
    (pvmSimpleFuncOperatorCauchyApproximationOfUniformCauchy P u hu).
      tendsto_completedOperator

end

end MathlibAnalytic
end MGAP4D
