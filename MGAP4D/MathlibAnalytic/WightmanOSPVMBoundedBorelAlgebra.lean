import MGAP4D.MathlibAnalytic.WightmanOSPVMBoundedBorelUniformApproximation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Filter Topology MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

/-- PVM bounded Borel functions are determined by their underlying function;
the remaining fields are propositions. -/
@[ext] theorem PVMBoundedBorelRealFunction.ext
    {F G : PVMBoundedBorelRealFunction}
    (h : F.toFun = G.toFun) : F = G := by
  cases F with
  | mk f hf hb =>
      cases G with
      | mk g hg gb =>
          cases h
          rfl

/-- A Mathlib simple real function regarded as a bounded Borel function for the
standalone PVM integral. -/
noncomputable def explicitBoundedBorelOfSimpleFunc
    (f : SimpleFunc ℝ ℝ) : PVMBoundedBorelRealFunction where
  toFun := f
  measurable_toFun := f.measurable
  bounded_toFun := by
    obtain ⟨C, hC⟩ := (f.map fun x : ℝ => ‖x‖).exists_forall_le
    refine ⟨C, ?_⟩
    intro t
    simpa [SimpleFunc.map_apply] using hC t

/-- Mapping one value in the common pair range produces a value in the range of
the mapped pair simple function. -/
def pvmSimpleFuncPairRangeMap
    (f g : SimpleFunc ℝ ℝ) (coefficient : ℝ × ℝ → ℝ)
    (c : (f.pair g).range) :
    ((f.pair g).map coefficient).range := by
  refine ⟨coefficient (c : ℝ × ℝ), ?_⟩
  rcases SimpleFunc.mem_range.mp c.property with ⟨t, ht⟩
  apply SimpleFunc.mem_range.mpr
  refine ⟨t, ?_⟩
  simpa [SimpleFunc.map_apply, ht]

@[simp] theorem pvmSimpleFuncPairRangeMap_val
    (f g : SimpleFunc ℝ ℝ) (coefficient : ℝ × ℝ → ℝ)
    (c : (f.pair g).range) :
    ((pvmSimpleFuncPairRangeMap f g coefficient c :
        ((f.pair g).map coefficient).range) : ℝ) =
      coefficient (c : ℝ × ℝ) :=
  rfl

/-- A fiber of a mapped pair simple function is the finite union of all common
pair fibers carrying that mapped coefficient. -/
theorem pvmSimpleFuncFiber_eq_pairFiberUnion_map
    (f g : SimpleFunc ℝ ℝ) (coefficient : ℝ × ℝ → ℝ)
    (a : ((f.pair g).map coefficient).range) :
    pvmSimpleFuncFiber ((f.pair g).map coefficient) a =
      pvmFiniteCarrierUnion
        (Finset.univ.filter
          (fun c : (f.pair g).range =>
            pvmSimpleFuncPairRangeMap f g coefficient c = a))
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
      simpa [c, pvmSimpleFuncPairRangeMap, pvmSimpleFuncFiber,
        SimpleFunc.map_apply] using hx
    · simp [pvmSimpleFuncPairFiber, c]
  · intro hx
    rw [pvmFiniteCarrierUnion] at hx
    rcases Set.mem_iUnion.mp hx with ⟨c, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hc, hxc⟩
    have hca : pvmSimpleFuncPairRangeMap f g coefficient c = a :=
      (Finset.mem_filter.mp hc).2
    have hPair : (f.pair g) x = (c : ℝ × ℝ) := by
      simpa [pvmSimpleFuncPairFiber] using hxc
    have hVal : coefficient (c : ℝ × ℝ) = (a : ℝ) := by
      exact congrArg Subtype.val hca
    simpa [pvmSimpleFuncFiber, SimpleFunc.map_apply, hPair, hVal]

/-- Projection onto a mapped coarse fiber is the sum of the projections onto its
common pair-fiber refinement. -/
theorem orthogonalProjectionValuedSetFunction_projection_simpleMapFiber_eq_sum_pair
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f g : SimpleFunc ℝ ℝ) (coefficient : ℝ × ℝ → ℝ)
    (a : ((f.pair g).map coefficient).range) (x : H) :
    P.projection
        (pvmSimpleFuncFiber ((f.pair g).map coefficient) a) x =
      ∑ c ∈ Finset.univ.filter
        (fun c : (f.pair g).range =>
          pvmSimpleFuncPairRangeMap f g coefficient c = a),
        P.projection (pvmSimpleFuncPairFiber f g c) x := by
  rw [pvmSimpleFuncFiber_eq_pairFiberUnion_map f g coefficient a]
  exact
    orthogonalProjectionValuedSetFunction_projection_finiteCarrierUnion_eq_sum
      P (pvmSimpleFuncPairFiber f g)
        (pvmSimpleFuncPairFiber_pairwise_disjoint f g)
        (Finset.univ.filter
          (fun c : (f.pair g).range =>
            pvmSimpleFuncPairRangeMap f g coefficient c = a)) x

/-- The common-refinement integral is unchanged when equal coefficients are
merged into the canonical fibers of the mapped simple function. -/
theorem pvmSimpleFuncPairSpectralIntegralOperator_eq_map
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f g : SimpleFunc ℝ ℝ) (coefficient : ℝ × ℝ → ℝ) :
    pvmSimpleFuncPairSpectralIntegralOperator P f g coefficient =
      pvmSimpleFuncSpectralIntegralOperator P
        ((f.pair g).map coefficient) := by
  ext x
  rw [pvmSimpleFuncPairSpectralIntegralOperator_apply,
    pvmSimpleFuncSpectralIntegralOperator_apply]
  unfold pvmFiniteSimpleSpectralIntegral
  symm
  calc
    (∑ a : ((f.pair g).map coefficient).range,
        (a : ℝ) •
          P.projection
            (pvmSimpleFuncFiber ((f.pair g).map coefficient) a) x) =
      ∑ a : ((f.pair g).map coefficient).range,
        (a : ℝ) •
          ∑ c ∈ Finset.univ.filter
            (fun c : (f.pair g).range =>
              pvmSimpleFuncPairRangeMap f g coefficient c = a),
            P.projection (pvmSimpleFuncPairFiber f g c) x := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [orthogonalProjectionValuedSetFunction_projection_simpleMapFiber_eq_sum_pair]
    _ = ∑ a : ((f.pair g).map coefficient).range,
        ∑ c ∈ Finset.univ.filter
          (fun c : (f.pair g).range =>
            pvmSimpleFuncPairRangeMap f g coefficient c = a),
          (a : ℝ) • P.projection (pvmSimpleFuncPairFiber f g c) x := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.smul_sum]
    _ = ∑ a : ((f.pair g).map coefficient).range,
        ∑ c ∈ Finset.univ.filter
          (fun c : (f.pair g).range =>
            pvmSimpleFuncPairRangeMap f g coefficient c = a),
          coefficient (c : ℝ × ℝ) •
            P.projection (pvmSimpleFuncPairFiber f g c) x := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro c hc
      have hca := (Finset.mem_filter.mp hc).2
      have hVal : coefficient (c : ℝ × ℝ) = (a : ℝ) := by
        exact congrArg Subtype.val hca
      rw [hVal]
    _ = ∑ c : (f.pair g).range,
        coefficient (c : ℝ × ℝ) •
          P.projection (pvmSimpleFuncPairFiber f g c) x := by
      simpa using
        (Finset.sum_fiberwise
          (s := (Finset.univ : Finset (f.pair g).range))
          (g := pvmSimpleFuncPairRangeMap f g coefficient)
          (f := fun c : (f.pair g).range =>
            coefficient (c : ℝ × ℝ) •
              P.projection (pvmSimpleFuncPairFiber f g c) x))

/-- Canonical simple-function PVM integration preserves subtraction. -/
theorem pvmSimpleFuncSpectralIntegralOperator_sub
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f g : SimpleFunc ℝ ℝ) :
    pvmSimpleFuncSpectralIntegralOperator P (f - g) =
      pvmSimpleFuncSpectralIntegralOperator P f -
        pvmSimpleFuncSpectralIntegralOperator P g := by
  have hSub :
      f - g = (f.pair g).map (fun p : ℝ × ℝ => p.1 - p.2) := by
    ext t
    rfl
  rw [hSub]
  rw [← pvmSimpleFuncPairSpectralIntegralOperator_eq_map]
  exact pvmSimpleFuncPairSpectralIntegralOperator_sub_eq P f g

/-- The zero simple function integrates to the zero operator. -/
theorem pvmSimpleFuncSpectralIntegralOperator_zero
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H) :
    pvmSimpleFuncSpectralIntegralOperator P (0 : SimpleFunc ℝ ℝ) = 0 := by
  simpa using
    (pvmSimpleFuncSpectralIntegralOperator_sub P
      (0 : SimpleFunc ℝ ℝ) (0 : SimpleFunc ℝ ℝ))

/-- The constant-one simple function integrates to the identity operator. -/
theorem pvmSimpleFuncSpectralIntegralOperator_one
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H) :
    pvmSimpleFuncSpectralIntegralOperator P (1 : SimpleFunc ℝ ℝ) =
      ContinuousLinearMap.id ℝ H := by
  ext x
  rw [pvmSimpleFuncSpectralIntegralOperator_apply]
  unfold pvmFiniteSimpleSpectralIntegral
  have hSum :=
    orthogonalProjectionValuedSetFunction_projection_sum_eq_of_iUnion_eq_univ
      P (pvmSimpleFuncFiber (1 : SimpleFunc ℝ ℝ))
        (pvmSimpleFuncFiber_pairwise_disjoint (1 : SimpleFunc ℝ ℝ))
        (pvmSimpleFuncFiber_iUnion_eq_univ (1 : SimpleFunc ℝ ℝ)) x
  calc
    (∑ c : (1 : SimpleFunc ℝ ℝ).range,
        (c : ℝ) • P.projection (pvmSimpleFuncFiber 1 c) x) =
      ∑ c : (1 : SimpleFunc ℝ ℝ).range,
        P.projection (pvmSimpleFuncFiber 1 c) x := by
      apply Finset.sum_congr rfl
      intro c hc
      have hcOne : (c : ℝ) = 1 := by
        rcases SimpleFunc.mem_range.mp c.property with ⟨t, ht⟩
        simpa using ht.symm
      simp [hcOne]
    _ = x := hSum

/-- The measurable indicator as a Mathlib simple real function. -/
noncomputable def pvmSimpleFuncIndicator
    (s : Set ℝ) (hs : MeasurableSet s) : SimpleFunc ℝ ℝ :=
  SimpleFunc.piecewise s hs (1 : SimpleFunc ℝ ℝ) 0

@[simp] theorem pvmSimpleFuncIndicator_apply
    (s : Set ℝ) (hs : MeasurableSet s) (t : ℝ) :
    pvmSimpleFuncIndicator s hs t =
      Set.indicator s (fun _ : ℝ => (1 : ℝ)) t := by
  classical
  rfl

/-- The PVM integral of a measurable simple indicator is its spectral
projection. -/
theorem pvmSimpleFuncSpectralIntegralOperator_indicator
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (s : Set ℝ) (hs : MeasurableSet s) :
    pvmSimpleFuncSpectralIntegralOperator P (pvmSimpleFuncIndicator s hs) =
      P.projection s := by
  classical
  by_cases hEmpty : s = ∅
  · subst s
    have hIndicator : pvmSimpleFuncIndicator ∅ MeasurableSet.empty = 0 := by
      ext t
      simp [pvmSimpleFuncIndicator]
    rw [hIndicator, pvmSimpleFuncSpectralIntegralOperator_zero]
    ext x
    simp [P.empty_apply]
  · by_cases hUniv : s = Set.univ
    · subst s
      have hIndicator :
          pvmSimpleFuncIndicator Set.univ MeasurableSet.univ = 1 := by
        ext t
        simp [pvmSimpleFuncIndicator]
      rw [hIndicator, pvmSimpleFuncSpectralIntegralOperator_one]
      ext x
      simp [P.univ_apply]
    · have hsNonempty : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
      let c1 : (pvmSimpleFuncIndicator s hs).range := by
        refine ⟨1, ?_⟩
        apply SimpleFunc.mem_range.mpr
        rcases hsNonempty with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        simp [pvmSimpleFuncIndicator, ht]
      ext x
      rw [pvmSimpleFuncSpectralIntegralOperator_apply]
      unfold pvmFiniteSimpleSpectralIntegral
      rw [Finset.sum_eq_single c1]
      · have hFiber :
            pvmSimpleFuncFiber (pvmSimpleFuncIndicator s hs) c1 = s := by
          ext t
          by_cases ht : t ∈ s <;>
            simp [pvmSimpleFuncFiber, pvmSimpleFuncIndicator, c1, ht]
        simp [c1, hFiber]
      · intro c hc hne
        have hcZero : (c : ℝ) = 0 := by
          rcases SimpleFunc.mem_range.mp c.property with ⟨t, ht⟩
          by_cases hts : t ∈ s
          · have hcOne : (c : ℝ) = 1 := by
              simpa [pvmSimpleFuncIndicator, hts] using ht.symm
            exfalso
            apply hne
            apply Subtype.ext
            simpa [c1] using hcOne
          · simpa [pvmSimpleFuncIndicator, hts] using ht.symm
        simp [hcZero]
      · simp

/-- A constant sequence gives an exact uniform simple approximation of a simple
function. -/
noncomputable def explicitBoundedBorelSimpleFuncUniformApproximation
    (f : SimpleFunc ℝ ℝ) :
    ExplicitBoundedBorelSimpleUniformApproximation
      (explicitBoundedBorelOfSimpleFunc f) where
  simple := fun _ => f
  uniform_tendsto := by
    intro ε hε
    refine ⟨0, ?_⟩
    intro n hn t
    simpa [explicitBoundedBorelOfSimpleFunc] using hε

/-- The completed bounded Borel integral agrees with simple functions. -/
theorem pvmBoundedBorelSpectralIntegralOperator_ofSimpleFunc
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f : SimpleFunc ℝ ℝ) :
    pvmBoundedBorelSpectralIntegralOperator P
        (explicitBoundedBorelOfSimpleFunc f) =
      pvmSimpleFuncSpectralIntegralOperator P f := by
  let A := explicitBoundedBorelSimpleFuncUniformApproximation f
  have hCompleted :
      A.completedOperator P = pvmSimpleFuncSpectralIntegralOperator P f := by
    apply tendsto_nhds_unique (A.tendsto_completedOperator P)
    have hConst :
        Tendsto
          (fun _ : ℕ => pvmSimpleFuncSpectralIntegralOperator P f)
          atTop (𝓝 (pvmSimpleFuncSpectralIntegralOperator P f)) :=
      tendsto_const_nhds
    simpa [A, explicitBoundedBorelSimpleFuncUniformApproximation] using hConst
  calc
    pvmBoundedBorelSpectralIntegralOperator P
        (explicitBoundedBorelOfSimpleFunc f) = A.completedOperator P :=
      (A.completedOperator_eq_canonical P).symm
    _ = pvmSimpleFuncSpectralIntegralOperator P f := hCompleted

/-- The completed bounded Borel spectral integral sends the constant-one
function to the identity operator. -/
theorem pvmBoundedBorelSpectralIntegralOperator_one
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H) :
    pvmBoundedBorelSpectralIntegralOperator P pvmBoundedBorelOne =
      ContinuousLinearMap.id ℝ H := by
  have hOne :
      pvmBoundedBorelOne =
        explicitBoundedBorelOfSimpleFunc (1 : SimpleFunc ℝ ℝ) := by
    apply PVMBoundedBorelRealFunction.ext
    funext t
    rfl
  rw [hOne, pvmBoundedBorelSpectralIntegralOperator_ofSimpleFunc,
    pvmSimpleFuncSpectralIntegralOperator_one]

/-- The completed bounded Borel spectral integral sends indicators to spectral
projections. -/
theorem pvmBoundedBorelSpectralIntegralOperator_indicator
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (s : Set ℝ) (hs : MeasurableSet s) :
    pvmBoundedBorelSpectralIntegralOperator P
        (pvmBoundedBorelIndicator s hs) =
      P.projection s := by
  have hIndicator :
      pvmBoundedBorelIndicator s hs =
        explicitBoundedBorelOfSimpleFunc (pvmSimpleFuncIndicator s hs) := by
    apply PVMBoundedBorelRealFunction.ext
    funext t
    rfl
  rw [hIndicator, pvmBoundedBorelSpectralIntegralOperator_ofSimpleFunc,
    pvmSimpleFuncSpectralIntegralOperator_indicator]

/-- Subtracting two uniform simple approximations gives a uniform approximation
of the pointwise difference. -/
noncomputable def explicitBoundedBorelSimpleUniformApproximationSub
    {F G : PVMBoundedBorelRealFunction}
    (A : ExplicitBoundedBorelSimpleUniformApproximation F)
    (B : ExplicitBoundedBorelSimpleUniformApproximation G) :
    ExplicitBoundedBorelSimpleUniformApproximation
      (pvmBoundedBorelSub F G) where
  simple := fun n => A.simple n - B.simple n
  uniform_tendsto := by
    intro ε hε
    have hε2 : 0 < ε / 2 := half_pos hε
    obtain ⟨NA, hNA⟩ := A.uniform_tendsto (ε / 2) hε2
    obtain ⟨NB, hNB⟩ := B.uniform_tendsto (ε / 2) hε2
    refine ⟨max NA NB, ?_⟩
    intro n hn t
    have hnA : NA ≤ n := le_trans (le_max_left NA NB) hn
    have hnB : NB ≤ n := le_trans (le_max_right NA NB) hn
    change ‖(A.simple n t - B.simple n t) -
      (F.toFun t - G.toFun t)‖ < ε
    have hTriangle :
        ‖(A.simple n t - B.simple n t) -
            (F.toFun t - G.toFun t)‖ ≤
          ‖A.simple n t - F.toFun t‖ +
            ‖B.simple n t - G.toFun t‖ := by
      calc
        ‖(A.simple n t - B.simple n t) -
            (F.toFun t - G.toFun t)‖ =
          ‖(A.simple n t - F.toFun t) -
            (B.simple n t - G.toFun t)‖ := by
              congr 1
              ring
        _ ≤ ‖A.simple n t - F.toFun t‖ +
            ‖B.simple n t - G.toFun t‖ := norm_sub_le _ _
    exact hTriangle.trans_lt <| by
      calc
        ‖A.simple n t - F.toFun t‖ +
            ‖B.simple n t - G.toFun t‖ < ε / 2 + ε / 2 :=
          add_lt_add (hNA n hnA t) (hNB n hnB t)
        _ = ε := by ring

/-- The completed bounded Borel spectral integral preserves subtraction. -/
theorem pvmBoundedBorelSpectralIntegralOperator_sub
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (F G : PVMBoundedBorelRealFunction) :
    pvmBoundedBorelSpectralIntegralOperator P
        (pvmBoundedBorelSub F G) =
      pvmBoundedBorelSpectralIntegralOperator P F -
        pvmBoundedBorelSpectralIntegralOperator P G := by
  let A := explicitBoundedBorelCanonicalSimpleUniformApproximation F
  let B := explicitBoundedBorelCanonicalSimpleUniformApproximation G
  let C := explicitBoundedBorelSimpleUniformApproximationSub A B
  have hTerm (n : ℕ) :
      pvmSimpleFuncSpectralIntegralOperator P (C.simple n) =
        pvmSimpleFuncSpectralIntegralOperator P (A.simple n) -
          pvmSimpleFuncSpectralIntegralOperator P (B.simple n) := by
    dsimp [C, explicitBoundedBorelSimpleUniformApproximationSub]
    exact pvmSimpleFuncSpectralIntegralOperator_sub
      P (A.simple n) (B.simple n)
  have hDifference :
      Tendsto
        (fun n => pvmSimpleFuncSpectralIntegralOperator P (C.simple n))
        atTop
        (𝓝 (A.completedOperator P - B.completedOperator P)) := by
    have hAB :=
      (A.tendsto_completedOperator P).sub (B.tendsto_completedOperator P)
    simpa only [hTerm] using hAB
  have hA :
      A.completedOperator P = pvmBoundedBorelSpectralIntegralOperator P F :=
    A.completedOperator_eq_canonical P
  have hB :
      B.completedOperator P = pvmBoundedBorelSpectralIntegralOperator P G :=
    B.completedOperator_eq_canonical P
  have hTarget :
      Tendsto
        (fun n => pvmSimpleFuncSpectralIntegralOperator P (C.simple n))
        atTop
        (𝓝 (pvmBoundedBorelSpectralIntegralOperator P F -
          pvmBoundedBorelSpectralIntegralOperator P G)) := by
    simpa only [hA, hB] using hDifference
  have hCompleted :
      C.completedOperator P =
        pvmBoundedBorelSpectralIntegralOperator P F -
          pvmBoundedBorelSpectralIntegralOperator P G :=
    tendsto_nhds_unique (C.tendsto_completedOperator P) hTarget
  calc
    pvmBoundedBorelSpectralIntegralOperator P
        (pvmBoundedBorelSub F G) = C.completedOperator P :=
      (C.completedOperator_eq_canonical P).symm
    _ = pvmBoundedBorelSpectralIntegralOperator P F -
        pvmBoundedBorelSpectralIntegralOperator P G := hCompleted

end

end MathlibAnalytic
end MGAP4D
