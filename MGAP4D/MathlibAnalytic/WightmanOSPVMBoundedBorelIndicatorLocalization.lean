import MGAP4D.MathlibAnalytic.WightmanOSQuadraticPVMScalarTailContinuity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

/-- The basic PVM laws already imply that projections of disjoint spectral sets
compose to zero. -/
theorem orthogonalProjectionValuedSetFunction_disjoint_composition_zero_from_basic_laws_localization
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H) :
    P.HasDisjointCompositionZero := by
  intro s t hst x
  have hCross (z : H) :
      P.projection s (P.projection t z) +
          P.projection t (P.projection s z) = 0 := by
    have h := P.idempotent (s ∪ t) z
    rw [P.disjoint_additive s t hst (P.projection (s ∪ t) z),
      P.disjoint_additive s t hst z] at h
    simp only [map_add, P.idempotent] at h
    calc
      P.projection s (P.projection t z) +
          P.projection t (P.projection s z) =
          (P.projection s z + P.projection s (P.projection t z) +
              (P.projection t (P.projection s z) + P.projection t z)) -
            (P.projection s z + P.projection t z) := by abel
      _ = 0 := by rw [h, sub_self]
  have hPtPs (z : H) :
      P.projection t (P.projection s z) = 0 := by
    let q : H := P.projection t (P.projection s z)
    have hSum := hCross (P.projection s z)
    rw [P.idempotent s z] at hSum
    change P.projection s q + q = 0 at hSum
    have hInner :=
      congrArg (fun w : H => inner ℝ w (P.projection s z)) hSum
    simp only [inner_add_left, inner_zero_left] at hInner
    have hqInner :
        inner ℝ q (P.projection s z) = ‖q‖ ^ 2 := by
      calc
        inner ℝ q (P.projection s z) =
            inner ℝ (P.projection t q) (P.projection s z) := by
              rw [show P.projection t q = q by
                dsimp [q]
                exact P.idempotent t (P.projection s z)]
        _ = inner ℝ q (P.projection t (P.projection s z)) :=
          P.selfAdjoint t q (P.projection s z)
        _ = inner ℝ q q := by rfl
        _ = ‖q‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have hFirst :
        inner ℝ (P.projection s q) (P.projection s z) = ‖q‖ ^ 2 := by
      calc
        inner ℝ (P.projection s q) (P.projection s z) =
            inner ℝ q (P.projection s (P.projection s z)) :=
          P.selfAdjoint s q (P.projection s z)
        _ = inner ℝ q (P.projection s z) := by rw [P.idempotent s z]
        _ = ‖q‖ ^ 2 := hqInner
    rw [hFirst, hqInner] at hInner
    have hqNormSq : ‖q‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖q‖]
    have hqZero : q = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp hqNormSq)
    simpa [q] using hqZero
  have h := hCross x
  rw [hPtPs x, add_zero] at h
  exact h

/-- A projection onto a larger spectral set fixes vectors already projected onto
one of its subsets. -/
theorem orthogonalProjectionValuedSetFunction_projection_projection_eq_of_subset_apply
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    {u s : Set ℝ} (hus : u ⊆ s) (x : H) :
    P.projection s (P.projection u x) = P.projection u x := by
  have hsUnion : s = u ∪ (s \ u) := by
    ext y
    constructor
    · intro hys
      by_cases hyu : y ∈ u
      · exact Or.inl hyu
      · exact Or.inr ⟨hys, hyu⟩
    · rintro (hyu | hyDiff)
      · exact hus hyu
      · exact hyDiff.1
  have hDisjoint : Disjoint u (s \ u) := by
    rw [Set.disjoint_left]
    intro y hyu hyDiff
    exact hyDiff.2 hyu
  have hReverse : Disjoint (s \ u) u := hDisjoint.symm
  have hZero : P.projection (s \ u) (P.projection u x) = 0 :=
    orthogonalProjectionValuedSetFunction_disjoint_composition_zero_from_basic_laws_localization
      P (s \ u) u hReverse x
  rw [hsUnion, P.disjoint_additive u (s \ u) hDisjoint (P.projection u x),
    P.idempotent u x, hZero, add_zero]

/-- Canonical multiplicativity of the PVM projection family. -/
theorem orthogonalProjectionValuedSetFunction_projection_projection_eq_inter_apply
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (s t : Set ℝ) (x : H) :
    P.projection s (P.projection t x) = P.projection (s ∩ t) x := by
  have htUnion : t = (s ∩ t) ∪ (t \ s) := by
    ext y
    constructor
    · intro hyt
      by_cases hys : y ∈ s
      · exact Or.inl ⟨hys, hyt⟩
      · exact Or.inr ⟨hyt, hys⟩
    · rintro (hInter | hDiff)
      · exact hInter.2
      · exact hDiff.1
  have hDisjoint : Disjoint (s ∩ t) (t \ s) := by
    rw [Set.disjoint_left]
    intro y hInter hDiff
    exact hDiff.2 hInter.1
  have hTailDisjoint : Disjoint s (t \ s) := by
    rw [Set.disjoint_left]
    intro y hys hDiff
    exact hDiff.2 hys
  have hZero : P.projection s (P.projection (t \ s) x) = 0 :=
    orthogonalProjectionValuedSetFunction_disjoint_composition_zero_from_basic_laws_localization
      P s (t \ s) hTailDisjoint x
  calc
    P.projection s (P.projection t x) =
        P.projection s
          (P.projection ((s ∩ t) ∪ (t \ s)) x) :=
      congrArg (fun r : Set ℝ => P.projection s (P.projection r x)) htUnion
    _ = P.projection s
          (P.projection (s ∩ t) x + P.projection (t \ s) x) := by
      rw [P.disjoint_additive (s ∩ t) (t \ s) hDisjoint x]
    _ = P.projection s (P.projection (s ∩ t) x) +
          P.projection s (P.projection (t \ s) x) := by rw [map_add]
    _ = P.projection (s ∩ t) x + 0 := by
      rw [orthogonalProjectionValuedSetFunction_projection_projection_eq_of_subset_apply
        P Set.inter_subset_left x, hZero]
    _ = P.projection (s ∩ t) x := add_zero _

/-- Restriction of a Mathlib simple function to a measurable spectral set. -/
noncomputable def pvmSimpleFuncRestrict
    (s : Set ℝ) (hs : MeasurableSet s) (f : SimpleFunc ℝ ℝ) :
    SimpleFunc ℝ ℝ :=
  (f.pair (pvmSimpleFuncIndicator s hs)).map
    (fun p : ℝ × ℝ => p.1 * p.2)

@[simp] theorem pvmSimpleFuncRestrict_apply
    (s : Set ℝ) (hs : MeasurableSet s)
    (f : SimpleFunc ℝ ℝ) (energy : ℝ) :
    pvmSimpleFuncRestrict s hs f energy = Set.indicator s f energy := by
  classical
  change f energy * pvmSimpleFuncIndicator s hs energy =
    Set.indicator s f energy
  by_cases henergy : energy ∈ s <;>
    simp [pvmSimpleFuncIndicator_apply, henergy]

/-- Simple-function spectral integration localizes exactly under a measurable
indicator. -/
theorem pvmSimpleFuncSpectralIntegralOperator_restrict_apply
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (s : Set ℝ) (hs : MeasurableSet s)
    (f : SimpleFunc ℝ ℝ) (x : H) :
    pvmSimpleFuncSpectralIntegralOperator P
        (pvmSimpleFuncRestrict s hs f) x =
      pvmSimpleFuncSpectralIntegralOperator P f (P.projection s x) := by
  classical
  let indicator := pvmSimpleFuncIndicator s hs
  have hMap :
      pvmSimpleFuncSpectralIntegralOperator P
          (pvmSimpleFuncRestrict s hs f) =
        pvmSimpleFuncPairSpectralIntegralOperator P f indicator
          (fun p : ℝ × ℝ => p.1 * p.2) := by
    dsimp [pvmSimpleFuncRestrict, indicator]
    exact (pvmSimpleFuncPairSpectralIntegralOperator_eq_map
      P f (pvmSimpleFuncIndicator s hs)
        (fun p : ℝ × ℝ => p.1 * p.2)).symm
  rw [hMap]
  rw [← pvmSimpleFuncPairSpectralIntegralOperator_fst_eq P f indicator]
  rw [pvmSimpleFuncPairSpectralIntegralOperator_apply,
    pvmSimpleFuncPairSpectralIntegralOperator_apply]
  apply Finset.sum_congr rfl
  intro c hc
  let carrier : Set ℝ := pvmSimpleFuncPairFiber f indicator c
  have hProjection :
      P.projection carrier (P.projection s x) =
        P.projection (carrier ∩ s) x :=
    orthogonalProjectionValuedSetFunction_projection_projection_eq_inter_apply
      P carrier s x
  rw [hProjection]
  rcases SimpleFunc.mem_range.mp c.property with ⟨energy, henergy⟩
  have hSnd : indicator energy = (c : ℝ × ℝ).2 := by
    have h := congrArg Prod.snd henergy
    simpa [SimpleFunc.pair_apply] using h
  by_cases henergyS : energy ∈ s
  · have hcOne : (c : ℝ × ℝ).2 = 1 := by
      have hi : indicator energy = 1 := by
        simp [indicator, pvmSimpleFuncIndicator, henergyS]
      exact hSnd.symm.trans hi
    have hCarrierSubset : carrier ⊆ s := by
      intro y hy
      have hPairY : (f.pair indicator) y = (c : ℝ × ℝ) := by
        simpa [carrier, pvmSimpleFuncPairFiber] using hy
      have hSndY : indicator y = (c : ℝ × ℝ).2 := by
        have h := congrArg Prod.snd hPairY
        simpa [SimpleFunc.pair_apply] using h
      by_contra hyS
      have hiZero : indicator y = 0 := by
        simp [indicator, pvmSimpleFuncIndicator, hyS]
      rw [hSndY, hcOne] at hiZero
      norm_num at hiZero
    have hInter : carrier ∩ s = carrier :=
      Set.inter_eq_left.mpr hCarrierSubset
    rw [hcOne, mul_one, hInter]
  · have hcZero : (c : ℝ × ℝ).2 = 0 := by
      have hi : indicator energy = 0 := by
        simp [indicator, pvmSimpleFuncIndicator, henergyS]
      exact hSnd.symm.trans hi
    have hInter : carrier ∩ s = ∅ := by
      ext y
      constructor
      · intro hy
        have hPairY : (f.pair indicator) y = (c : ℝ × ℝ) := by
          simpa [carrier, pvmSimpleFuncPairFiber] using hy.1
        have hSndY : indicator y = (c : ℝ × ℝ).2 := by
          have h := congrArg Prod.snd hPairY
          simpa [SimpleFunc.pair_apply] using h
        have hiOne : indicator y = 1 := by
          simp [indicator, pvmSimpleFuncIndicator, hy.2]
        rw [hSndY, hcZero] at hiOne
        norm_num at hiOne
      · intro hy
        simpa using hy
    simp [hcZero, hInter, P.empty_apply]

/-- Operator-norm convergence of simple PVM integrals implies convergence after
application to any fixed Hilbert vector. -/
theorem ExplicitBoundedBorelSimpleUniformApproximation.tendsto_completedOperator_apply
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {F : PVMBoundedBorelRealFunction}
    (A : ExplicitBoundedBorelSimpleUniformApproximation F)
    (P : OrthogonalProjectionValuedSetFunction H) (x : H) :
    Tendsto
      (fun n => pvmSimpleFuncSpectralIntegralOperator P (A.simple n) x)
      atTop (𝓝 (A.completedOperator P x)) := by
  refine (Metric.tendsto_nhds).2 ?_
  intro ε hε
  by_cases hx : x = 0
  · subst x
    filter_upwards [] with n
    simpa using hε
  · have hxNorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hδ : 0 < (ε / 2) / ‖x‖ := div_pos (half_pos hε) hxNorm
    have hEventuallyOperator :
        ∀ᶠ n : ℕ in atTop,
          dist
            (pvmSimpleFuncSpectralIntegralOperator P (A.simple n))
            (A.completedOperator P) < (ε / 2) / ‖x‖ :=
      Metric.tendsto_nhds.1 (A.tendsto_completedOperator P)
        ((ε / 2) / ‖x‖) hδ
    filter_upwards [hEventuallyOperator] with n hn
    rw [dist_eq_norm]
    change
      ‖(pvmSimpleFuncSpectralIntegralOperator P (A.simple n) -
          A.completedOperator P) x‖ < ε
    have hOperator :
        ‖pvmSimpleFuncSpectralIntegralOperator P (A.simple n) -
            A.completedOperator P‖ < (ε / 2) / ‖x‖ := by
      simpa [dist_eq_norm] using hn
    calc
      ‖(pvmSimpleFuncSpectralIntegralOperator P (A.simple n) -
          A.completedOperator P) x‖ ≤
          ‖pvmSimpleFuncSpectralIntegralOperator P (A.simple n) -
            A.completedOperator P‖ * ‖x‖ :=
        (pvmSimpleFuncSpectralIntegralOperator P (A.simple n) -
          A.completedOperator P).le_opNorm x
      _ < ((ε / 2) / ‖x‖) * ‖x‖ :=
        mul_lt_mul_of_pos_right hOperator hxNorm
      _ = ε / 2 := by field_simp [hxNorm.ne']
      _ < ε := half_lt_self hε

/-- Restricting every simple approximant gives a uniform simple approximation
of the restricted bounded Borel multiplier. -/
noncomputable def explicitBoundedBorelSimpleUniformApproximationRestrict
    {F : PVMBoundedBorelRealFunction}
    (A : ExplicitBoundedBorelSimpleUniformApproximation F)
    (s : Set ℝ) (hs : MeasurableSet s) :
    ExplicitBoundedBorelSimpleUniformApproximation
      (pvmBoundedBorelRestrict s hs F) where
  simple := fun n => pvmSimpleFuncRestrict s hs (A.simple n)
  uniform_tendsto := by
    intro ε hε
    obtain ⟨N, hN⟩ := A.uniform_tendsto ε hε
    refine ⟨N, ?_⟩
    intro n hn energy
    rw [pvmSimpleFuncRestrict_apply]
    by_cases henergy : energy ∈ s
    · simpa [pvmBoundedBorelRestrict, henergy] using hN n hn energy
    · simpa [pvmBoundedBorelRestrict, henergy] using hε

/-- Completed bounded-Borel PVM integration commutes with restriction to a
measurable spectral set. -/
theorem pvmBoundedBorelSpectralIntegralOperator_restrict_apply
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (s : Set ℝ) (hs : MeasurableSet s)
    (F : PVMBoundedBorelRealFunction) (x : H) :
    pvmBoundedBorelSpectralIntegralOperator P
        (pvmBoundedBorelRestrict s hs F) x =
      pvmBoundedBorelSpectralIntegralOperator P F (P.projection s x) := by
  let A := explicitBoundedBorelCanonicalSimpleUniformApproximation F
  let B := explicitBoundedBorelSimpleUniformApproximationRestrict A s hs
  have hB := B.tendsto_completedOperator_apply P x
  have hA := A.tendsto_completedOperator_apply P (P.projection s x)
  have hTerm : ∀ n : ℕ,
      pvmSimpleFuncSpectralIntegralOperator P (B.simple n) x =
        pvmSimpleFuncSpectralIntegralOperator P (A.simple n)
          (P.projection s x) := by
    intro n
    dsimp [B, explicitBoundedBorelSimpleUniformApproximationRestrict]
    exact pvmSimpleFuncSpectralIntegralOperator_restrict_apply
      P s hs (A.simple n) x
  have hCompleted :
      B.completedOperator P x = A.completedOperator P (P.projection s x) :=
    tendsto_nhds_unique hB (by simpa only [hTerm] using hA)
  rw [B.completedOperator_eq_canonical P,
    A.completedOperator_eq_canonical P] at hCompleted
  exact hCompleted

/-- The zero bounded Borel multiplier. -/
def pvmBoundedBorelZero : PVMBoundedBorelRealFunction where
  toFun := fun _ => 0
  measurable_toFun := measurable_const
  bounded_toFun := ⟨0, by intro energy; simp⟩

/-- The completed PVM integral of the zero multiplier is the zero operator. -/
theorem pvmBoundedBorelSpectralIntegralOperator_zero
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H) :
    pvmBoundedBorelSpectralIntegralOperator P pvmBoundedBorelZero = 0 := by
  have hZero :
      pvmBoundedBorelZero =
        explicitBoundedBorelOfSimpleFunc (0 : SimpleFunc ℝ ℝ) := by
    apply PVMBoundedBorelRealFunction.ext
    funext energy
    rfl
  rw [hZero, pvmBoundedBorelSpectralIntegralOperator_ofSimpleFunc,
    pvmSimpleFuncSpectralIntegralOperator_zero]

/-- Uniformly bounded multipliers have integrated restrictions controlled by the
corresponding spectral projection tail. -/
theorem pvmBoundedBorelSpectralIntegralOperator_restrict_norm_le
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (s : Set ℝ) (hs : MeasurableSet s)
    (F : PVMBoundedBorelRealFunction)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ energy : ℝ, ‖F.toFun energy‖ ≤ C)
    (x : H) :
    ‖pvmBoundedBorelSpectralIntegralOperator P
        (pvmBoundedBorelRestrict s hs F) x‖ ≤
      C * ‖P.projection s x‖ := by
  rw [pvmBoundedBorelSpectralIntegralOperator_restrict_apply]
  have hOperator :
      ‖pvmBoundedBorelSpectralIntegralOperator P F‖ ≤ C := by
    have hDifference :=
      pvmBoundedBorelSpectralIntegralOperator_sub_opNorm_le
        P F pvmBoundedBorelZero C hC (by
          intro energy
          simpa [pvmBoundedBorelZero] using hBound energy)
    simpa [pvmBoundedBorelSpectralIntegralOperator_zero P] using hDifference
  calc
    ‖pvmBoundedBorelSpectralIntegralOperator P F (P.projection s x)‖ ≤
        ‖pvmBoundedBorelSpectralIntegralOperator P F‖ *
          ‖P.projection s x‖ :=
      (pvmBoundedBorelSpectralIntegralOperator P F).le_opNorm
        (P.projection s x)
    _ ≤ C * ‖P.projection s x‖ :=
      mul_le_mul_of_nonneg_right hOperator (norm_nonneg _)

/-- The actual scalar PVM tail theorem therefore makes every uniformly bounded
completed spectral multiplier tail small at a fixed Hilbert vector. -/
theorem quadraticPVM_boundedBorelIntegral_natEnergyTail_eventually_small
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (F : PVMBoundedBorelRealFunction)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ energy : ℝ, ‖F.toFun energy‖ ≤ C)
    (ψ : M.H) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖pvmBoundedBorelSpectralIntegralOperator M.spectralPVM
          (pvmBoundedBorelRestrict
            (pvmNatEnergyTail n)
            (measurableSet_pvmNatEnergyTail n)
            F) ψ‖ < ε := by
  have hCOne : 0 < C + 1 := by linarith
  have hδ : 0 < ε / (C + 1) := div_pos hε hCOne
  filter_upwards
    [quadraticPVM_projection_natEnergyTail_eventually_small
      A ψ hδ] with n hn
  have hIntegral :=
    pvmBoundedBorelSpectralIntegralOperator_restrict_norm_le
      M.spectralPVM (pvmNatEnergyTail n)
      (measurableSet_pvmNatEnergyTail n) F C hC hBound ψ
  apply hIntegral.trans_lt
  calc
    C * ‖M.spectralPVM.projection (pvmNatEnergyTail n) ψ‖ ≤
        (C + 1) * ‖M.spectralPVM.projection (pvmNatEnergyTail n) ψ‖ := by
      gcongr
      linarith
    _ < (C + 1) * (ε / (C + 1)) :=
      mul_lt_mul_of_pos_left hn hCOne
    _ = ε := by field_simp [hCOne.ne']

end

end MathlibAnalytic
end MGAP4D
