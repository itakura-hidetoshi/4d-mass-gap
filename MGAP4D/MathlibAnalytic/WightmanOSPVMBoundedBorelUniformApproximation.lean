import MGAP4D.MathlibAnalytic.WightmanOSPVMSimpleFuncUniformCauchy
import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianPVMLocalFunctionalCalculus
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Filter Topology MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

/-- Integer floor indices obtained by quantizing a bounded Borel real function at
mesh size `1 / (n + 1)`.  Boundedness makes the integer range finite. -/
noncomputable def explicitBoundedBorelFloorIndexSimpleFunc
    (F : ExplicitBoundedBorelRealFunction) (n : ℕ) : SimpleFunc ℝ ℤ where
  toFun := fun t => ⌊(((n : ℝ) + 1) * F.toFun t)⌋
  finite_range' := by
    obtain ⟨C, hC⟩ := F.bounded_toFun
    let K : ℝ := (n : ℝ) + 1
    have hK : 0 ≤ K := by positivity
    refine Set.Finite.subset
      (Set.finite_Icc (⌊-K * C⌋ : ℤ) (⌊K * C⌋ : ℤ)) ?_
    rintro z ⟨t, rfl⟩
    have hAbs : |F.toFun t| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC t
    have hLower : -C ≤ F.toFun t := (abs_le.mp hAbs).1
    have hUpper : F.toFun t ≤ C := (abs_le.mp hAbs).2
    constructor
    · exact Int.floor_mono (mul_le_mul_of_nonneg_left hLower hK)
    · exact Int.floor_mono (mul_le_mul_of_nonneg_left hUpper hK)
  measurableSet_fiber' := by
    intro z
    have hMeas :
        Measurable (fun t : ℝ => ⌊(((n : ℝ) + 1) * F.toFun t)⌋) :=
      (measurable_const.mul F.measurable_toFun).floor
    exact hMeas (measurableSet_singleton z)

/-- The canonical lower-grid simple approximation of a bounded Borel function. -/
noncomputable def explicitBoundedBorelSimpleApproximation
    (F : ExplicitBoundedBorelRealFunction) (n : ℕ) : SimpleFunc ℝ ℝ :=
  (explicitBoundedBorelFloorIndexSimpleFunc F n).map
    (fun z : ℤ => (z : ℝ) / ((n : ℝ) + 1))

@[simp] theorem explicitBoundedBorelSimpleApproximation_apply
    (F : ExplicitBoundedBorelRealFunction) (n : ℕ) (t : ℝ) :
    explicitBoundedBorelSimpleApproximation F n t =
      (⌊(((n : ℝ) + 1) * F.toFun t)⌋ : ℝ) / ((n : ℝ) + 1) :=
  rfl

/-- The lower-grid approximation error is strictly smaller than its mesh. -/
theorem explicitBoundedBorelSimpleApproximation_error_lt
    (F : ExplicitBoundedBorelRealFunction) (n : ℕ) (t : ℝ) :
    ‖explicitBoundedBorelSimpleApproximation F n t - F.toFun t‖ <
      1 / ((n : ℝ) + 1) := by
  let K : ℝ := (n : ℝ) + 1
  have hK : 0 < K := by positivity
  let z : ℤ := ⌊K * F.toFun t⌋
  have hzLe : (z : ℝ) ≤ K * F.toFun t := by
    dsimp [z]
    exact Int.floor_le _
  have hxLt : K * F.toFun t < (z : ℝ) + 1 := by
    dsimp [z]
    exact Int.lt_floor_add_one _
  have hApproxLe : (z : ℝ) / K ≤ F.toFun t := by
    apply (div_le_iff₀ hK).2
    simpa only [mul_comm] using hzLe
  have hError : F.toFun t - (z : ℝ) / K < 1 / K := by
    have hScaled : F.toFun t < ((z : ℝ) + 1) / K := by
      apply (lt_div_iff₀ hK).2
      simpa only [mul_comm] using hxLt
    calc
      F.toFun t - (z : ℝ) / K <
          ((z : ℝ) + 1) / K - (z : ℝ) / K :=
        sub_lt_sub_right hScaled _
      _ = 1 / K := by field_simp
  change ‖(z : ℝ) / K - F.toFun t‖ < 1 / K
  calc
    ‖(z : ℝ) / K - F.toFun t‖ = F.toFun t - (z : ℝ) / K := by
      rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hApproxLe)]
      ring
    _ < 1 / K := hError

/-- A sequence of simple functions converging uniformly to one explicit bounded
Borel function. -/
structure ExplicitBoundedBorelSimpleUniformApproximation
    (F : ExplicitBoundedBorelRealFunction) where
  simple : ℕ → SimpleFunc ℝ ℝ
  uniform_tendsto :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n, N ≤ n → ∀ t : ℝ,
        ‖simple n t - F.toFun t‖ < ε

/-- The floor-grid sequence is a concrete uniform simple approximation. -/
noncomputable def explicitBoundedBorelCanonicalSimpleUniformApproximation
    (F : ExplicitBoundedBorelRealFunction) :
    ExplicitBoundedBorelSimpleUniformApproximation F where
  simple := explicitBoundedBorelSimpleApproximation F
  uniform_tendsto := by
    intro ε hε
    have hRate :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hEventually :
        ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
      (tendsto_order.1 hRate).2 ε hε
    rcases (eventually_atTop.1 hEventually) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn t
    exact
      (explicitBoundedBorelSimpleApproximation_error_lt F n t).trans
        (hN n hn)

/-- Uniform convergence to one bounded Borel function implies the simple-function
sequence is uniformly Cauchy. -/
theorem ExplicitBoundedBorelSimpleUniformApproximation.uniformCauchy
    {F : ExplicitBoundedBorelRealFunction}
    (A : ExplicitBoundedBorelSimpleUniformApproximation F) :
    PVMSimpleFuncUniformCauchy A.simple := by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨N, hN⟩ := A.uniform_tendsto (ε / 2) hε2
  refine ⟨N, ?_⟩
  intro m hm n hn t
  calc
    ‖A.simple m t - A.simple n t‖ ≤
        ‖A.simple m t - F.toFun t‖ +
          ‖F.toFun t - A.simple n t‖ :=
      norm_sub_le _ _
    _ = ‖A.simple m t - F.toFun t‖ +
          ‖A.simple n t - F.toFun t‖ := by
      rw [norm_sub_rev]
    _ < ε / 2 + ε / 2 := add_lt_add (hN m hm t) (hN n hn t)
    _ = ε := by ring

/-- The completed PVM operator attached to any uniform simple approximation. -/
noncomputable def ExplicitBoundedBorelSimpleUniformApproximation.completedOperator
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {F : ExplicitBoundedBorelRealFunction}
    (P : OrthogonalProjectionValuedSetFunction H)
    (A : ExplicitBoundedBorelSimpleUniformApproximation F) : H →L[ℝ] H :=
  pvmSimpleFuncCompletedOperatorOfUniformCauchy P A.simple A.uniformCauchy

/-- The approximating simple-function PVM operators converge in operator norm to
the completed operator. -/
theorem ExplicitBoundedBorelSimpleUniformApproximation.tendsto_completedOperator
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {F : ExplicitBoundedBorelRealFunction}
    (P : OrthogonalProjectionValuedSetFunction H)
    (A : ExplicitBoundedBorelSimpleUniformApproximation F) :
    Tendsto
      (fun n => pvmSimpleFuncSpectralIntegralOperator P (A.simple n))
      atTop (𝓝 (A.completedOperator P)) := by
  exact pvmSimpleFunc_tendsto_completedOperatorOfUniformCauchy
    P A.simple A.uniformCauchy

/-- Uniform simple approximation is representation independent after operator
completion. -/
theorem explicitBoundedBorelSimpleUniformApproximation_completedOperator_eq
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {F : ExplicitBoundedBorelRealFunction}
    (P : OrthogonalProjectionValuedSetFunction H)
    (A B : ExplicitBoundedBorelSimpleUniformApproximation F) :
    A.completedOperator P = B.completedOperator P := by
  apply tendsto_nhds_unique A.tendsto_completedOperator
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨NA, hNA⟩ := A.uniform_tendsto (ε / 4) hε4
  obtain ⟨NB, hNB⟩ := B.uniform_tendsto (ε / 4) hε4
  obtain ⟨NO, hNO⟩ :=
    (Metric.tendsto_atTop.1 B.tendsto_completedOperator) (ε / 2) hε2
  refine ⟨max (max NA NB) NO, ?_⟩
  intro n hn
  have hnA : NA ≤ n := le_trans (le_max_left NA NB) (le_trans (le_max_left _ NO) hn)
  have hnB : NB ≤ n := le_trans (le_max_right NA NB) (le_trans (le_max_left _ NO) hn)
  have hnO : NO ≤ n := le_trans (le_max_right (max NA NB) NO) hn
  have hPoint : ∀ t : ℝ, ‖A.simple n t - B.simple n t‖ ≤ ε / 2 := by
    intro t
    calc
      ‖A.simple n t - B.simple n t‖ ≤
          ‖A.simple n t - F.toFun t‖ +
            ‖F.toFun t - B.simple n t‖ := norm_sub_le _ _
      _ = ‖A.simple n t - F.toFun t‖ +
            ‖B.simple n t - F.toFun t‖ := by rw [norm_sub_rev]
      _ < ε / 4 + ε / 4 := add_lt_add (hNA n hnA t) (hNB n hnB t)
      _ = ε / 2 := by ring
      _ ≤ ε / 2 := le_rfl
  have hOperators :
      ‖pvmSimpleFuncSpectralIntegralOperator P (A.simple n) -
          pvmSimpleFuncSpectralIntegralOperator P (B.simple n)‖ ≤ ε / 2 :=
    pvmSimpleFuncSpectralIntegralOperator_sub_opNorm_le
      P (A.simple n) (B.simple n) (ε / 2) hε2.le hPoint
  calc
    dist (pvmSimpleFuncSpectralIntegralOperator P (A.simple n))
        (B.completedOperator P) ≤
      dist (pvmSimpleFuncSpectralIntegralOperator P (A.simple n))
          (pvmSimpleFuncSpectralIntegralOperator P (B.simple n)) +
        dist (pvmSimpleFuncSpectralIntegralOperator P (B.simple n))
          (B.completedOperator P) := dist_triangle _ _ _
    _ = ‖pvmSimpleFuncSpectralIntegralOperator P (A.simple n) -
          pvmSimpleFuncSpectralIntegralOperator P (B.simple n)‖ +
        dist (pvmSimpleFuncSpectralIntegralOperator P (B.simple n))
          (B.completedOperator P) := by rw [dist_eq_norm]
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hOperators (hNO n hnO)
    _ = ε := by ring

/-- The canonical bounded Borel PVM spectral integral obtained by floor-grid
completion. -/
noncomputable def pvmBoundedBorelSpectralIntegralOperator
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (F : ExplicitBoundedBorelRealFunction) : H →L[ℝ] H :=
  (explicitBoundedBorelCanonicalSimpleUniformApproximation F).completedOperator P

/-- The canonical floor-grid simple integrals converge in operator norm to the
bounded Borel spectral integral. -/
theorem pvmSimpleFunc_tendsto_boundedBorelSpectralIntegralOperator
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (F : ExplicitBoundedBorelRealFunction) :
    Tendsto
      (fun n => pvmSimpleFuncSpectralIntegralOperator P
        (explicitBoundedBorelSimpleApproximation F n))
      atTop (𝓝 (pvmBoundedBorelSpectralIntegralOperator P F)) := by
  exact
    (explicitBoundedBorelCanonicalSimpleUniformApproximation F).tendsto_completedOperator P

/-- Every uniform simple approximation of the same bounded Borel function
completes to the canonical bounded Borel spectral integral. -/
theorem ExplicitBoundedBorelSimpleUniformApproximation.completedOperator_eq_canonical
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {F : ExplicitBoundedBorelRealFunction}
    (P : OrthogonalProjectionValuedSetFunction H)
    (A : ExplicitBoundedBorelSimpleUniformApproximation F) :
    A.completedOperator P = pvmBoundedBorelSpectralIntegralOperator P F := by
  exact explicitBoundedBorelSimpleUniformApproximation_completedOperator_eq
    P A (explicitBoundedBorelCanonicalSimpleUniformApproximation F)

end

end MathlibAnalytic
end MGAP4D
