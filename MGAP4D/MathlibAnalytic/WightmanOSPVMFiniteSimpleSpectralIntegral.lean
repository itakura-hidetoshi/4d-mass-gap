import MGAP4D.MathlibAnalytic.WightmanOSPVMDisjointCompositionDerived
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped BigOperators InnerProductSpace

noncomputable section

/-- The union of a finite family of spectral carriers. -/
def pvmFiniteCarrierUnion
    {ι : Type} (I : Finset ι) (carrier : ι → Set ℝ) : Set ℝ :=
  ⋃ i ∈ I, carrier i

/-- A carrier is disjoint from the union of the other carriers in a finite
subfamily. -/
theorem pvmFiniteCarrierUnion_disjoint_of_pairwise
    {ι : Type} [DecidableEq ι]
    (carrier : ι → Set ℝ)
    (hPairwise : Pairwise (Function.onFun Disjoint carrier))
    {a : ι} {I : Finset ι} (ha : a ∉ I) :
    Disjoint (carrier a) (pvmFiniteCarrierUnion I carrier) := by
  rw [Set.disjoint_left]
  intro x hxa hxI
  simp only [pvmFiniteCarrierUnion, Set.mem_iUnion] at hxI
  rcases hxI with ⟨i, hi, hxi⟩
  have hai : a ≠ i := by
    intro h
    subst i
    exact ha hi
  exact Set.disjoint_left.mp (hPairwise hai) hxa hxi

/-- Inserting one index adds its carrier by set union. -/
theorem pvmFiniteCarrierUnion_insert
    {ι : Type} [DecidableEq ι]
    (carrier : ι → Set ℝ) (a : ι) (I : Finset ι) :
    pvmFiniteCarrierUnion (insert a I) carrier =
      carrier a ∪ pvmFiniteCarrierUnion I carrier := by
  ext x
  simp [pvmFiniteCarrierUnion]

/-- Finite disjoint additivity iterated over a finite family. -/
theorem orthogonalProjectionValuedSetFunction_projection_finiteCarrierUnion_eq_sum
    {H ι : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [DecidableEq ι]
    (P : OrthogonalProjectionValuedSetFunction H)
    (carrier : ι → Set ℝ)
    (hPairwise : Pairwise (Function.onFun Disjoint carrier))
    (I : Finset ι) (x : H) :
    P.projection (pvmFiniteCarrierUnion I carrier) x =
      ∑ i ∈ I, P.projection (carrier i) x := by
  induction I using Finset.induction_on with
  | empty =>
      simp [pvmFiniteCarrierUnion, P.empty_apply]
  | @insert a I ha ih =>
      have hDisjoint :
          Disjoint (carrier a) (pvmFiniteCarrierUnion I carrier) :=
        pvmFiniteCarrierUnion_disjoint_of_pairwise carrier hPairwise ha
      rw [pvmFiniteCarrierUnion_insert carrier a I]
      rw [P.disjoint_additive _ _ hDisjoint x, ih]
      simp [ha]

/-- A finite disjoint partition of the whole spectral line resolves the identity. -/
theorem orthogonalProjectionValuedSetFunction_projection_sum_eq_of_iUnion_eq_univ
    {H ι : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype ι]
    (P : OrthogonalProjectionValuedSetFunction H)
    (carrier : ι → Set ℝ)
    (hPairwise : Pairwise (Function.onFun Disjoint carrier))
    (hCover : (⋃ i, carrier i) = Set.univ)
    (x : H) :
    (∑ i : ι, P.projection (carrier i) x) = x := by
  classical
  have hUnion :
      pvmFiniteCarrierUnion (Finset.univ : Finset ι) carrier = Set.univ := by
    simpa [pvmFiniteCarrierUnion] using hCover
  calc
    (∑ i : ι, P.projection (carrier i) x) =
        P.projection (pvmFiniteCarrierUnion (Finset.univ : Finset ι) carrier) x :=
      (orthogonalProjectionValuedSetFunction_projection_finiteCarrierUnion_eq_sum
        P carrier hPairwise Finset.univ x).symm
    _ = P.projection Set.univ x := by rw [hUnion]
    _ = x := P.univ_apply x

/-- Disjoint spectral projections have zero real inner product. -/
theorem orthogonalProjectionValuedSetFunction_inner_projection_projection_eq_zero
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    {s t : Set ℝ} (hst : Disjoint s t) (x : H) :
    inner ℝ (P.projection s x) (P.projection t x) = 0 := by
  calc
    inner ℝ (P.projection s x) (P.projection t x) =
        inner ℝ x (P.projection s (P.projection t x)) :=
      P.selfAdjoint s x (P.projection t x)
    _ = inner ℝ x 0 := by
      rw [orthogonalProjectionValuedSetFunction_hasDisjointCompositionZero_of_projectionLaws
        P s t hst x]
    _ = 0 := by simp

/-- The finite simple spectral integral associated with a disjoint spectral
partition. -/
def pvmFiniteSimpleSpectralIntegral
    {H ι : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype ι]
    (P : OrthogonalProjectionValuedSetFunction H)
    (coefficients : ι → ℝ)
    (carrier : ι → Set ℝ)
    (x : H) : H :=
  ∑ i : ι, coefficients i • P.projection (carrier i) x

/-- Pythagoras for a finite simple PVM spectral integral. -/
theorem pvmFiniteSimpleSpectralIntegral_norm_sq
    {H ι : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype ι]
    (P : OrthogonalProjectionValuedSetFunction H)
    (coefficients : ι → ℝ)
    (carrier : ι → Set ℝ)
    (hPairwise : Pairwise (Function.onFun Disjoint carrier))
    (x : H) :
    ‖pvmFiniteSimpleSpectralIntegral P coefficients carrier x‖ ^ 2 =
      ∑ i : ι,
        coefficients i ^ 2 * ‖P.projection (carrier i) x‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  calc
    inner ℝ
        (pvmFiniteSimpleSpectralIntegral P coefficients carrier x)
        (pvmFiniteSimpleSpectralIntegral P coefficients carrier x) =
      ∑ i : ι, ∑ j : ι,
        coefficients i * coefficients j *
          inner ℝ (P.projection (carrier i) x)
            (P.projection (carrier j) x) := by
      simp only [pvmFiniteSimpleSpectralIntegral, sum_inner, inner_sum,
        real_inner_smul_left, real_inner_smul_right]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i : ι,
        coefficients i ^ 2 * ‖P.projection (carrier i) x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single i]
      · rw [real_inner_self_eq_norm_sq]
        ring
      · intro j hj hji
        have hij : i ≠ j := Ne.symm hji
        rw [orthogonalProjectionValuedSetFunction_inner_projection_projection_eq_zero
          P (hPairwise hij) x]
        ring
      · simp

/-- For a finite PVM partition, the squared projection norms sum to the squared
norm of the original vector. -/
theorem orthogonalProjectionValuedSetFunction_sum_projection_norm_sq_eq
    {H ι : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype ι]
    (P : OrthogonalProjectionValuedSetFunction H)
    (carrier : ι → Set ℝ)
    (hPairwise : Pairwise (Function.onFun Disjoint carrier))
    (hCover : (⋃ i, carrier i) = Set.univ)
    (x : H) :
    (∑ i : ι, ‖P.projection (carrier i) x‖ ^ 2) = ‖x‖ ^ 2 := by
  have hNorm :=
    pvmFiniteSimpleSpectralIntegral_norm_sq P (fun _ : ι => 1)
      carrier hPairwise x
  have hIntegral :
      pvmFiniteSimpleSpectralIntegral P (fun _ : ι => 1) carrier x = x := by
    unfold pvmFiniteSimpleSpectralIntegral
    simpa using
      orthogonalProjectionValuedSetFunction_projection_sum_eq_of_iUnion_eq_univ
        P carrier hPairwise hCover x
  rw [hIntegral] at hNorm
  simpa using hNorm.symm

/-- The finite simple spectral integral has the sharp sup-norm estimate. -/
theorem pvmFiniteSimpleSpectralIntegral_norm_le
    {H ι : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype ι]
    (P : OrthogonalProjectionValuedSetFunction H)
    (coefficients : ι → ℝ)
    (carrier : ι → Set ℝ)
    (hPairwise : Pairwise (Function.onFun Disjoint carrier))
    (hCover : (⋃ i, carrier i) = Set.univ)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ i : ι, |coefficients i| ≤ C)
    (x : H) :
    ‖pvmFiniteSimpleSpectralIntegral P coefficients carrier x‖ ≤
      C * ‖x‖ := by
  classical
  have hCoeffSq (i : ι) : coefficients i ^ 2 ≤ C ^ 2 := by
    have hSub : 0 ≤ C - |coefficients i| := sub_nonneg.mpr (hBound i)
    have hAdd : 0 ≤ C + |coefficients i| :=
      add_nonneg hC (abs_nonneg (coefficients i))
    have hProd : 0 ≤ (C - |coefficients i|) * (C + |coefficients i|) :=
      mul_nonneg hSub hAdd
    nlinarith [sq_abs (coefficients i)]
  have hSq :
      ‖pvmFiniteSimpleSpectralIntegral P coefficients carrier x‖ ^ 2 ≤
        C ^ 2 * ‖x‖ ^ 2 := by
    calc
      ‖pvmFiniteSimpleSpectralIntegral P coefficients carrier x‖ ^ 2 =
          ∑ i : ι,
            coefficients i ^ 2 * ‖P.projection (carrier i) x‖ ^ 2 :=
        pvmFiniteSimpleSpectralIntegral_norm_sq
          P coefficients carrier hPairwise x
      _ ≤ ∑ i : ι,
          C ^ 2 * ‖P.projection (carrier i) x‖ ^ 2 := by
        exact Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (hCoeffSq i)
            (sq_nonneg ‖P.projection (carrier i) x‖)
      _ = C ^ 2 *
          (∑ i : ι, ‖P.projection (carrier i) x‖ ^ 2) := by
        rw [Finset.mul_sum]
      _ = C ^ 2 * ‖x‖ ^ 2 := by
        rw [orthogonalProjectionValuedSetFunction_sum_projection_norm_sq_eq
          P carrier hPairwise hCover x]
  have hRight : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg x)
  have hSquareRight : (C * ‖x‖) ^ 2 = C ^ 2 * ‖x‖ ^ 2 := by ring
  rw [← hSquareRight] at hSq
  nlinarith [norm_nonneg
    (pvmFiniteSimpleSpectralIntegral P coefficients carrier x)]

/-- The finite simple spectral integral as a bounded operator. -/
def pvmFiniteSimpleSpectralIntegralOperator
    {H ι : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype ι]
    (P : OrthogonalProjectionValuedSetFunction H)
    (coefficients : ι → ℝ)
    (carrier : ι → Set ℝ) : H →L[ℝ] H :=
  ∑ i : ι, coefficients i • P.projection (carrier i)

@[simp] theorem pvmFiniteSimpleSpectralIntegralOperator_apply
    {H ι : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype ι]
    (P : OrthogonalProjectionValuedSetFunction H)
    (coefficients : ι → ℝ)
    (carrier : ι → Set ℝ)
    (x : H) :
    pvmFiniteSimpleSpectralIntegralOperator P coefficients carrier x =
      pvmFiniteSimpleSpectralIntegral P coefficients carrier x := by
  simp [pvmFiniteSimpleSpectralIntegralOperator,
    pvmFiniteSimpleSpectralIntegral]

/-- The operator norm of a finite simple spectral integral is bounded by the
supremum of its coefficients. -/
theorem pvmFiniteSimpleSpectralIntegralOperator_opNorm_le
    {H ι : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype ι]
    (P : OrthogonalProjectionValuedSetFunction H)
    (coefficients : ι → ℝ)
    (carrier : ι → Set ℝ)
    (hPairwise : Pairwise (Function.onFun Disjoint carrier))
    (hCover : (⋃ i, carrier i) = Set.univ)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ i : ι, |coefficients i| ≤ C) :
    ‖pvmFiniteSimpleSpectralIntegralOperator P coefficients carrier‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound hC
  intro x
  rw [pvmFiniteSimpleSpectralIntegralOperator_apply]
  exact pvmFiniteSimpleSpectralIntegral_norm_le
    P coefficients carrier hPairwise hCover C hC hBound x

end

end MathlibAnalytic
end MGAP4D
