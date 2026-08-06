import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelStrictFiniteResponseAsymptotic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Finite stationary response of one target envelope to an arbitrary declared
coordinate-variation profile.  The random-scan operator is used only as an
exact stationary comparison device. -/
def finiteInfluenceKernelObservableResponse
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (sourceEnvelope variation : ι → ℝ)
    (iterations : ℕ) : ℝ :=
  finiteInfluenceKernelPartialSource
      K sourceEnvelope variation iterations +
    2 * finiteProductVariationTotal
      (finiteInfluenceKernelRandomScanVariationIterate
        K variation iterations)

/-- Matrix entry obtained by applying the finite stationary response to the
unit singleton variation at one input coordinate. -/
def finiteInfluenceKernelObservableResponseEntry
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (sourceEnvelope : ι → ℝ)
    (iterations : ℕ)
    (source : ι) : ℝ :=
  finiteInfluenceKernelObservableResponse
    K sourceEnvelope
      (finiteInfluenceKernelSingletonVariation 1 source)
      iterations

/-- Every profile is exactly the finite superposition of its coordinatewise
singleton profiles. -/
theorem finiteInfluenceKernelSingletonVariation_sum_weighted
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (variation : ι → ℝ)
    (coordinate : ι) :
    (∑ source : ι,
      finiteInfluenceKernelSingletonVariation
        (variation source) source coordinate) =
      variation coordinate := by
  classical
  rw [Finset.sum_eq_single coordinate]
  · simp [finiteInfluenceKernelSingletonVariation]
  · intro source _hsource hNe
    simp [finiteInfluenceKernelSingletonVariation, Ne.symm hNe]
  · intro hCoordinate
    exact False.elim (hCoordinate (Finset.mem_univ coordinate))

/-- Kernel random-scan updating is homogeneous. -/
theorem finiteInfluenceKernelRandomScanUpdatedVariation_scale
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (c : ℝ)
    (variation : ι → ℝ)
    (source : ι) :
    finiteInfluenceKernelRandomScanUpdatedVariation
        K (fun e => c * variation e) source =
      c * finiteInfluenceKernelRandomScanUpdatedVariation
        K variation source := by
  unfold finiteInfluenceKernelRandomScanUpdatedVariation
  have hPoint (target : ι) :
      finiteInfluenceKernelUpdatedVariation
          K (fun e => c * variation e) target source =
        c * finiteInfluenceKernelUpdatedVariation
          K variation target source := by
    by_cases hEq : source = target
    · simp [finiteInfluenceKernelUpdatedVariation, hEq]
    · simp only [finiteInfluenceKernelUpdatedVariation, hEq, if_false]
      ring
  calc
    (Fintype.card ι : ℝ)⁻¹ *
        ∑ target : ι,
          finiteInfluenceKernelUpdatedVariation
            K (fun e => c * variation e) target source =
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ target : ι,
          c * finiteInfluenceKernelUpdatedVariation
            K variation target source := by
      congr 1
      apply Finset.sum_congr rfl
      intro target _htarget
      exact hPoint target
    _ = c * ((Fintype.card ι : ℝ)⁻¹ *
        ∑ target : ι,
          finiteInfluenceKernelUpdatedVariation
            K variation target source) := by
      rw [← Finset.mul_sum]
      ring

/-- Every finite kernel random-scan iterate is homogeneous. -/
theorem finiteInfluenceKernelRandomScanVariationIterate_scale
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (c : ℝ)
    (variation : ι → ℝ)
    (iterations : ℕ)
    (source : ι) :
    finiteInfluenceKernelRandomScanVariationIterate
        K (fun e => c * variation e) iterations source =
      c * finiteInfluenceKernelRandomScanVariationIterate
        K variation iterations source := by
  induction iterations generalizing source with
  | zero => rfl
  | succ n ih =>
      rw [finiteInfluenceKernelRandomScanVariationIterate_succ,
        finiteInfluenceKernelRandomScanVariationIterate_succ]
      calc
        finiteInfluenceKernelRandomScanUpdatedVariation K
            (finiteInfluenceKernelRandomScanVariationIterate
              K (fun e => c * variation e) n) source =
          finiteInfluenceKernelRandomScanUpdatedVariation K
            (fun e => c *
              finiteInfluenceKernelRandomScanVariationIterate
                K variation n e) source := by
            apply congrArg
              (fun profile : ι → ℝ =>
                finiteInfluenceKernelRandomScanUpdatedVariation
                  K profile source)
            funext e
            exact ih e
        _ = c * finiteInfluenceKernelRandomScanUpdatedVariation K
            (finiteInfluenceKernelRandomScanVariationIterate
              K variation n) source :=
          finiteInfluenceKernelRandomScanUpdatedVariation_scale
            K c _ source

/-- Kernel source pairing is homogeneous in the variation profile. -/
theorem finiteInfluenceKernelSourceError_scale
    {ι : Type}
    [Fintype ι]
    (c : ℝ)
    (sourceEnvelope variation : ι → ℝ) :
    finiteInfluenceKernelSourceError sourceEnvelope
        (fun e => c * variation e) =
      c * finiteInfluenceKernelSourceError sourceEnvelope variation := by
  unfold finiteInfluenceKernelSourceError
  calc
    (Fintype.card ι : ℝ)⁻¹ *
        ∑ target : ι,
          sourceEnvelope target * (c * variation target) =
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ target : ι,
          c * (sourceEnvelope target * variation target) := by
      congr 1
      apply Finset.sum_congr rfl
      intro target _htarget
      ring
    _ = c * ((Fintype.card ι : ℝ)⁻¹ *
        ∑ target : ι,
          sourceEnvelope target * variation target) := by
      rw [← Finset.mul_sum]
      ring

/-- Accumulated kernel source response is homogeneous. -/
theorem finiteInfluenceKernelPartialSource_scale
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (c : ℝ)
    (sourceEnvelope variation : ι → ℝ)
    (iterations : ℕ) :
    finiteInfluenceKernelPartialSource K sourceEnvelope
        (fun e => c * variation e) iterations =
      c * finiteInfluenceKernelPartialSource
        K sourceEnvelope variation iterations := by
  induction iterations with
  | zero => simp
  | succ n ih =>
      rw [finiteInfluenceKernelPartialSource_succ,
        finiteInfluenceKernelPartialSource_succ, ih]
      rw [show
        finiteInfluenceKernelRandomScanVariationIterate
            K (fun e => c * variation e) n =
          fun e => c *
            finiteInfluenceKernelRandomScanVariationIterate
              K variation n e by
        funext e
        exact finiteInfluenceKernelRandomScanVariationIterate_scale
          K c variation n e]
      rw [finiteInfluenceKernelSourceError_scale]
      ring

/-- Finite total profile mass is homogeneous. -/
theorem finiteProductVariationTotal_scale
    {ι : Type}
    [Fintype ι]
    (c : ℝ)
    (variation : ι → ℝ) :
    finiteProductVariationTotal (fun e => c * variation e) =
      c * finiteProductVariationTotal variation := by
  unfold finiteProductVariationTotal
  rw [← Finset.mul_sum]

/-- The finite observable response is homogeneous in its variation profile. -/
theorem finiteInfluenceKernelObservableResponse_scale
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (c : ℝ)
    (sourceEnvelope variation : ι → ℝ)
    (iterations : ℕ) :
    finiteInfluenceKernelObservableResponse K sourceEnvelope
        (fun e => c * variation e) iterations =
      c * finiteInfluenceKernelObservableResponse
        K sourceEnvelope variation iterations := by
  unfold finiteInfluenceKernelObservableResponse
  rw [finiteInfluenceKernelPartialSource_scale]
  rw [show
    finiteInfluenceKernelRandomScanVariationIterate
        K (fun e => c * variation e) iterations =
      fun e => c *
        finiteInfluenceKernelRandomScanVariationIterate
          K variation iterations e by
    funext e
    exact finiteInfluenceKernelRandomScanVariationIterate_scale
      K c variation iterations e]
  rw [finiteProductVariationTotal_scale]
  ring

/-- Kernel source pairing distributes over a finite superposition. -/
theorem finiteInfluenceKernelSourceError_sum
    {ι κ : Type}
    [Fintype ι]
    [Fintype κ]
    (sourceEnvelope : ι → ℝ)
    (family : κ → ι → ℝ) :
    finiteInfluenceKernelSourceError sourceEnvelope
        (fun e => ∑ k : κ, family k e) =
      ∑ k : κ,
        finiteInfluenceKernelSourceError sourceEnvelope (family k) := by
  unfold finiteInfluenceKernelSourceError
  calc
    (Fintype.card ι : ℝ)⁻¹ *
        ∑ target : ι,
          sourceEnvelope target *
            (∑ k : κ, family k target) =
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ target : ι, ∑ k : κ,
          sourceEnvelope target * family k target := by
      congr 1
      apply Finset.sum_congr rfl
      intro target _htarget
      rw [Finset.mul_sum]
    _ = (Fintype.card ι : ℝ)⁻¹ *
        ∑ k : κ, ∑ target : ι,
          sourceEnvelope target * family k target := by
      rw [Finset.sum_comm]
    _ = ∑ k : κ,
        (Fintype.card ι : ℝ)⁻¹ *
          ∑ target : ι,
            sourceEnvelope target * family k target := by
      rw [Finset.mul_sum]

/-- Accumulated kernel source response distributes over finite
superpositions. -/
theorem finiteInfluenceKernelPartialSource_sum
    {ι κ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype κ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (sourceEnvelope : ι → ℝ)
    (family : κ → ι → ℝ)
    (iterations : ℕ) :
    finiteInfluenceKernelPartialSource K sourceEnvelope
        (fun e => ∑ k : κ, family k e) iterations =
      ∑ k : κ,
        finiteInfluenceKernelPartialSource
          K sourceEnvelope (family k) iterations := by
  induction iterations with
  | zero => simp
  | succ n ih =>
      rw [finiteInfluenceKernelPartialSource_succ, ih]
      rw [show
        finiteInfluenceKernelRandomScanVariationIterate K
            (fun e => ∑ k : κ, family k e) n =
          fun e => ∑ k : κ,
            finiteInfluenceKernelRandomScanVariationIterate
              K (family k) n e by
        funext e
        exact finiteInfluenceKernelRandomScanVariationIterate_sum
          K family n e]
      rw [finiteInfluenceKernelSourceError_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [finiteInfluenceKernelPartialSource_succ]

/-- Total profile mass distributes over finite superpositions. -/
theorem finiteProductVariationTotal_sum
    {ι κ : Type}
    [Fintype ι]
    [Fintype κ]
    (family : κ → ι → ℝ) :
    finiteProductVariationTotal (fun e => ∑ k : κ, family k e) =
      ∑ k : κ, finiteProductVariationTotal (family k) := by
  unfold finiteProductVariationTotal
  rw [Finset.sum_comm]

/-- The finite observable response distributes over finite superpositions. -/
theorem finiteInfluenceKernelObservableResponse_sum
    {ι κ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype κ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (sourceEnvelope : ι → ℝ)
    (family : κ → ι → ℝ)
    (iterations : ℕ) :
    finiteInfluenceKernelObservableResponse K sourceEnvelope
        (fun e => ∑ k : κ, family k e) iterations =
      ∑ k : κ,
        finiteInfluenceKernelObservableResponse
          K sourceEnvelope (family k) iterations := by
  unfold finiteInfluenceKernelObservableResponse
  rw [finiteInfluenceKernelPartialSource_sum]
  rw [show
    finiteInfluenceKernelRandomScanVariationIterate K
        (fun e => ∑ k : κ, family k e) iterations =
      fun e => ∑ k : κ,
        finiteInfluenceKernelRandomScanVariationIterate
          K (family k) iterations e by
    funext e
    exact finiteInfluenceKernelRandomScanVariationIterate_sum
      K family iterations e]
  rw [finiteProductVariationTotal_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]

/-- Exact response-matrix expansion of an arbitrary finite coordinate profile. -/
theorem finiteInfluenceKernelObservableResponse_eq_matrix_mul
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (sourceEnvelope variation : ι → ℝ)
    (iterations : ℕ) :
    finiteInfluenceKernelObservableResponse
        K sourceEnvelope variation iterations =
      ∑ source : ι,
        finiteInfluenceKernelObservableResponseEntry
          K sourceEnvelope iterations source * variation source := by
  let family : ι → ι → ℝ := fun source =>
    finiteInfluenceKernelSingletonVariation
      (variation source) source
  have hVariation :
      (fun e => ∑ source : ι, family source e) = variation := by
    funext e
    exact finiteInfluenceKernelSingletonVariation_sum_weighted variation e
  rw [← hVariation,
    finiteInfluenceKernelObservableResponse_sum K sourceEnvelope family iterations]
  apply Finset.sum_congr rfl
  intro source _hsource
  have hSingleton :
      family source =
        fun e => variation source *
          finiteInfluenceKernelSingletonVariation 1 source e := by
    funext e
    unfold family finiteInfluenceKernelSingletonVariation
    split <;> ring
  rw [hSingleton,
    finiteInfluenceKernelObservableResponse_scale]
  unfold finiteInfluenceKernelObservableResponseEntry
  ring

/-- Response entries are nonnegative for a nonnegative target envelope. -/
theorem finiteInfluenceKernelObservableResponseEntry_nonneg
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (sourceEnvelope : ι → ℝ)
    (hEnvelope : ∀ e : ι, 0 ≤ sourceEnvelope e)
    (iterations : ℕ)
    (source : ι) :
    0 ≤ finiteInfluenceKernelObservableResponseEntry
      K sourceEnvelope iterations source := by
  unfold finiteInfluenceKernelObservableResponseEntry
    finiteInfluenceKernelObservableResponse
  have hSingleton :
      ∀ e : ι,
        0 ≤ finiteInfluenceKernelSingletonVariation 1 source e := by
    intro e
    unfold finiteInfluenceKernelSingletonVariation
    split <;> norm_num
  have hPartial :
      0 ≤ finiteInfluenceKernelPartialSource K sourceEnvelope
        (finiteInfluenceKernelSingletonVariation 1 source) iterations := by
    induction iterations with
    | zero => exact le_rfl
    | succ n ih =>
        rw [finiteInfluenceKernelPartialSource_succ]
        exact add_nonneg ih
          (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
            (Finset.sum_nonneg fun e _he =>
              mul_nonneg (hEnvelope e)
                (finiteInfluenceKernelRandomScanVariationIterate_nonneg
                  K _ hSingleton n e)))
  exact add_nonneg hPartial
    (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun e _he =>
        finiteInfluenceKernelRandomScanVariationIterate_nonneg
          K _ hSingleton iterations e))

end

end MathlibAnalytic
end MGAP4D
