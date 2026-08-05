import MGAP4D.MathlibAnalytic.FinitePositiveWeightNonstrictStationaryResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A weight-independent nonnegative influence kernel.  Row and column bounds
are supplied separately so the same kernel can be used both before and after a
bootstrap enters the strict Dobrushin region. -/
structure FiniteNonnegativeInfluenceKernelData
    (ι : Type)
    [DecidableEq ι]
    [Fintype ι] where
  influence : ι → ι → ℝ
  influence_nonneg :
    ∀ target source : ι, 0 ≤ influence target source
  influence_diagonal_zero :
    ∀ e : ι, influence e e = 0

/-- Row sum of a weight-independent influence kernel. -/
def finiteInfluenceKernelRowSum
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : ι) : ℝ :=
  ∑ source : ι, K.influence target source

/-- Column sum of a weight-independent influence kernel. -/
def finiteInfluenceKernelColumnSum
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (source : ι) : ℝ :=
  ∑ target : ι, K.influence target source

/-- The universal full-`L¹` top kernel: two off the diagonal and zero on the
diagonal. -/
noncomputable def finiteUniversalTwoInfluenceKernel
    (ι : Type)
    [DecidableEq ι]
    [Fintype ι] :
    FiniteNonnegativeInfluenceKernelData ι :=
  { influence := fun target source => if target = source then 0 else 2
    influence_nonneg := by
      intro target source
      split
      · exact le_rfl
      · norm_num
    influence_diagonal_zero := by
      intro e
      simp }

/-- Every canonical positive-weight influence matrix is dominated by the
universal two kernel. -/
theorem finitePositiveWeightCanonicalNonstrictInfluence_le_universalTwoKernel
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (target source : ι) :
    finitePositiveWeightCanonicalNonstrictInfluence weight target source ≤
      (finiteUniversalTwoInfluenceKernel ι).influence target source := by
  by_cases hEq : target = source
  · subst source
    simp
  · simp only [finiteUniversalTwoInfluenceKernel, hEq, if_false]
    exact finitePositiveWeightCanonicalNonstrictInfluence_le_two
      weight hweight target source

/-- One target update of a profile by a weight-independent kernel. -/
def finiteInfluenceKernelUpdatedVariation
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ)
    (target source : ι) : ℝ :=
  if source = target then 0
  else variation source + K.influence target source * variation target

/-- Kernel target updates preserve profile nonnegativity. -/
theorem finiteInfluenceKernelUpdatedVariation_nonneg
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ)
    (hVariation : ∀ e : ι, 0 ≤ variation e)
    (target source : ι) :
    0 ≤ finiteInfluenceKernelUpdatedVariation
      K variation target source := by
  by_cases hEq : source = target
  · simp [finiteInfluenceKernelUpdatedVariation, hEq]
  · simp only [finiteInfluenceKernelUpdatedVariation, hEq, if_false]
    exact add_nonneg (hVariation source)
      (mul_nonneg (K.influence_nonneg target source)
        (hVariation target))

/-- Uniform random-scan average of the kernel target updates. -/
def finiteInfluenceKernelRandomScanUpdatedVariation
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ)
    (source : ι) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ *
    ∑ target : ι,
      finiteInfluenceKernelUpdatedVariation K variation target source

/-- Kernel random-scan updating preserves nonnegative profiles. -/
theorem finiteInfluenceKernelRandomScanUpdatedVariation_nonneg
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ)
    (hVariation : ∀ e : ι, 0 ≤ variation e)
    (source : ι) :
    0 ≤ finiteInfluenceKernelRandomScanUpdatedVariation
      K variation source := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun target _hTarget =>
      finiteInfluenceKernelUpdatedVariation_nonneg
        K variation hVariation target source)

/-- Exact transpose-oriented target-sum identity.  This is the point where a
column sum, rather than the usual Dobrushin row sum, controls propagation of a
singleton source variation. -/
theorem finiteInfluenceKernelUpdatedVariation_sum_target_eq
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ)
    (source : ι) :
    (∑ target : ι,
      finiteInfluenceKernelUpdatedVariation K variation target source) =
      (Fintype.card ι : ℝ) * variation source +
        (∑ target : ι,
          K.influence target source * variation target) -
        variation source := by
  classical
  have hPointwise (target : ι) :
      finiteInfluenceKernelUpdatedVariation K variation target source =
        variation source + K.influence target source * variation target -
          (if target = source then variation source else 0) := by
    by_cases hEq : target = source
    · subst target
      simp [finiteInfluenceKernelUpdatedVariation,
        K.influence_diagonal_zero]
    · simp [finiteInfluenceKernelUpdatedVariation, hEq, Ne.symm hEq]
  calc
    (∑ target : ι,
      finiteInfluenceKernelUpdatedVariation K variation target source) =
      ∑ target : ι,
        (variation source + K.influence target source * variation target -
          (if target = source then variation source else 0)) := by
      apply Finset.sum_congr rfl
      intro target _hTarget
      exact hPointwise target
    _ = (Fintype.card ι : ℝ) * variation source +
        (∑ target : ι,
          K.influence target source * variation target) -
        variation source := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      simp [nsmul_eq_mul]

/-- Reciprocal random-scan rate generated by a uniform column coefficient. -/
def finiteInfluenceKernelReciprocalRandomScanRate
    (ι : Type)
    [Fintype ι]
    (columnCoefficient : ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ *
    ((Fintype.card ι : ℝ) - 1 + columnCoefficient)

/-- A nonnegative subunit column coefficient produces a nonnegative reciprocal
random-scan rate. -/
theorem finiteInfluenceKernelReciprocalRandomScanRate_nonneg
    {ι : Type}
    [Fintype ι]
    (hCard : 0 < Fintype.card ι)
    (columnCoefficient : ℝ)
    (hColumnNonneg : 0 ≤ columnCoefficient) :
    0 ≤ finiteInfluenceKernelReciprocalRandomScanRate
      ι columnCoefficient := by
  have hCardOne : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast hCard
  unfold finiteInfluenceKernelReciprocalRandomScanRate
  exact mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg _))
    (by linarith)

/-- A strict column coefficient gives a reciprocal random-scan rate strictly
below one. -/
theorem finiteInfluenceKernelReciprocalRandomScanRate_lt_one
    {ι : Type}
    [Fintype ι]
    (hCard : 0 < Fintype.card ι)
    (columnCoefficient : ℝ)
    (hColumnLtOne : columnCoefficient < 1) :
    finiteInfluenceKernelReciprocalRandomScanRate
      ι columnCoefficient < 1 := by
  let n : ℝ := Fintype.card ι
  have hn : 0 < n := by
    exact_mod_cast hCard
  have hNumerator : n - 1 + columnCoefficient < n := by
    linarith
  unfold finiteInfluenceKernelReciprocalRandomScanRate
  change n⁻¹ * (n - 1 + columnCoefficient) < 1
  calc
    n⁻¹ * (n - 1 + columnCoefficient) < n⁻¹ * n :=
      mul_lt_mul_of_pos_left hNumerator (inv_pos.mpr hn)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hn)

/-- Exact complement identity for the reciprocal rate. -/
theorem one_sub_finiteInfluenceKernelReciprocalRandomScanRate
    {ι : Type}
    [Fintype ι]
    (hCard : 0 < Fintype.card ι)
    (columnCoefficient : ℝ) :
    1 - finiteInfluenceKernelReciprocalRandomScanRate
        ι columnCoefficient =
      (Fintype.card ι : ℝ)⁻¹ * (1 - columnCoefficient) := by
  have hCardNe : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hCard
  unfold finiteInfluenceKernelReciprocalRandomScanRate
  field_simp [hCardNe]
  ring

/-- A uniform column bound contracts the supremum of a nonnegative variation
profile at the reciprocal random-scan rate. -/
theorem finiteInfluenceKernelRandomScanUpdatedVariation_le_rate_mul
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hCard : 0 < Fintype.card ι)
    (columnCoefficient : ℝ)
    (hColumnNonneg : 0 ≤ columnCoefficient)
    (hColumnSum :
      ∀ source : ι,
        finiteInfluenceKernelColumnSum K source ≤ columnCoefficient)
    (variation : ι → ℝ)
    (hVariationNonneg : ∀ e : ι, 0 ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e : ι, variation e ≤ bound)
    (source : ι) :
    finiteInfluenceKernelRandomScanUpdatedVariation
        K variation source ≤
      finiteInfluenceKernelReciprocalRandomScanRate
          ι columnCoefficient * bound := by
  let n : ℝ := Fintype.card ι
  have hn : 0 < n := by
    exact_mod_cast hCard
  have hnOne : 1 ≤ n := by
    exact_mod_cast hCard
  have hWeighted :
      (∑ target : ι,
        K.influence target source * variation target) ≤
      columnCoefficient * bound := by
    calc
      (∑ target : ι,
        K.influence target source * variation target) ≤
        ∑ target : ι, K.influence target source * bound := by
          apply Finset.sum_le_sum
          intro target _hTarget
          exact mul_le_mul_of_nonneg_left
            (hVariationBound target)
            (K.influence_nonneg target source)
      _ = finiteInfluenceKernelColumnSum K source * bound := by
        unfold finiteInfluenceKernelColumnSum
        rw [Finset.sum_mul]
      _ ≤ columnCoefficient * bound :=
        mul_le_mul_of_nonneg_right
          (hColumnSum source) hBoundNonneg
  have hBase :
      n * variation source - variation source ≤
        (n - 1) * bound := by
    have hScale := mul_le_mul_of_nonneg_left
      (hVariationBound source) (by linarith : 0 ≤ n - 1)
    nlinarith
  have hTargetSum :
      (∑ target : ι,
        finiteInfluenceKernelUpdatedVariation
          K variation target source) ≤
      (n - 1) * bound + columnCoefficient * bound := by
    rw [finiteInfluenceKernelUpdatedVariation_sum_target_eq]
    change n * variation source +
        (∑ target : ι,
          K.influence target source * variation target) -
        variation source ≤ _
    linarith
  unfold finiteInfluenceKernelRandomScanUpdatedVariation
    finiteInfluenceKernelReciprocalRandomScanRate
  change n⁻¹ *
      (∑ target : ι,
        finiteInfluenceKernelUpdatedVariation
          K variation target source) ≤
    n⁻¹ * (n - 1 + columnCoefficient) * bound
  calc
    n⁻¹ *
        (∑ target : ι,
          finiteInfluenceKernelUpdatedVariation
            K variation target source) ≤
      n⁻¹ * ((n - 1) * bound + columnCoefficient * bound) :=
        mul_le_mul_of_nonneg_left hTargetSum (le_of_lt (inv_pos.mpr hn))
    _ = n⁻¹ * (n - 1 + columnCoefficient) * bound := by ring

/-- Iterated kernel random-scan profile. -/
def finiteInfluenceKernelRandomScanVariationIterate
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ) : ℕ → (ι → ℝ)
  | 0 => variation
  | n + 1 =>
      finiteInfluenceKernelRandomScanUpdatedVariation
        K (finiteInfluenceKernelRandomScanVariationIterate K variation n)

@[simp] theorem finiteInfluenceKernelRandomScanVariationIterate_zero
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ) :
    finiteInfluenceKernelRandomScanVariationIterate K variation 0 =
      variation := rfl

@[simp] theorem finiteInfluenceKernelRandomScanVariationIterate_succ
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ)
    (n : ℕ) :
    finiteInfluenceKernelRandomScanVariationIterate K variation (n + 1) =
      finiteInfluenceKernelRandomScanUpdatedVariation
        K (finiteInfluenceKernelRandomScanVariationIterate K variation n) := rfl

/-- Iterated kernel profiles remain nonnegative. -/
theorem finiteInfluenceKernelRandomScanVariationIterate_nonneg
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ)
    (hVariation : ∀ e : ι, 0 ≤ variation e)
    (n : ℕ)
    (source : ι) :
    0 ≤ finiteInfluenceKernelRandomScanVariationIterate
      K variation n source := by
  induction n with
  | zero => exact hVariation source
  | succ n ih =>
      exact finiteInfluenceKernelRandomScanUpdatedVariation_nonneg
        K _ ih source

/-- Iterated reciprocal column contraction of a uniformly bounded
nonnegative profile. -/
theorem finiteInfluenceKernelRandomScanVariationIterate_le_rate_pow_mul
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hCard : 0 < Fintype.card ι)
    (columnCoefficient : ℝ)
    (hColumnNonneg : 0 ≤ columnCoefficient)
    (hColumnSum :
      ∀ source : ι,
        finiteInfluenceKernelColumnSum K source ≤ columnCoefficient)
    (variation : ι → ℝ)
    (hVariationNonneg : ∀ e : ι, 0 ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e : ι, variation e ≤ bound)
    (n : ℕ)
    (source : ι) :
    finiteInfluenceKernelRandomScanVariationIterate
        K variation n source ≤
      finiteInfluenceKernelReciprocalRandomScanRate
          ι columnCoefficient ^ n * bound := by
  let rate := finiteInfluenceKernelReciprocalRandomScanRate
    ι columnCoefficient
  have hRateNonneg : 0 ≤ rate :=
    finiteInfluenceKernelReciprocalRandomScanRate_nonneg
      hCard columnCoefficient hColumnNonneg
  induction n with
  | zero => simpa [rate] using hVariationBound source
  | succ n ih =>
      have hIterNonneg :
          ∀ e : ι,
            0 ≤ finiteInfluenceKernelRandomScanVariationIterate
              K variation n e :=
        finiteInfluenceKernelRandomScanVariationIterate_nonneg
          K variation hVariationNonneg n
      have hStep :=
        finiteInfluenceKernelRandomScanUpdatedVariation_le_rate_mul
          K hCard columnCoefficient hColumnNonneg hColumnSum
          (finiteInfluenceKernelRandomScanVariationIterate K variation n)
          hIterNonneg (rate ^ n * bound)
          (mul_nonneg (pow_nonneg hRateNonneg n) hBoundNonneg)
          ih source
      simpa [rate, pow_succ, mul_assoc] using hStep

/-- Kernel random-scan updating is monotone on profiles. -/
theorem finiteInfluenceKernelRandomScanUpdatedVariation_mono
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (left right : ι → ℝ)
    (hLeftRight : ∀ e : ι, left e ≤ right e)
    (source : ι) :
    finiteInfluenceKernelRandomScanUpdatedVariation K left source ≤
      finiteInfluenceKernelRandomScanUpdatedVariation K right source := by
  have hInvNonneg : 0 ≤ (Fintype.card ι : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  unfold finiteInfluenceKernelRandomScanUpdatedVariation
  apply mul_le_mul_of_nonneg_left _ hInvNonneg
  apply Finset.sum_le_sum
  intro target _hTarget
  by_cases hEq : source = target
  · simp [finiteInfluenceKernelUpdatedVariation, hEq]
  · simp only [finiteInfluenceKernelUpdatedVariation, hEq, if_false]
    exact add_le_add (hLeftRight source)
      (mul_le_mul_of_nonneg_left
        (hLeftRight target) (K.influence_nonneg target source))

/-- A non-strict concrete influence update is dominated by any entrywise
larger nonnegative kernel update. -/
theorem finitePositiveWeightNonstrictRandomScanUpdatedVariation_le_kernel
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightNonstrictL1MatrixData weight)
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hDomination :
      FinitePositiveWeightNonstrictInfluenceDominatedBy D K.influence)
    (variation : ι → ℝ)
    (hVariation : ∀ e : ι, 0 ≤ variation e)
    (source : ι) :
    finitePositiveWeightNonstrictRandomScanUpdatedVariation
        D variation source ≤
      finiteInfluenceKernelRandomScanUpdatedVariation
        K variation source := by
  have hInvNonneg : 0 ≤ (Fintype.card ι : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  unfold finitePositiveWeightNonstrictRandomScanUpdatedVariation
    finiteInfluenceKernelRandomScanUpdatedVariation
  apply mul_le_mul_of_nonneg_left _ hInvNonneg
  apply Finset.sum_le_sum
  intro target _hTarget
  by_cases hEq : source = target
  · simp [finitePositiveWeightNonstrictUpdatedVariation,
      finiteInfluenceKernelUpdatedVariation, hEq]
  · simp only [finitePositiveWeightNonstrictUpdatedVariation,
      finiteInfluenceKernelUpdatedVariation, hEq, if_false]
    exact add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_right
        (hDomination target source) (hVariation target))

/-- Iterated non-strict profile propagation. -/
def finitePositiveWeightNonstrictRandomScanVariationIterate
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightNonstrictL1MatrixData weight)
    (variation : ι → ℝ) : ℕ → (ι → ℝ)
  | 0 => variation
  | n + 1 =>
      finitePositiveWeightNonstrictRandomScanUpdatedVariation
        D
        (finitePositiveWeightNonstrictRandomScanVariationIterate
          D variation n)

/-- Iterated non-strict profiles remain nonnegative. -/
theorem finitePositiveWeightNonstrictRandomScanVariationIterate_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightNonstrictL1MatrixData weight)
    (variation : ι → ℝ)
    (hVariation : ∀ e : ι, 0 ≤ variation e)
    (n : ℕ)
    (source : ι) :
    0 ≤ finitePositiveWeightNonstrictRandomScanVariationIterate
      D variation n source := by
  induction n with
  | zero => exact hVariation source
  | succ n ih =>
      exact finitePositiveWeightNonstrictRandomScanUpdatedVariation_nonneg
        D _ ih source

/-- Entrywise kernel domination propagates through every finite random-scan
variation iterate. -/
theorem finitePositiveWeightNonstrictRandomScanVariationIterate_le_kernel
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightNonstrictL1MatrixData weight)
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hDomination :
      FinitePositiveWeightNonstrictInfluenceDominatedBy D K.influence)
    (variation : ι → ℝ)
    (hVariation : ∀ e : ι, 0 ≤ variation e)
    (n : ℕ)
    (source : ι) :
    finitePositiveWeightNonstrictRandomScanVariationIterate
        D variation n source ≤
      finiteInfluenceKernelRandomScanVariationIterate
        K variation n source := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      have hIterNonneg :
          ∀ e : ι,
            0 ≤ finitePositiveWeightNonstrictRandomScanVariationIterate
              D variation n e :=
        finitePositiveWeightNonstrictRandomScanVariationIterate_nonneg
          D variation hVariation n
      calc
        finitePositiveWeightNonstrictRandomScanVariationIterate
            D variation (n + 1) source =
          finitePositiveWeightNonstrictRandomScanUpdatedVariation
            D
            (finitePositiveWeightNonstrictRandomScanVariationIterate
              D variation n) source := rfl
        _ ≤ finiteInfluenceKernelRandomScanUpdatedVariation
            K
            (finitePositiveWeightNonstrictRandomScanVariationIterate
              D variation n) source :=
          finitePositiveWeightNonstrictRandomScanUpdatedVariation_le_kernel
            D K hDomination _ hIterNonneg source
        _ ≤ finiteInfluenceKernelRandomScanUpdatedVariation
            K
            (finiteInfluenceKernelRandomScanVariationIterate
              K variation n) source :=
          finiteInfluenceKernelRandomScanUpdatedVariation_mono
            K _ _ ih source
        _ = finiteInfluenceKernelRandomScanVariationIterate
            K variation (n + 1) source := rfl

/-- The variation component carried by the non-strict stationary comparison
iterate is definitionally the non-strict profile iterate. -/
theorem
    FinitePositiveWeightStationaryNonstrictComparisonData.rightRandomScanIterateVariation_eq
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    {leftWeight rightWeight : (ι → G) → ℝ}
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight)
    (n : ℕ) :
    (C.rightRandomScanIterateVariationBound P n).variation =
      finitePositiveWeightNonstrictRandomScanVariationIterate
        C.rightInfluence P.variation n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [
        FinitePositiveWeightStationaryNonstrictComparisonData.rightRandomScanIterateVariationBound_succ,
        finitePositiveWeightNonstrictRandomScanVariationIterate]
      change
        finitePositiveWeightNonstrictRandomScanUpdatedVariation
            C.rightInfluence
            (C.rightRandomScanIterateVariationBound P n).variation =
          finitePositiveWeightNonstrictRandomScanUpdatedVariation
            C.rightInfluence
            (finitePositiveWeightNonstrictRandomScanVariationIterate
              C.rightInfluence P.variation n)
      rw [ih]

/-- Kernel updating distributes over a finite sum of profiles. -/
theorem finiteInfluenceKernelUpdatedVariation_sum
    {ι κ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype κ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (family : κ → ι → ℝ)
    (target source : ι) :
    finiteInfluenceKernelUpdatedVariation
        K (fun e => ∑ k : κ, family k e) target source =
      ∑ k : κ,
        finiteInfluenceKernelUpdatedVariation
          K (family k) target source := by
  by_cases hEq : source = target
  · simp [finiteInfluenceKernelUpdatedVariation, hEq]
  · simp only [finiteInfluenceKernelUpdatedVariation, hEq, if_false]
    rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Kernel random-scan updating distributes over a finite profile sum. -/
theorem finiteInfluenceKernelRandomScanUpdatedVariation_sum
    {ι κ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype κ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (family : κ → ι → ℝ)
    (source : ι) :
    finiteInfluenceKernelRandomScanUpdatedVariation
        K (fun e => ∑ k : κ, family k e) source =
      ∑ k : κ,
        finiteInfluenceKernelRandomScanUpdatedVariation
          K (family k) source := by
  unfold finiteInfluenceKernelRandomScanUpdatedVariation
  simp_rw [finiteInfluenceKernelUpdatedVariation_sum]
  rw [Finset.sum_comm, Finset.mul_sum]

/-- Every finite kernel iterate distributes over finite profile sums. -/
theorem finiteInfluenceKernelRandomScanVariationIterate_sum
    {ι κ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype κ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (family : κ → ι → ℝ)
    (n : ℕ)
    (source : ι) :
    finiteInfluenceKernelRandomScanVariationIterate
        K (fun e => ∑ k : κ, family k e) n source =
      ∑ k : κ,
        finiteInfluenceKernelRandomScanVariationIterate
          K (family k) n source := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [finiteInfluenceKernelRandomScanVariationIterate_succ]
      rw [finiteInfluenceKernelRandomScanUpdatedVariation_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      apply congrArg
        (fun profile : ι → ℝ =>
          finiteInfluenceKernelRandomScanUpdatedVariation K profile source)
      funext e
      exact ih e

/-- Singleton variation profile of amplitude `magnitude`. -/
def finiteInfluenceKernelSingletonVariation
    {ι : Type}
    [DecidableEq ι]
    (magnitude : ℝ)
    (source coordinate : ι) : ℝ :=
  if coordinate = source then magnitude else 0

/-- Superposing every singleton profile gives the constant profile. -/
theorem finiteInfluenceKernelSingletonVariation_sum_source
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (magnitude : ℝ)
    (coordinate : ι) :
    (∑ source : ι,
      finiteInfluenceKernelSingletonVariation
        magnitude source coordinate) = magnitude := by
  classical
  rw [Finset.sum_eq_single coordinate]
  · simp [finiteInfluenceKernelSingletonVariation]
  · intro source _hSource hSource
    simp [finiteInfluenceKernelSingletonVariation, Ne.symm hSource]
  · intro hCoordinate
    exact False.elim (hCoordinate (Finset.mem_univ coordinate))

/-- The source-superposition of all iterated singleton profiles is the iterate
of the corresponding constant profile. -/
theorem finiteInfluenceKernelSingletonVariation_iterate_sum_source
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (magnitude : ℝ)
    (n : ℕ)
    (coordinate : ι) :
    (∑ source : ι,
      finiteInfluenceKernelRandomScanVariationIterate
        K (finiteInfluenceKernelSingletonVariation magnitude source)
        n coordinate) =
      finiteInfluenceKernelRandomScanVariationIterate
        K (fun _ : ι => magnitude) n coordinate := by
  symm
  calc
    finiteInfluenceKernelRandomScanVariationIterate
        K (fun _ : ι => magnitude) n coordinate =
      finiteInfluenceKernelRandomScanVariationIterate
        K
        (fun e => ∑ source : ι,
          finiteInfluenceKernelSingletonVariation magnitude source e)
        n coordinate := by
      apply congrArg
        (fun profile : ι → ℝ =>
          finiteInfluenceKernelRandomScanVariationIterate
            K profile n coordinate)
      funext e
      exact (finiteInfluenceKernelSingletonVariation_sum_source
        magnitude e).symm
    _ = ∑ source : ι,
        finiteInfluenceKernelRandomScanVariationIterate
          K (finiteInfluenceKernelSingletonVariation magnitude source)
          n coordinate :=
      finiteInfluenceKernelRandomScanVariationIterate_sum
        K (fun source =>
          finiteInfluenceKernelSingletonVariation magnitude source)
        n coordinate

/-- Reciprocal column contraction of the complete source-superposition at one
coordinate. -/
theorem finiteInfluenceKernelSingletonVariation_iterate_sum_source_le
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hCard : 0 < Fintype.card ι)
    (columnCoefficient : ℝ)
    (hColumnNonneg : 0 ≤ columnCoefficient)
    (hColumnSum :
      ∀ source : ι,
        finiteInfluenceKernelColumnSum K source ≤ columnCoefficient)
    (magnitude : ℝ)
    (hMagnitude : 0 ≤ magnitude)
    (n : ℕ)
    (coordinate : ι) :
    (∑ source : ι,
      finiteInfluenceKernelRandomScanVariationIterate
        K (finiteInfluenceKernelSingletonVariation magnitude source)
        n coordinate) ≤
      finiteInfluenceKernelReciprocalRandomScanRate
          ι columnCoefficient ^ n * magnitude := by
  rw [finiteInfluenceKernelSingletonVariation_iterate_sum_source]
  exact
    finiteInfluenceKernelRandomScanVariationIterate_le_rate_pow_mul
      K hCard columnCoefficient hColumnNonneg hColumnSum
      (fun _ : ι => magnitude) (fun _ => hMagnitude)
      magnitude hMagnitude (fun _ => le_rfl) n coordinate

/-- Source-summed terminal total variation of all iterated singleton profiles. -/
theorem finiteInfluenceKernelSingletonVariation_iterate_total_sum_source_le
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hCard : 0 < Fintype.card ι)
    (columnCoefficient : ℝ)
    (hColumnNonneg : 0 ≤ columnCoefficient)
    (hColumnSum :
      ∀ source : ι,
        finiteInfluenceKernelColumnSum K source ≤ columnCoefficient)
    (magnitude : ℝ)
    (hMagnitude : 0 ≤ magnitude)
    (n : ℕ) :
    (∑ source : ι,
      finiteProductVariationTotal
        (finiteInfluenceKernelRandomScanVariationIterate
          K (finiteInfluenceKernelSingletonVariation magnitude source) n)) ≤
      (Fintype.card ι : ℝ) *
        (finiteInfluenceKernelReciprocalRandomScanRate
          ι columnCoefficient ^ n * magnitude) := by
  unfold finiteProductVariationTotal
  rw [Finset.sum_comm]
  calc
    (∑ coordinate : ι,
      ∑ source : ι,
        finiteInfluenceKernelRandomScanVariationIterate
          K (finiteInfluenceKernelSingletonVariation magnitude source)
          n coordinate) ≤
      ∑ _coordinate : ι,
        (finiteInfluenceKernelReciprocalRandomScanRate
          ι columnCoefficient ^ n * magnitude) := by
      apply Finset.sum_le_sum
      intro coordinate _hCoordinate
      exact
        finiteInfluenceKernelSingletonVariation_iterate_sum_source_le
          K hCard columnCoefficient hColumnNonneg hColumnSum
          magnitude hMagnitude n coordinate
    _ = (Fintype.card ι : ℝ) *
        (finiteInfluenceKernelReciprocalRandomScanRate
          ι columnCoefficient ^ n * magnitude) := by
      simp [nsmul_eq_mul]

/-- Kernel source pairing for a cross-weight source envelope. -/
def finiteInfluenceKernelSourceError
    {ι : Type}
    [Fintype ι]
    (sourceEnvelope variation : ι → ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ *
    ∑ target : ι, sourceEnvelope target * variation target

/-- Kernel accumulated source response through finitely many profile
iterations. -/
def finiteInfluenceKernelPartialSource
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (sourceEnvelope variation : ι → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      finiteInfluenceKernelPartialSource K sourceEnvelope variation n +
        finiteInfluenceKernelSourceError sourceEnvelope
          (finiteInfluenceKernelRandomScanVariationIterate
            K variation n)

/-- A concrete non-strict source functional is bounded by an entrywise source
envelope and an entrywise larger kernel profile. -/
theorem
    FinitePositiveWeightStationaryNonstrictComparisonData.sourceError_le_kernel
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    {leftWeight rightWeight : (ι → G) → ℝ}
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight)
    (sourceEnvelope leftVariation rightVariation : ι → ℝ)
    (hEnvelopeNonneg : ∀ e : ι, 0 ≤ sourceEnvelope e)
    (hEnvelope : ∀ e : ι, C.sourceBound e ≤ sourceEnvelope e)
    (hLeftNonneg : ∀ e : ι, 0 ≤ leftVariation e)
    (hVariation : ∀ e : ι, leftVariation e ≤ rightVariation e) :
    C.sourceError leftVariation ≤
      finiteInfluenceKernelSourceError sourceEnvelope rightVariation := by
  have hInvNonneg : 0 ≤ (Fintype.card ι : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  unfold sourceError finiteInfluenceKernelSourceError
  apply mul_le_mul_of_nonneg_left _ hInvNonneg
  apply Finset.sum_le_sum
  intro e _he
  calc
    C.sourceBound e * leftVariation e ≤
        sourceEnvelope e * leftVariation e :=
      mul_le_mul_of_nonneg_right (hEnvelope e) (hLeftNonneg e)
    _ ≤ sourceEnvelope e * rightVariation e :=
      mul_le_mul_of_nonneg_left (hVariation e) (hEnvelopeNonneg e)

/-- A concrete accumulated non-strict response is bounded by the corresponding
kernel accumulated response. -/
theorem
    FinitePositiveWeightStationaryNonstrictComparisonData.partialStationarySource_le_kernel
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    {leftWeight rightWeight : (ι → G) → ℝ}
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight)
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hDomination :
      FinitePositiveWeightNonstrictInfluenceDominatedBy
        C.rightInfluence K.influence)
    (sourceEnvelope : ι → ℝ)
    (hEnvelopeNonneg : ∀ e : ι, 0 ≤ sourceEnvelope e)
    (hEnvelope : ∀ e : ι, C.sourceBound e ≤ sourceEnvelope e)
    (n : ℕ) :
    C.partialStationarySource P n ≤
      finiteInfluenceKernelPartialSource
        K sourceEnvelope P.variation n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      have hActualNonneg :
          ∀ e : ι,
            0 ≤ (C.rightRandomScanIterateVariationBound P n).variation e :=
        (C.rightRandomScanIterateVariationBound P n).variation_nonneg
      have hProfile :
          ∀ e : ι,
            (C.rightRandomScanIterateVariationBound P n).variation e ≤
              finiteInfluenceKernelRandomScanVariationIterate
                K P.variation n e := by
        intro e
        rw [C.rightRandomScanIterateVariation_eq P n]
        exact
          finitePositiveWeightNonstrictRandomScanVariationIterate_le_kernel
            C.rightInfluence K hDomination P.variation
            P.variation_nonneg n e
      have hSource := C.sourceError_le_kernel
        sourceEnvelope
        (C.rightRandomScanIterateVariationBound P n).variation
        (finiteInfluenceKernelRandomScanVariationIterate
          K P.variation n)
        hEnvelopeNonneg hEnvelope hActualNonneg hProfile
      rw [partialStationarySource_succ]
      unfold finiteInfluenceKernelPartialSource
      exact add_le_add ih hSource

/-- Finite geometric series used by the reciprocal response bound. -/
def finiteRealGeometricSeries (rate : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, rate ^ k

@[simp] theorem finiteRealGeometricSeries_zero
    (rate : ℝ) :
    finiteRealGeometricSeries rate 0 = 0 := by
  simp [finiteRealGeometricSeries]

@[simp] theorem finiteRealGeometricSeries_succ
    (rate : ℝ)
    (n : ℕ) :
    finiteRealGeometricSeries rate (n + 1) =
      finiteRealGeometricSeries rate n + rate ^ n := by
  simp [finiteRealGeometricSeries, Finset.sum_range_succ]

/-- Elementary finite geometric identity, proved internally to avoid hiding
any convergence argument. -/
theorem one_sub_mul_finiteRealGeometricSeries
    (rate : ℝ)
    (n : ℕ) :
    (1 - rate) * finiteRealGeometricSeries rate n =
      1 - rate ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [finiteRealGeometricSeries_succ, mul_add, ih, pow_succ]
      ring

/-- A nonnegative subunit finite geometric series is bounded by its infinite
resolvent. -/
theorem finiteRealGeometricSeries_le_inv_one_sub
    (rate : ℝ)
    (hRateNonneg : 0 ≤ rate)
    (hRateLtOne : rate < 1)
    (n : ℕ) :
    finiteRealGeometricSeries rate n ≤ (1 - rate)⁻¹ := by
  have hGap : 0 < 1 - rate := sub_pos.mpr hRateLtOne
  have hProduct :
      finiteRealGeometricSeries rate n * (1 - rate) ≤ 1 := by
    rw [mul_comm, one_sub_mul_finiteRealGeometricSeries]
    exact sub_le_self 1 (pow_nonneg hRateNonneg n)
  exact (le_div_iff₀ hGap).2 (by simpa [div_eq_mul_inv] using hProduct)

/-- Summed kernel source error of all singleton initial profiles at one
iteration. -/
theorem finiteInfluenceKernelSourceError_singleton_iterate_sum_source_le
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hCard : 0 < Fintype.card ι)
    (columnCoefficient : ℝ)
    (hColumnNonneg : 0 ≤ columnCoefficient)
    (hColumnSum :
      ∀ source : ι,
        finiteInfluenceKernelColumnSum K source ≤ columnCoefficient)
    (sourceEnvelope : ι → ℝ)
    (hEnvelopeNonneg : ∀ e : ι, 0 ≤ sourceEnvelope e)
    (magnitude : ℝ)
    (hMagnitude : 0 ≤ magnitude)
    (n : ℕ) :
    (∑ source : ι,
      finiteInfluenceKernelSourceError sourceEnvelope
        (finiteInfluenceKernelRandomScanVariationIterate
          K (finiteInfluenceKernelSingletonVariation magnitude source) n)) ≤
      (Fintype.card ι : ℝ)⁻¹ *
        finiteProductVariationTotal sourceEnvelope *
          (finiteInfluenceKernelReciprocalRandomScanRate
            ι columnCoefficient ^ n * magnitude) := by
  have hInvNonneg : 0 ≤ (Fintype.card ι : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  unfold finiteInfluenceKernelSourceError
  rw [← Finset.mul_sum, Finset.sum_comm]
  apply mul_le_mul_of_nonneg_left _ hInvNonneg
  calc
    (∑ target : ι,
      ∑ source : ι,
        sourceEnvelope target *
          finiteInfluenceKernelRandomScanVariationIterate
            K (finiteInfluenceKernelSingletonVariation magnitude source)
            n target) =
      ∑ target : ι,
        sourceEnvelope target *
          (∑ source : ι,
            finiteInfluenceKernelRandomScanVariationIterate
              K (finiteInfluenceKernelSingletonVariation magnitude source)
              n target) := by
      apply Finset.sum_congr rfl
      intro target _hTarget
      rw [Finset.mul_sum]
    _ ≤ ∑ target : ι,
        sourceEnvelope target *
          (finiteInfluenceKernelReciprocalRandomScanRate
            ι columnCoefficient ^ n * magnitude) := by
      apply Finset.sum_le_sum
      intro target _hTarget
      exact mul_le_mul_of_nonneg_left
        (finiteInfluenceKernelSingletonVariation_iterate_sum_source_le
          K hCard columnCoefficient hColumnNonneg hColumnSum
          magnitude hMagnitude n target)
        (hEnvelopeNonneg target)
    _ = finiteProductVariationTotal sourceEnvelope *
        (finiteInfluenceKernelReciprocalRandomScanRate
          ι columnCoefficient ^ n * magnitude) := by
      unfold finiteProductVariationTotal
      rw [Finset.sum_mul]

/-- Source-summed finite kernel response of all singleton profiles. -/
theorem finiteInfluenceKernelPartialSource_singleton_sum_source_le
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hCard : 0 < Fintype.card ι)
    (columnCoefficient : ℝ)
    (hColumnNonneg : 0 ≤ columnCoefficient)
    (hColumnSum :
      ∀ source : ι,
        finiteInfluenceKernelColumnSum K source ≤ columnCoefficient)
    (sourceEnvelope : ι → ℝ)
    (hEnvelopeNonneg : ∀ e : ι, 0 ≤ sourceEnvelope e)
    (magnitude : ℝ)
    (hMagnitude : 0 ≤ magnitude)
    (n : ℕ) :
    (∑ source : ι,
      finiteInfluenceKernelPartialSource
        K sourceEnvelope
        (finiteInfluenceKernelSingletonVariation magnitude source) n) ≤
      (Fintype.card ι : ℝ)⁻¹ *
        finiteProductVariationTotal sourceEnvelope * magnitude *
          finiteRealGeometricSeries
            (finiteInfluenceKernelReciprocalRandomScanRate
              ι columnCoefficient) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [finiteInfluenceKernelPartialSource,
        Finset.sum_add_distrib, finiteRealGeometricSeries_succ]
      have hStep :=
        finiteInfluenceKernelSourceError_singleton_iterate_sum_source_le
          K hCard columnCoefficient hColumnNonneg hColumnSum
          sourceEnvelope hEnvelopeNonneg magnitude hMagnitude n
      calc
        (∑ source : ι,
            finiteInfluenceKernelPartialSource
              K sourceEnvelope
                (finiteInfluenceKernelSingletonVariation magnitude source) n) +
            ∑ source : ι,
              finiteInfluenceKernelSourceError sourceEnvelope
                (finiteInfluenceKernelRandomScanVariationIterate K
                  (finiteInfluenceKernelSingletonVariation magnitude source)
                  n) ≤
          (Fintype.card ι : ℝ)⁻¹ *
              finiteProductVariationTotal sourceEnvelope * magnitude *
                finiteRealGeometricSeries
                  (finiteInfluenceKernelReciprocalRandomScanRate
                    ι columnCoefficient) n +
            (Fintype.card ι : ℝ)⁻¹ *
              finiteProductVariationTotal sourceEnvelope *
                (finiteInfluenceKernelReciprocalRandomScanRate
                  ι columnCoefficient ^ n * magnitude) :=
          add_le_add ih hStep
        _ = (Fintype.card ι : ℝ)⁻¹ *
            finiteProductVariationTotal sourceEnvelope * magnitude *
              (finiteRealGeometricSeries
                  (finiteInfluenceKernelReciprocalRandomScanRate
                    ι columnCoefficient) n +
                finiteInfluenceKernelReciprocalRandomScanRate
                  ι columnCoefficient ^ n) := by ring

/-- The reciprocal resolvent cancels the coordinate-card normalization:
`|ι|⁻¹ (1-q_col)⁻¹ = (1-columnCoefficient)⁻¹`. -/
theorem inv_card_mul_inv_one_sub_reciprocalRate
    {ι : Type}
    [Fintype ι]
    (hCard : 0 < Fintype.card ι)
    (columnCoefficient : ℝ)
    (hColumnLtOne : columnCoefficient < 1) :
    (Fintype.card ι : ℝ)⁻¹ *
        (1 - finiteInfluenceKernelReciprocalRandomScanRate
          ι columnCoefficient)⁻¹ =
      (1 - columnCoefficient)⁻¹ := by
  have hCardNe : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hCard
  have hGapNe : 1 - columnCoefficient ≠ 0 :=
    ne_of_gt (sub_pos.mpr hColumnLtOne)
  rw [one_sub_finiteInfluenceKernelReciprocalRandomScanRate
    hCard columnCoefficient]
  field_simp [hCardNe, hGapNe]

/-- Volume-independent source-summed accumulated response. -/
theorem finiteInfluenceKernelPartialSource_singleton_sum_source_le_resolvent
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hCard : 0 < Fintype.card ι)
    (columnCoefficient : ℝ)
    (hColumnNonneg : 0 ≤ columnCoefficient)
    (hColumnLtOne : columnCoefficient < 1)
    (hColumnSum :
      ∀ source : ι,
        finiteInfluenceKernelColumnSum K source ≤ columnCoefficient)
    (sourceEnvelope : ι → ℝ)
    (hEnvelopeNonneg : ∀ e : ι, 0 ≤ sourceEnvelope e)
    (magnitude : ℝ)
    (hMagnitude : 0 ≤ magnitude)
    (n : ℕ) :
    (∑ source : ι,
      finiteInfluenceKernelPartialSource
        K sourceEnvelope
        (finiteInfluenceKernelSingletonVariation magnitude source) n) ≤
      finiteProductVariationTotal sourceEnvelope * magnitude *
        (1 - columnCoefficient)⁻¹ := by
  let rate := finiteInfluenceKernelReciprocalRandomScanRate
    ι columnCoefficient
  have hRateNonneg : 0 ≤ rate :=
    finiteInfluenceKernelReciprocalRandomScanRate_nonneg
      hCard columnCoefficient hColumnNonneg
  have hRateLtOne : rate < 1 :=
    finiteInfluenceKernelReciprocalRandomScanRate_lt_one
      hCard columnCoefficient hColumnLtOne
  have hFinite :=
    finiteInfluenceKernelPartialSource_singleton_sum_source_le
      K hCard columnCoefficient hColumnNonneg hColumnSum
      sourceEnvelope hEnvelopeNonneg magnitude hMagnitude n
  have hGeom := finiteRealGeometricSeries_le_inv_one_sub
    rate hRateNonneg hRateLtOne n
  have hFactorNonneg :
      0 ≤ (Fintype.card ι : ℝ)⁻¹ *
        finiteProductVariationTotal sourceEnvelope * magnitude := by
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun e _he => hEnvelopeNonneg e))
      hMagnitude
  calc
    (∑ source : ι,
      finiteInfluenceKernelPartialSource
        K sourceEnvelope
        (finiteInfluenceKernelSingletonVariation magnitude source) n) ≤
      (Fintype.card ι : ℝ)⁻¹ *
        finiteProductVariationTotal sourceEnvelope * magnitude *
          finiteRealGeometricSeries rate n := hFinite
    _ ≤ (Fintype.card ι : ℝ)⁻¹ *
        finiteProductVariationTotal sourceEnvelope * magnitude *
          (1 - rate)⁻¹ :=
      mul_le_mul_of_nonneg_left hGeom hFactorNonneg
    _ = finiteProductVariationTotal sourceEnvelope * magnitude *
        (1 - columnCoefficient)⁻¹ := by
      rw [show
        (Fintype.card ι : ℝ)⁻¹ * (1 - rate)⁻¹ =
          (1 - columnCoefficient)⁻¹ by
        exact inv_card_mul_inv_one_sub_reciprocalRate
          hCard columnCoefficient hColumnLtOne]
      ring

end

end MathlibAnalytic
end MGAP4D
