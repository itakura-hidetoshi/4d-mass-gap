import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNonnegativeTopEigenvector
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped InnerProductSpace InnerProduct

noncomputable section

universe u

/-- On a probability space, a normalized nonnegative real `L²` vector has
strictly positive integral. -/
theorem realL2_integral_pos_of_ae_nonnegative_norm_one
    {α : Type u} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hnorm : ‖f‖ = 1) :
    0 < ∫ x, f x ∂μ := by
  have hfInt : Integrable (fun x => f x) μ := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp f).mono_exponent (by norm_num)
  have hnonneg : 0 ≤ ∫ x, f x ∂μ := integral_nonneg_of_ae hf
  have hne : (∫ x, f x ∂μ) ≠ 0 := by
    intro hzero
    have hae0 : (fun x => f x) =ᵐ[μ] (fun _ => (0 : ℝ)) :=
      (integral_eq_zero_iff_of_nonneg_ae hf hfInt).1 hzero
    have hf0 : f = 0 := by
      rw [Lp.eq_zero_iff_ae_eq_zero]
      simpa only [Pi.zero_apply] using hae0
    rw [hf0, norm_zero] at hnorm
    norm_num at hnorm
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- The real `L²` inner product with the constant-one vector is ordinary
integration. -/
theorem realL2_inner_const_one_eq_integral
    {α : Type u} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    (g : Lp ℝ 2 μ) :
    inner ℝ (Lp.const 2 μ (1 : ℝ)) g = ∫ x, g x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const (μ := μ) (p := 2) (c := (1 : ℝ))] with x hx
  rw [hx]
  simp [real_inner_eq_re_inner (𝕜 := ℝ), RCLike.inner_apply,
    RCLike.re_to_real, Function.const_apply]

/-- More generally, pairing a scalar multiple of the constant-one vector with
`g` is the scalar times the integral of `g`. -/
theorem realL2_inner_smul_const_one_eq_integral
    {α : Type u} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    (c : ℝ)
    (g : Lp ℝ 2 μ) :
    inner ℝ (c • Lp.const 2 μ (1 : ℝ)) g = c * ∫ x, g x ∂μ := by
  rw [real_inner_smul_left, realL2_inner_const_one_eq_integral]

/-- If a real `L²` vector pairs nonnegatively with its own negative part, then
it is nonnegative almost everywhere.  This is the cone-duality step used below
and does not require choosing a pointwise representative of an operator
output. -/
theorem realL2_ae_nonnegative_of_inner_negPart_nonneg
    {α : Type u} [MeasurableSpace α] {μ : Measure α}
    (h : Lp ℝ 2 μ)
    (hh : 0 ≤ inner ℝ h (Lp.negPart h)) :
    ∀ᵐ x ∂μ, 0 ≤ h x := by
  have hformula :
      inner ℝ h (Lp.negPart h) = - ‖Lp.negPart h‖ ^ 2 := by
    rw [MeasureTheory.L2.inner_def, realL2_norm_sq_eq_integral_norm_sq]
    calc
      (∫ x, inner ℝ (h x) (Lp.negPart h x) ∂μ) =
          ∫ x, -(‖Lp.negPart h x‖ ^ 2) ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_negPart_eq_max h] with x hx
        rw [hx]
        simp only [real_inner_eq_re_inner (𝕜 := ℝ), RCLike.inner_apply,
          RCLike.re_to_real, conj_trivial]
        by_cases hnonneg : 0 ≤ h x
        · rw [max_eq_right (neg_nonpos.mpr hnonneg)]
          simp
        · have hneg : h x < 0 := lt_of_not_ge hnonneg
          rw [max_eq_left (neg_nonneg.mpr hneg.le)]
          rw [Real.norm_eq_abs, abs_of_nonneg (neg_nonneg.mpr hneg.le)]
          ring
      _ = - ∫ x, ‖Lp.negPart h x‖ ^ 2 ∂μ := by
        rw [integral_neg]
  have hnormSq : ‖Lp.negPart h‖ ^ 2 = 0 := by
    rw [hformula] at hh
    nlinarith [sq_nonneg ‖Lp.negPart h‖]
  have hnorm : ‖Lp.negPart h‖ = 0 := by
    nlinarith [norm_nonneg (Lp.negPart h)]
  have hnegZero : Lp.negPart h = 0 := norm_eq_zero.mp hnorm
  have hzero : ∀ᵐ x ∂μ, Lp.negPart h x = 0 := by
    rw [hnegZero]
    simpa only [Pi.zero_apply] using (Lp.coeFn_zero ℝ 2 μ)
  filter_upwards [Lp.coeFn_negPart_eq_max h, hzero] with x hx hz
  rw [hx] at hz
  have hle : -h x ≤ 0 := by
    calc
      -h x ≤ max (-h x) 0 := le_max_left _ _
      _ = 0 := hz
  linarith

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

set_option maxHeartbeats 2000000

/-- Joint continuity and compactness upgrade pointwise positivity of the actual
one-slab Wilson kernel to a uniform positive floor on each fixed finite
volume. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_exists_uniform_pos_lower_bound
    (H N : ℕ)
    (beta : ℝ) :
    ∃ m : ℝ, 0 < m ∧
      ∀ A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        m ≤ periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B := by
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let k : X × X → ℝ := fun p =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta p.1 p.2
  have hkcont : Continuous k := by
    simpa [X, k] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        H N beta
  obtain ⟨p, _hp, hmin⟩ :=
    isCompact_univ.exists_isMinOn
      (Set.univ_nonempty : (Set.univ : Set (X × X)).Nonempty)
      hkcont.continuousOn
  refine ⟨k p, ?_, ?_⟩
  · dsimp [k]
    exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta p.1 p.2
  · intro A B
    exact hmin (by simp : (A, B) ∈ (Set.univ : Set (X × X)))

/-- A uniform lower bound on the literal Wilson kernel yields the corresponding
rank-one lower bound on every nonnegative matrix coefficient of the actual
ambient Haar-`L²` transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (m : ℝ)
    (hm : ∀ A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      m ≤ periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta A B)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (hf : ∀ᵐ A ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      0 ≤ f A)
    (hg : ∀ᵐ A ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      0 ≤ g A) :
    m * (∫ A, f A ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) *
        (∫ B, g B ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) ≤
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) g := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
    H N hN beta hbeta
  let E := realL2ExternalTensor f g
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner,
    realL2HilbertSchmidtKernelPairing]
  change
    m * (∫ A, f A ∂μ) * (∫ B, g B ∂μ) ≤
      ∫ z, inner ℝ (K z) (E z) ∂(μ.prod μ)
  have hfgInt : Integrable (realL2ExternalTensorFunction f g) (μ.prod μ) := by
    rw [← memLp_one_iff_integrable]
    exact (realL2ExternalTensorFunction_memLp_two f g).mono_exponent (by norm_num)
  have hleftInt :
      Integrable (fun z : _ × _ => m * realL2ExternalTensorFunction f g z) (μ.prod μ) :=
    hfgInt.const_mul m
  have hrightInt : Integrable (fun z => inner ℝ (K z) (E z)) (μ.prod μ) :=
    MeasureTheory.L2.integrable_inner K E
  have hfFst : ∀ᵐ z ∂(μ.prod μ), 0 ≤ f z.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hf
  have hgSnd : ∀ᵐ z ∂(μ.prod μ), 0 ≤ g z.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hg
  have hKrep :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
      H N hN beta hbeta
  have hErep := realL2ExternalTensor_coeFn f g
  calc
    m * (∫ A, f A ∂μ) * (∫ B, g B ∂μ) =
        m * ∫ z : _ × _, f z.1 * g z.2 ∂(μ.prod μ) := by
      rw [integral_prod_mul]
      exact mul_assoc m _ _
    _ = ∫ z : _ × _, m * (f z.1 * g z.2) ∂(μ.prod μ) := by
      rw [integral_const_mul]
    _ = ∫ z : _ × _, m * realL2ExternalTensorFunction f g z ∂(μ.prod μ) := by
      rfl
    _ ≤ ∫ z, inner ℝ (K z) (E z) ∂(μ.prod μ) := by
      apply integral_mono_ae hleftInt hrightInt
      filter_upwards [hKrep, hErep, hfFst, hgSnd] with z hk hE hfz hgz
      simp only [realL2ExternalTensorFunction] at hE ⊢
      rw [hk, hE]
      simp only [real_inner_eq_re_inner (𝕜 := ℝ), RCLike.inner_apply,
        RCLike.re_to_real, conj_trivial]
      have hfg : 0 ≤ f z.1 * g z.2 := mul_nonneg hfz hgz
      calc
        m * (f z.1 * g z.2) ≤
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta z.1 z.2 * (f z.1 * g z.2) :=
          mul_le_mul_of_nonneg_right (hm z.1 z.2) hfg
        _ = (f z.1 * g z.2) *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta z.1 z.2 := by ring

/-- The actual ambient Wilson transfer improves every normalized nonnegative
`L²` vector to a vector bounded below by a strictly positive constant almost
everywhere. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_ae_ge_pos_const
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (hf : ∀ᵐ A ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      0 ≤ f A)
    (hnorm : ‖f‖ = 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᵐ A ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
        c ≤ periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f A := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  obtain ⟨m, hmpos, hm⟩ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_exists_uniform_pos_lower_bound
      H N beta
  have hfIntPos : 0 < ∫ A, f A ∂μ :=
    realL2_integral_pos_of_ae_nonnegative_norm_one f hf hnorm
  let c := m * ∫ A, f A ∂μ
  have hcpos : 0 < c := mul_pos hmpos hfIntPos
  let oneL2 : Lp ℝ 2 μ := Lp.const 2 μ (1 : ℝ)
  let T := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
    H N hN beta hbeta
  let h : Lp ℝ 2 μ := T f - c • oneL2
  let g : Lp ℝ 2 μ := Lp.negPart h
  have hgNonneg : ∀ᵐ A ∂μ, 0 ≤ g A := by
    dsimp [g]
    exact (Lp.coeFn_negPart_eq_max h).mono fun A hA => by
      rw [hA]
      exact le_max_right _ _
  have hpair :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner_lower_bound
      H N hN beta hbeta m hm f g hf hgNonneg
  have honePair : inner ℝ (c • oneL2) g = c * ∫ A, g A ∂μ := by
    simpa [oneL2] using realL2_inner_smul_const_one_eq_integral c g
  have hh : 0 ≤ inner ℝ h g := by
    rw [show h = T f - c • oneL2 by rfl, inner_sub_left, honePair]
    have hpair' : c * (∫ A, g A ∂μ) ≤ inner ℝ (T f) g := by
      simpa [c, μ, T] using hpair
    linarith
  have hNonneg : ∀ᵐ A ∂μ, 0 ≤ h A :=
    realL2_ae_nonnegative_of_inner_negPart_nonneg h hh
  have hTsub :
      (fun A => h A) =ᵐ[μ] fun A => T f A - c := by
    have hsub := Lp.coeFn_sub (T f) (c • oneL2)
    have hsmul := Lp.coeFn_smul c oneL2
    have hone := Lp.coeFn_const (μ := μ) (p := 2) (c := (1 : ℝ))
    filter_upwards [hsub, hsmul, hone] with A hs hsc ho
    have hs' : h A = T f A - (c • oneL2) A := by
      change (T f - c • oneL2 : Lp ℝ 2 μ) A = T f A - (c • oneL2) A
      simpa only [Pi.sub_apply] using hs
    have hsc' : (c • oneL2) A = c * oneL2 A := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hsc
    have ho' : oneL2 A = 1 := by
      simpa [oneL2, Function.const_apply] using ho
    calc
      h A = T f A - (c • oneL2) A := hs'
      _ = T f A - c * oneL2 A := by rw [hsc']
      _ = T f A - c := by rw [ho']; ring
  refine ⟨c, hcpos, ?_⟩
  filter_upwards [hNonneg, hTsub] with A hA hEq
  rw [hEq] at hA
  linarith

/-- The constant physical unit vector has strictly positive transfer
expectation, now derived from the uniform Wilson-kernel floor. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_transfer_expectation_pos_from_uniform_kernel_floor
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 < inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N))
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let oneP := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  obtain ⟨m, hmpos, hm⟩ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_exists_uniform_pos_lower_bound
      H N beta
  have honeNonneg : ∀ᵐ A ∂μ, 0 ≤ (oneP : Lp ℝ 2 μ) A := by
    change ∀ᵐ A ∂μ, 0 ≤ (Lp.const 2 μ (1 : ℝ)) A
    filter_upwards [Lp.coeFn_const (μ := μ) (p := 2) (c := (1 : ℝ))] with A hA
    rw [hA]
    simp
  have honeNorm : ‖(oneP : Lp ℝ 2 μ)‖ = 1 := by
    change ‖oneP‖ = 1
    exact periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H N
  have honeIntPos : 0 < ∫ A, (oneP : Lp ℝ 2 μ) A ∂μ :=
    realL2_integral_pos_of_ae_nonnegative_norm_one
      (oneP : Lp ℝ 2 μ) honeNonneg honeNorm
  have hpair :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner_lower_bound
      H N hN beta hbeta m hm
      (oneP : Lp ℝ 2 μ) (oneP : Lp ℝ 2 μ) honeNonneg honeNonneg
  have hleftPos :
      0 < m * (∫ A, (oneP : Lp ℝ 2 μ) A ∂μ) *
        (∫ A, (oneP : Lp ℝ 2 μ) A ∂μ) :=
    mul_pos (mul_pos hmpos honeIntPos) honeIntPos
  change 0 < inner ℝ
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
      H N hN beta hbeta (oneP : Lp ℝ 2 μ))
    (oneP : Lp ℝ 2 μ)
  exact lt_of_lt_of_le hleftPos hpair

/-- The physical one-slab transfer norm is strictly positive by the same
uniform-kernel-floor route. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  have hExpPos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_transfer_expectation_pos_from_uniform_kernel_floor
      H N hN beta hbeta
  change 0 < inner ℝ
    (T (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N))
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) at hExpPos
  have hT : T ≠ 0 := by
    intro hzero
    rw [hzero] at hExpPos
    simp at hExpPos
  have hnormNe : ‖T‖ ≠ 0 := by
    intro hnorm
    have hTzero : T = 0 := by
      rw [← ContinuousLinearMap.opNorm_zero_iff]
      exact hnorm
    exact hT hTzero
  exact lt_of_le_of_ne (norm_nonneg T) (Ne.symm hnormNe)

/-- The canonical nonnegative physical top eigenvector from the previous unit
is in fact strictly positive almost everywhere.  No simplicity or uniqueness
of the top eigenspace is used. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∀ᵐ A ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      0 <
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 A := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  let f : Lp ℝ 2 μ := Ω.1
  let lambda := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖
  have hfNonneg : ∀ᵐ A ∂μ, 0 ≤ f A := by
    simpa [f, Ω] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
        H N hN beta hbeta
  have hfnorm : ‖f‖ = 1 := by
    change ‖Ω‖ = 1
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H N hN beta hbeta
  obtain ⟨c, hcpos, hTc⟩ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_ae_ge_pos_const
      H N hN beta hbeta f hfNonneg hfnorm
  have hlambdaPos : 0 < lambda := by
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H N hN beta hbeta
  have heigenP :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H N hN beta hbeta
  have heigenAmbient :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f = lambda • f := by
    have hval := congrArg Subtype.val heigenP
    simpa [f, Ω, lambda] using hval
  have hcoe :
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f A) =ᵐ[μ]
        fun A => lambda * f A := by
    rw [heigenAmbient]
    simpa only [Pi.smul_apply, smul_eq_mul] using Lp.coeFn_smul lambda f
  filter_upwards [hTc, hcoe] with A hc hEq
  rw [hEq] at hc
  by_contra hnot
  have hfa : f A ≤ 0 := le_of_not_gt hnot
  have hnonpos : lambda * f A ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlambdaPos.le hfa
  linarith

/-- Audit-visible strict-positivity receipt for the finite-volume physical
Wilson vacuum.  This package deliberately stops short of claiming uniqueness
or simplicity of the top eigenvalue. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabStrictlyPositiveTopEigenvectorPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  unit :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta‖ = 1
  aePositive :
    ∀ᵐ A ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      0 <
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 A
  topEigen :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta
  topNormPositive :
    0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖

/-- Construct the strictly positive finite-volume physical Wilson vacuum
receipt from the literal one-slab kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabStrictlyPositiveTopEigenvectorPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabStrictlyPositiveTopEigenvectorPackage
      H N hN beta hbeta :=
  { unit :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
        H N hN beta hbeta
    aePositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_pos
        H N hN beta hbeta
    topEigen :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
        H N hN beta hbeta
    topNormPositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D