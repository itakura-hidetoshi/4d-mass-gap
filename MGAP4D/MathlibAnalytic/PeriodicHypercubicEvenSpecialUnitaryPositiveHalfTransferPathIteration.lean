import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfHaarTemporalGaugeReduction
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 1000000

local instance positiveHalfTransferIterationSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance positiveHalfTransferIterationSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfTransferIterationSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfTransferIterationSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfTransferIterationSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfTransferIterationSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A spatial path with exactly `n` adjacent one-slab transfer steps and therefore `n+1` slices. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath
    (H N n : ℕ) : Type :=
  Fin (n + 1) → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N

/-- Product one-slice Haar law on an arbitrary finite `n`-slab spatial path. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure
    (H N n : ℕ) :
    Measure (PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n) :=
  Measure.pi
    (fun _ : Fin (n + 1) =>
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

instance periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaar_isProbabilityMeasure
    (H N n : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n) := by
  unfold periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure
  infer_instance

/-- Product of the actual one-slab temporal-gauge kernels along an arbitrary `n`-slab path. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
    (H N : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n) : ℝ :=
  ∏ i : Fin n,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
      (path i.castSucc) (path i.succ)

/-- Endpoint-weighted `n`-slab path amplitude.  For `n = H+1` this is the temporal-gauge
positive-half amplitude produced after #2061 has integrated out the temporal-link field. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
    (H N : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (f g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) : ℝ :=
  ∫ path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
    f (path 0) *
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel H N beta n path *
      g (path (Fin.last n))
    ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)

/-- The arbitrary finite path kernel is continuous. -/
theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel_continuous
    (H N : ℕ)
    (beta : ℝ)
    (n : ℕ) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel H N beta n) := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
  apply continuous_finset_prod
  intro i _hi
  exact
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).comp (by fun_prop)

/-- At nonnegative coupling every arbitrary finite path kernel has absolute value at most one. -/
theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel_abs_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n) :
    |periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
        H N beta n path| ≤ 1 := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
  have habs :
      |∏ i : Fin n,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
            (path i.castSucc) (path i.succ)| =
        ∏ i : Fin n,
          |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
            (path i.castSucc) (path i.succ)| := by
    simpa using
      (Finset.abs_prod (Finset.univ : Finset (Fin n))
        (fun i : Fin n =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
            (path i.castSucc) (path i.succ)))
  rw [habs]
  calc
    (∏ i : Fin n,
        |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
          (path i.castSucc) (path i.succ)|) ≤
      ∏ _i : Fin n, (1 : ℝ) := by
        exact Finset.prod_le_prod
          (fun _ _ => abs_nonneg _)
          (fun i _ =>
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
              H N hN beta hbeta (path i.castSucc) (path i.succ))
    _ = 1 := by simp

/-- For an `L²` left boundary state, multiplication by one bounded one-slab kernel is integrable
on the product Haar probability. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabWeightedLeft_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        f p.1 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2)
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  have hf1 : Integrable (fun A => f A) μ := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp f).mono_exponent (by norm_num)
  have hbase : Integrable (fun p :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => f p.1)
      (μ.prod μ) := hf1.comp_fst μ
  have hKmeas : AEStronglyMeasurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2)
      (μ.prod μ) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).aestronglyMeasurable
  apply hbase.mono (hbase.aestronglyMeasurable.mul hKmeas)
  filter_upwards with p
  have hk :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H N hN beta hbeta p.1 p.2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left hk (abs_nonneg (f p.1))

/-- Literal pointwise integral representative of the Riesz-constructed one-slab transfer. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
    (H N : ℕ)
    (beta : ℝ)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ∫ A,
    f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B
    ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

/-- The literal one-slab integral representative belongs to spatial Haar `L²`. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative_memLp
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
        H N beta f)
      2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let F := fun p :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      f p.1 * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta p.1 p.2
  have hF : Integrable F (μ.prod μ) := by
    simpa [μ, F] using
      periodicHypercubicEvenSpecialUnitaryOneSlabWeightedLeft_integrable
        H N hN beta hbeta f
  have hf1 : Integrable (fun A => f A) μ := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp f).mono_exponent (by norm_num)
  have hrepInt : Integrable
      (fun B => ∫ A, F (A, B) ∂μ) μ := hF.integral_prod_right
  apply MemLp.of_bound hrepInt.aestronglyMeasurable
    (∫ A, ‖f A‖ ∂μ)
  filter_upwards [hF.prod_left_ae] with B hB
  change
    ‖∫ A, f A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B ∂μ‖ ≤
      ∫ A, ‖f A‖ ∂μ
  calc
    ‖∫ A, f A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B ∂μ‖ ≤
      ∫ A, ‖f A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ A, ‖f A‖ ∂μ := by
      apply integral_mono_ae hB.norm hf1.norm
      filter_upwards with A
      change
        |f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B| ≤ |f A|
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
          H N hN beta hbeta A B)
        (abs_nonneg (f A))

/-- `L²` vector associated to the literal one-slab integral representative. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative_memLp
    H N hN beta hbeta f).toLp
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
        H N beta f)

/-- The literal integral `L²` vector has the expected almost-everywhere representative. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2_coeFn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2
        H N hN beta hbeta f =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
        H N beta f :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative_memLp
    H N hN beta hbeta f).coeFn_toLp

/-- The Riesz one-slab transfer matrix coefficient is the literal endpoint-weighted double Haar
integral of the one-slab Wilson kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner_eq_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) g =
      ∫ p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        f p.1 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 * g p.2
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner]
  unfold realL2HilbertSchmidtKernelPairing
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
    H N hN beta hbeta
  let tensor := realL2ExternalTensor
    (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
    (ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) f g
  calc
    inner ℝ K tensor =
        ∫ p,
          inner ℝ (K p) (tensor p)
          ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
      MeasureTheory.L2.inner_def K tensor
    _ = _ := by
      have hK :=
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
          H N hN beta hbeta
      have hfg := realL2ExternalTensor_coeFn
        (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        (ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) f g
      apply integral_congr_ae
      filter_upwards [hK, hfg] with p hpK hpfg
      change inner ℝ (K p) (tensor p) = _
      rw [show K p =
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 by simpa [K] using hpK]
      rw [show tensor p = f p.1 * g p.2 by
        simpa [tensor, realL2ExternalTensorFunction] using hpfg]
      rw [realL2Scalar_inner_eq_mul]
      ring

/-- The literal integral representative is exactly the already-canonical Riesz transfer vector. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2_eq_operator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2
        H N hN beta hbeta f =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta f := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  apply ext_inner_right ℝ
  intro g
  have hrep :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2_coeFn
      H N hN beta hbeta f
  have hf1 : Integrable (fun A => f A) μ := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp f).mono_exponent (by norm_num)
  have hg1 : Integrable (fun B => g B) μ := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp g).mono_exponent (by norm_num)
  have hbase : Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        f p.1 * g p.2)
      (μ.prod μ) := hf1.mul_prod hg1
  have hKmeas : AEStronglyMeasurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2)
      (μ.prod μ) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).aestronglyMeasurable
  have hAll : Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        f p.1 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 * g p.2)
      (μ.prod μ) := by
    apply hbase.mono
      (((Lp.aestronglyMeasurable f).comp_fst.mul hKmeas).mul
        (Lp.aestronglyMeasurable g).comp_snd)
    filter_upwards with p
    have hk :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H N hN beta hbeta p.1 p.2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    calc
      |f p.1| *
          |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2| * |g p.2| ≤
        |f p.1| * 1 * |g p.2| := by gcongr
      _ = |f p.1| * |g p.2| := by ring
  calc
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2
          H N hN beta hbeta f) g =
      ∫ B,
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2
            H N hN beta hbeta f B)
          (g B) ∂μ :=
      MeasureTheory.L2.inner_def
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2
          H N hN beta hbeta f) g
    _ = ∫ B,
        (∫ A,
          f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A B ∂μ) * g B ∂μ := by
      apply integral_congr_ae
      filter_upwards [hrep] with B hB
      rw [hB, realL2Scalar_inner_eq_mul]
      rfl
    _ = ∫ p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        f p.1 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 * g p.2 ∂(μ.prod μ) := by
      rw [MeasureTheory.integral_prod_symm _ hAll]
      apply integral_congr_ae
      filter_upwards with B
      rw [integral_mul_const]
    _ = inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) g := by
      symm
      simpa [μ] using
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner_eq_integral
          H N hN beta hbeta f g

/-- Pointwise form of the actual one-slab transfer, now justified from the Riesz construction. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_coeFn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta f =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
        H N beta f := by
  rw [← periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2_eq_operator
    H N hN beta hbeta f]
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2_coeFn
      H N hN beta hbeta f

/-- Recursive operator iterate with the path-integral convention
`T^[n+1] = T^[n] ∘ T`, matching removal of the first slab. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIterate
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ℕ →
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →L[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
  | 0 => 1
  | n + 1 =>
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIterate
        H N hN beta hbeta n).comp
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIterate_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIterate
      H N hN beta hbeta 0 = 1 := rfl

@[simp] theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIterate_succ
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIterate
        H N hN beta hbeta (n + 1) =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIterate
        H N hN beta hbeta n).comp
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta) := rfl

/-- The recursion agrees exactly with the ordinary composition power. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIterate_eq_pow
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIterate
        H N hN beta hbeta n =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIterate_succ, ih]
      simpa [ContinuousLinearMap.mul_def] using
        (pow_succ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H N hN beta hbeta) n).symm

/-- The zero-slab endpoint amplitude is the ordinary Haar-`L²` inner product. -/
theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude_zero
    (H N : ℕ)
    (beta : ℝ)
    (f g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
        H N beta 0 f g = inner ℝ f g := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  change
    (∫ path : Fin 1 → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      f (path 0) * g (path 0) ∂(Measure.pi (fun _ : Fin 1 => μ))) = inner ℝ f g
  calc
    (∫ path : Fin 1 → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      f (path 0) * g (path 0) ∂(Measure.pi (fun _ : Fin 1 => μ))) =
      ∫ path : Fin 1 → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        inner ℝ (f (path 0)) (g (path 0))
        ∂(Measure.pi (fun _ : Fin 1 => μ)) := by
      apply integral_congr_ae
      filter_upwards with path
      rw [realL2Scalar_inner_eq_mul]
    _ = ∫ A, inner ℝ (f A) (g A) ∂μ := by
      exact
        (MeasureTheory.measurePreserving_eval
          (μ := fun _ : Fin 1 => μ) (0 : Fin 1)).integral_comp'
          (fun A => inner ℝ (f A) (g A))
    _ = inner ℝ f g :=
      (MeasureTheory.L2.inner_def f g).symm

/-- Algebraic decomposition of an `(n+1)`-slab kernel after exposing its first slice. -/
private theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel_cons
    (H N : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n) :
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
        H N beta (n + 1) (Fin.cons A tail) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A (tail 0) *
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
          H N beta n tail := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
  rw [Fin.prod_univ_succ]
  simp [Fin.cons_succ]

/-- Exposing the first slice turns the `(n+1)`-slab path integral into the `n`-slab amplitude
with the one-slab transfer applied to the left endpoint state. -/
theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude_succ
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
        H N beta (n + 1) f g =
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
        H N beta n
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) g := by
  classical
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let tailμ := periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n
  let μs : Fin (n + 2) → Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) := fun _ => μ
  have hMP := MeasureTheory.measurePreserving_piFinSuccAbove μs (0 : Fin (n + 2))
  have hf1 : Integrable (fun A => f A) μ := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp f).mono_exponent (by norm_num)
  have hg1 : Integrable (fun A => g A) μ := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp g).mono_exponent (by norm_num)
  have hgtail : Integrable
      (fun tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        g (tail (Fin.last n))) tailμ := by
    simpa [tailμ, periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure] using
      (MeasureTheory.integrable_comp_eval
        (μ := fun _ : Fin (n + 1) => μ) hg1 (Fin.last n))
  have hbase : Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        f p.1 * g (p.2 (Fin.last n)))
      (μ.prod tailμ) := hf1.mul_prod hgtail
  have hKfirst : Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 (p.2 0)) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).measurable.comp
      (measurable_fst.prod_mk ((measurable_pi_apply 0).comp measurable_snd))
  have hKtail : Measurable
      (periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel H N beta n) :=
    (periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel_continuous
      H N beta n).measurable
  have hsplit : Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        f p.1 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 (p.2 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n p.2 *
          g (p.2 (Fin.last n)))
      (μ.prod tailμ) := by
    have hmeas : AEStronglyMeasurable
        (fun p :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
          f p.1 *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta p.1 (p.2 0) *
            periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
              H N beta n p.2 *
            g (p.2 (Fin.last n)))
        (μ.prod tailμ) := by
      exact (((Lp.aestronglyMeasurable f).comp_fst.mul hKfirst.aestronglyMeasurable).mul
        (hKtail.aestronglyMeasurable.comp_snd)).mul
          ((Lp.aestronglyMeasurable g).comp
            (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := tailμ))).comp
            (MeasureTheory.measurePreserving_eval
              (μ := fun _ : Fin (n + 1) => μ) (Fin.last n)).quasiMeasurePreserving
    apply hbase.mono hmeas
    filter_upwards with p
    have hk1 :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H N hN beta hbeta p.1 (p.2 0)
    have hkn :=
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel_abs_le_one
        H N hN beta hbeta n p.2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul]
    calc
      |f p.1| *
          |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 (p.2 0)| *
          |periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n p.2| * |g (p.2 (Fin.last n))| ≤
        |f p.1| * 1 * 1 * |g (p.2 (Fin.last n))| := by gcongr
      _ = |f p.1| * |g (p.2 (Fin.last n))| := by ring
  have hTf :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_coeFn
      H N hN beta hbeta f
  have hTfTail :=
    (MeasureTheory.measurePreserving_eval
      (μ := fun _ : Fin (n + 1) => μ) (0 : Fin (n + 1))).quasiMeasurePreserving.ae_eq hTf
  unfold periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
  calc
    (∫ path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N (n + 1),
      f (path 0) *
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
          H N beta (n + 1) path *
        g (path (Fin.last (n + 1)))
      ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N (n + 1))) =
      ∫ p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        f p.1 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 (p.2 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n p.2 *
          g (p.2 (Fin.last n)) ∂(μ.prod tailμ) := by
        change
          (∫ path : Fin (n + 2) → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
            f (path 0) *
              periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
                H N beta (n + 1) path *
              g (path (Fin.last (n + 1))) ∂(Measure.pi μs)) = _
        rw [← hMP.symm.integral_comp']
        apply integral_congr_ae
        filter_upwards with p
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.insertNth_zero]
        rw [periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel_cons]
        simp [Fin.cons_zero, Fin.cons_succ]
        ring
    _ = ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        (∫ A,
          f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A (tail 0) ∂μ) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail *
          g (tail (Fin.last n)) ∂tailμ := by
        rw [MeasureTheory.integral_prod_symm _ hsplit]
        apply integral_congr_ae
        filter_upwards with tail
        rw [integral_mul_const]
        ring
    _ = ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) (tail 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail *
          g (tail (Fin.last n)) ∂tailμ := by
        apply integral_congr_ae
        filter_upwards [hTfTail] with tail htail
        rw [htail]
    _ = ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) (tail 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail *
          g (tail (Fin.last n))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n) := by
        rfl

/-- Every finite temporal-gauge path amplitude is exactly the matrix coefficient of the
corresponding recursive one-slab transfer iterate. -/
theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude_eq_iterate_inner
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
        H N beta n f g =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIterate
          H N hN beta hbeta n f) g := by
  induction n generalizing f with
  | zero =>
      simpa using
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude_zero
          H N beta f g
  | succ n ih =>
      rw [periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude_succ
        H N hN beta hbeta n f g]
      rw [ih]
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIterate_succ]
      rfl

/-- Equivalently, every finite path amplitude is the matrix coefficient of the ordinary transfer
power. -/
theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude_eq_pow_inner
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
        H N beta n f g =
      inner ℝ
        (((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta) ^ n) f) g := by
  rw [periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude_eq_iterate_inner
    H N hN beta hbeta n f g]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIterate_eq_pow]

/-- The generic `H+1`-slab path carrier is definitionally the existing positive-half-cylinder
carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure_eq_nSlab
    (H N : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N =
      periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N
        (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) := by
  rfl

/-- The generic `H+1`-slab kernel is exactly the existing positive-half temporal-gauge kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugePathKernel_eq_nSlab
    (H N : ℕ)
    (beta : ℝ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta path =
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel H N beta
        (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) path := by
  rfl

/-- Coercing a physical transfer power back to the ambient Haar `L²` space agrees with the
corresponding power of the ambient transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_pow_coe
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ((((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ^ n) f :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta) ^ n)
        (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      change
        ((((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ n)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H N hN beta hbeta f) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) = _
      rw [ih]
      rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_coe]
      rfl

/-- Main transfer/path theorem: the complete temporal-gauge positive-half endpoint amplitude on
Gauss-law boundary states is exactly the matrix coefficient of the existing physical
`(H+1)`-fold one-slab transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_temporalGauge_integral_eq_physicalTransfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (∫ path,
      (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path *
        (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta f) g := by
  let n := periodicHypercubicEvenPositiveHalfCylinderSlabCount H
  have hAmp :=
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude_eq_pow_inner
      H N hN beta hbeta n
      (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
      (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  change
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
      H N beta n
      (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
      (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) = _
  rw [hAmp]
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
  change
    inner ℝ
      (((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta) ^ n)
        (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
      (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
    inner ℝ
      ((((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta) ^ n) f :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
      (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_pow_coe]

/-- Combining #2061 with the transfer/path theorem removes the temporal-link field and identifies
the complete unfixed positive-half endpoint amplitude directly with the physical transfer power.
The terminal residual is still absorbed only through the Gauss-law hypothesis. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_unfixed_iteratedHaar_integral_eq_physicalTransfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (∫ U,
      (∫ path,
        (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
            H N beta path U *
          (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N))
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure H N)) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta f) g := by
  calc
    _ = ∫ path,
        (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta path *
          (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
      exact
        periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_iteratedHaar_integral_eq_temporalGauge
          H N beta
          (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
          (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
          g.property
    _ = _ :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_temporalGauge_integral_eq_physicalTransfer
        H N hN beta hbeta f g

end

end MathlibAnalytic
end MGAP4D
