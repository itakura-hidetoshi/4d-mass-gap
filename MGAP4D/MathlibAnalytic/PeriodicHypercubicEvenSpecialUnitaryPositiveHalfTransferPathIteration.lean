import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfHaarTemporalGaugeReduction
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000

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

abbrev PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath
    (H N n : ℕ) : Type :=
  Fin (n + 1) → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N

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

noncomputable def periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
    (H N : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n) : ℝ :=
  ∏ i : Fin n,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
      (path i.castSucc) (path i.succ)

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

/-- Generic finite nearest-neighbour path kernels are measurable as soon as the one-step kernel
is measurable on the product space.  Keeping the carrier abstract prevents concrete finite
`SU(N)` product types from entering finite-product measurability elaboration. -/
private theorem finitePathKernel_measurable
    {X : Type*}
    [MeasurableSpace X]
    (K : X × X → ℝ)
    (hK : Measurable K)
    (n : ℕ) :
    Measurable
      (fun path : Fin (n + 1) → X =>
        ∏ i : Fin n, K (path i.castSucc, path i.succ)) := by
  classical
  apply (Finset.univ : Finset (Fin n)).measurable_prod
  intro i _hi
  exact hK.comp
    ((measurable_pi_apply i.castSucc).prodMk (measurable_pi_apply i.succ))

/-- A finite product of one-step kernels bounded in absolute value by one is itself bounded by
one.  This is the abstract majorization used by the path-integral recursion. -/
private theorem finitePathKernel_abs_le_one
    {X : Type*}
    (K : X × X → ℝ)
    (hK : ∀ p, |K p| ≤ 1)
    (n : ℕ)
    (path : Fin (n + 1) → X) :
    |∏ i : Fin n, K (path i.castSucc, path i.succ)| ≤ 1 := by
  classical
  have habs :
      |∏ i : Fin n, K (path i.castSucc, path i.succ)| =
        ∏ i : Fin n, |K (path i.castSucc, path i.succ)| := by
    simpa using
      (Finset.abs_prod (Finset.univ : Finset (Fin n))
        (fun i : Fin n => K (path i.castSucc, path i.succ)))
  rw [habs]
  calc
    (∏ i : Fin n, |K (path i.castSucc, path i.succ)|) ≤
        ∏ _i : Fin n, (1 : ℝ) := by
      exact Finset.prod_le_prod
        (fun _ _ => abs_nonneg _)
        (fun i _ => hK (path i.castSucc, path i.succ))
    _ = 1 := by simp

theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel_abs_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n) :
    |periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
        H N beta n path| ≤ 1 := by
  unfold periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
  apply finitePathKernel_abs_le_one
  intro p
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H N hN beta hbeta p.1 p.2

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
  change
    |f p.1 * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta p.1 p.2| ≤ |f p.1|
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_left hk (abs_nonneg (f p.1))

noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
    (H N : ℕ)
    (beta : ℝ)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ∫ A,
    f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B
    ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

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
      simpa using
        mul_le_mul_of_nonneg_left
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
            H N hN beta hbeta A B)
          (abs_nonneg (f A))

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
      rw [show K p =
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 by simpa [K] using hpK]
      rw [show tensor p = f p.1 * g p.2 by
        simpa [tensor, realL2ExternalTensorFunction] using hpfg]
      rw [realL2Scalar_inner_eq_mul]
      ring

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
    change
      |f p.1 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 * g p.2| ≤
        |f p.1 * g p.2|
    rw [abs_mul, abs_mul, abs_mul]
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

theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude_zero
    (H N : ℕ)
    (beta : ℝ)
    (f g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
        H N beta 0 f g = inner ℝ f g := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  have hfg : AEStronglyMeasurable (fun A => f A * g A) μ :=
    (Lp.aestronglyMeasurable f).mul (Lp.aestronglyMeasurable g)
  have heval :
      (∫ path : Fin 1 → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        f (path 0) * g (path 0) ∂(Measure.pi (fun _ : Fin 1 => μ))) =
        ∫ A, f A * g A ∂μ := by
    simpa using
      (MeasureTheory.integral_comp_eval
        (μ := fun _ : Fin 1 => μ) (i := (0 : Fin 1)) hfg)
  calc
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
        H N beta 0 f g =
      ∫ path : Fin 1 → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        f (path 0) * g (path 0) ∂(Measure.pi (fun _ : Fin 1 => μ)) := by
      simp [periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude,
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel,
        periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure, μ]
    _ = ∫ A, f A * g A ∂μ := heval
    _ = inner ℝ f g := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards with A
      rw [realL2Scalar_inner_eq_mul]

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

private noncomputable def periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSplitIntegrand
    (H N : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (f g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n) : ℝ :=
  (f p.1 * g (p.2 (Fin.last n))) *
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta p.1 (p.2 0) *
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
        H N beta n p.2)

/-- Abstract bounded-measurable-kernel majorization for the Fubini split.  All expensive concrete
`SU(N)` carrier structure is absent here; only probability normalization, endpoint `L²`,
measurability, and the pointwise kernel bound are used. -/
private theorem boundedMeasurableKernel_splitIntegrand_integrable
    {X : Type*}
    [MeasurableSpace X]
    (μ : Measure X)
    [IsProbabilityMeasure μ]
    (K : X × X → ℝ)
    (hKmeas : Measurable K)
    (hKbound : ∀ p, |K p| ≤ 1)
    (n : ℕ)
    (f g : Lp ℝ 2 μ) :
    Integrable
      (fun p : X × (Fin (n + 1) → X) =>
        (f p.1 * g (p.2 (Fin.last n))) *
          (K (p.1, p.2 0) *
            ∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)))
      (μ.prod (Measure.pi (fun _ : Fin (n + 1) => μ))) := by
  have hf1 : Integrable (fun x => f x) μ := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp f).mono_exponent (by norm_num)
  have hg1 : Integrable (fun x => g x) μ := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp g).mono_exponent (by norm_num)
  have hgtail : Integrable
      (fun tail : Fin (n + 1) → X => g (tail (Fin.last n)))
      (Measure.pi (fun _ : Fin (n + 1) => μ)) :=
    MeasureTheory.integrable_comp_eval
      (μ := fun _ : Fin (n + 1) => μ) (i := Fin.last n) hg1
  have hbase : Integrable
      (fun p : X × (Fin (n + 1) → X) =>
        f p.1 * g (p.2 (Fin.last n)))
      (μ.prod (Measure.pi (fun _ : Fin (n + 1) => μ))) :=
    hf1.mul_prod hgtail
  have hpair : Measurable
      (fun p : X × (Fin (n + 1) → X) => (p.1, p.2 0)) :=
    measurable_fst.prodMk
      ((measurable_pi_apply (0 : Fin (n + 1))).comp measurable_snd)
  have hKfirst : Measurable
      (fun p : X × (Fin (n + 1) → X) => K (p.1, p.2 0)) :=
    hKmeas.comp hpair
  have hKtail : Measurable
      (fun p : X × (Fin (n + 1) → X) =>
        ∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)) :=
    (finitePathKernel_measurable K hKmeas n).comp measurable_snd
  have hkernel : AEStronglyMeasurable
      (fun p : X × (Fin (n + 1) → X) =>
        K (p.1, p.2 0) *
          ∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ))
      (μ.prod (Measure.pi (fun _ : Fin (n + 1) => μ))) :=
    (hKfirst.mul hKtail).aestronglyMeasurable
  apply hbase.mono (hbase.aestronglyMeasurable.mul hkernel)
  filter_upwards with p
  have hk1 := hKbound (p.1, p.2 0)
  have hkn := finitePathKernel_abs_le_one K hKbound n p.2
  have hkprod :
      |K (p.1, p.2 0) *
        ∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)| ≤ 1 := by
    rw [abs_mul]
    calc
      |K (p.1, p.2 0)| *
          |∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)| ≤ 1 * 1 :=
        mul_le_mul hk1 hkn (abs_nonneg _) zero_le_one
      _ = 1 := by norm_num
  change
    |(f p.1 * g (p.2 (Fin.last n))) *
      (K (p.1, p.2 0) *
        ∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ))| ≤
      |f p.1 * g (p.2 (Fin.last n))|
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hkprod (abs_nonneg _)

private theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude_split
    (H N : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (f g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
        H N beta (n + 1) f g =
      ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSplitIntegrand
          H N beta n f g p
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)) := by
  classical
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let tailμ := periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n
  let μs : Fin (n + 2) → Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) := fun _ => μ
  have hMP := MeasureTheory.measurePreserving_piFinSuccAbove μs (0 : Fin (n + 2))
  unfold periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
  change
    (∫ path : Fin (n + 2) → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      f (path 0) *
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
          H N beta (n + 1) path *
        g (path (Fin.last (n + 1))) ∂(Measure.pi μs)) =
      ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSplitIntegrand
          H N beta n f g p ∂(μ.prod tailμ)
  rw [← hMP.symm.integral_comp']
  apply integral_congr_ae
  filter_upwards with p
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq]
  rw [periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel_cons]
  simp [periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSplitIntegrand,
    Fin.cons_zero]
  ring

private theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSplitIntegral_fubini
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    (∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSplitIntegrand
          H N beta n f g p
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n))) =
      ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
            H N beta f (tail 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail *
          g (tail (Fin.last n))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let K :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun p =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta p.1 p.2
  have hKmeas : Measurable K := by
    exact
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        H N beta).measurable
  have hKbound : ∀ p, |K p| ≤ 1 := by
    intro p
    exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H N hN beta hbeta p.1 p.2
  have hsplit0 :=
    boundedMeasurableKernel_splitIntegrand_integrable
      μ K hKmeas hKbound n f g
  have hsplit : Integrable
      (periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSplitIntegrand
        H N beta n f g)
      (μ.prod (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)) := by
    simpa [K, μ,
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSplitIntegrand,
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel,
      periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure] using hsplit0
  rw [MeasureTheory.integral_prod_symm _ hsplit]
  apply integral_congr_ae
  filter_upwards with tail
  calc
    (∫ A,
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSplitIntegrand
        H N beta n f g (A, tail) ∂μ) =
      ∫ A,
        (f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A (tail 0)) *
          (g (tail (Fin.last n)) *
            periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
              H N beta n tail) ∂μ := by
        apply integral_congr_ae
        filter_upwards with A
        simp [periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSplitIntegrand]
        ring
    _ = (∫ A,
          f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A (tail 0) ∂μ) *
        (g (tail (Fin.last n)) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail) := by
      rw [integral_mul_const]
    _ = periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
          H N beta f (tail 0) *
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
          H N beta n tail *
        g (tail (Fin.last n)) := by
      unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
      ring

private theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeRepresentativeIntegral_eq_transfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    (∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
          H N beta f (tail 0) *
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
          H N beta n tail *
        g (tail (Fin.last n))
      ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)) =
      ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H N hN beta hbeta f) (tail 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail *
          g (tail (Fin.last n))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let tailμ := periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n
  have hTf :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_coeFn
      H N hN beta hbeta f
  have hTfTail :
      (fun tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) (tail 0)) =ᵐ[tailμ]
      (fun tail =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
          H N beta f (tail 0)) := by
    simpa [tailμ, periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure] using
      ((MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin (n + 1) => μ) (0 : Fin (n + 1))).quasiMeasurePreserving.ae_eq hTf)
  apply integral_congr_ae
  filter_upwards [hTfTail] with tail htail
  rw [htail]

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
  calc
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
        H N beta (n + 1) f g =
      ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSplitIntegrand
          H N beta n f g p
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)) :=
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude_split
        H N beta n f g
    _ = ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
            H N beta f (tail 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail *
          g (tail (Fin.last n))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n) :=
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSplitIntegral_fubini
        H N hN beta hbeta n f g
    _ = ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H N hN beta hbeta f) (tail 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail *
          g (tail (Fin.last n))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n) :=
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeRepresentativeIntegral_eq_transfer
        H N hN beta hbeta n f g
    _ = periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
        H N beta n
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) g := by
      rfl

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
  induction n generalizing f with
  | zero =>
      simpa using
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude_zero
          H N beta f g
  | succ n ih =>
      rw [periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude_succ
        H N hN beta hbeta n f g]
      rw [ih]
      rw [pow_succ]
      simp [ContinuousLinearMap.mul_def]

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