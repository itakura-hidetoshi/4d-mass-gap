import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentative
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfTransferSliceObservableInsertion
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000

local instance transferSlabPairInsertionSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance transferSlabPairInsertionSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance transferSlabPairInsertionSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance transferSlabPairInsertionSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance transferSlabPairInsertionSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance transferSlabPairInsertionSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance transferSlabPairInsertionSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Actual `n`-slab Haar path integral with a bounded adjacent-slice observable
inserted on slab `j`.  The inserted factor sees precisely the two endpoints of
that slab; no transfer-operator identity is built into the definition. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
    (H N : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (j : Fin n)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) : ℝ :=
  ∫ path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
    f (path 0) *
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
        H N beta n path *
      b (path j.castSucc, path j.succ) *
      g (path (Fin.last n))
    ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)

private theorem transferSlabPairFinitePathKernel_measurable
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

private theorem transferSlabPairFinitePathKernel_abs_le_one
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

private theorem transferSlabPairPathKernel_cons
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

private noncomputable def periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableZeroSplitIntegrand
    (H N : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n) : ℝ :=
  (f p.1 * g (p.2 (Fin.last n))) *
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta p.1 (p.2 0) *
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
        H N beta n p.2 *
      b (p.1, p.2 0))

private theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableZeroSplitIntegrand_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    Integrable
      (periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableZeroSplitIntegrand
        H N beta n b f g)
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
        (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let tailμ := periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n
  let K :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun p => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta p.1 p.2
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
        (μ := fun _ : Fin (n + 1) => μ) (i := Fin.last n) hg1)
  have hbase : Integrable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        f p.1 * g (p.2 (Fin.last n))) (μ.prod tailμ) :=
    hf1.mul_prod hgtail
  have hKmeas : Measurable K :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).measurable
  have hKfirst : Measurable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        K (p.1, p.2 0)) :=
    hKmeas.comp
      (measurable_fst.prodMk
        ((measurable_pi_apply (0 : Fin (n + 1))).comp measurable_snd))
  have hKtail : Measurable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        ∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)) :=
    (transferSlabPairFinitePathKernel_measurable K hKmeas n).comp measurable_snd
  have hbfirst : Measurable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        b (p.1, p.2 0)) :=
    b.continuous.measurable.comp
      (measurable_fst.prodMk
        ((measurable_pi_apply (0 : Fin (n + 1))).comp measurable_snd))
  have hfactorMeas : AEStronglyMeasurable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        K (p.1, p.2 0) *
          (∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)) *
          b (p.1, p.2 0)) (μ.prod tailμ) :=
    ((hKfirst.mul hKtail).mul hbfirst).aestronglyMeasurable
  have hmajor : Integrable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        ‖b‖ * (f p.1 * g (p.2 (Fin.last n)))) (μ.prod tailμ) := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.smul ‖b‖
  apply hmajor.mono (hbase.aestronglyMeasurable.mul hfactorMeas)
  filter_upwards with p
  have hk1 : |K (p.1, p.2 0)| ≤ 1 :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H N hN beta hbeta p.1 (p.2 0)
  have hkn :
      |∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)| ≤ 1 :=
    transferSlabPairFinitePathKernel_abs_le_one K
      (fun q => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H N hN beta hbeta q.1 q.2) n p.2
  have hkprod :
      |K (p.1, p.2 0) *
        ∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)| ≤ 1 := by
    rw [abs_mul]
    calc
      |K (p.1, p.2 0)| *
          |∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)| ≤ 1 * 1 := by
        exact mul_le_mul hk1 hkn (abs_nonneg _) zero_le_one
      _ = 1 := by norm_num
  have hbnd : |b (p.1, p.2 0)| ≤ ‖b‖ := by
    simpa [Real.norm_eq_abs] using b.norm_coe_le_norm (p.1, p.2 0)
  have hfac :
      |K (p.1, p.2 0) *
          (∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)) *
          b (p.1, p.2 0)| ≤ ‖b‖ := by
    rw [abs_mul]
    calc
      |K (p.1, p.2 0) *
          ∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)| *
          |b (p.1, p.2 0)| ≤ 1 * ‖b‖ := by
        exact mul_le_mul hkprod hbnd (abs_nonneg _) zero_le_one
      _ = ‖b‖ := by simp
  change
    |(f p.1 * g (p.2 (Fin.last n))) *
      (K (p.1, p.2 0) *
        (∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)) * b (p.1, p.2 0))| ≤
      |‖b‖ * (f p.1 * g (p.2 (Fin.last n)))|
  calc
    _ = |f p.1 * g (p.2 (Fin.last n))| *
        |K (p.1, p.2 0) *
          (∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)) * b (p.1, p.2 0)| := by
      rw [abs_mul]
    _ ≤ |f p.1 * g (p.2 (Fin.last n))| * ‖b‖ :=
      mul_le_mul_of_nonneg_left hfac (abs_nonneg _)
    _ = ‖b‖ * |f p.1 * g (p.2 (Fin.last n))| := by ring
    _ = |‖b‖ * (f p.1 * g (p.2 (Fin.last n)))| := by
      symm
      rw [abs_mul, abs_of_nonneg (norm_nonneg b), abs_mul]

private theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude_zero_split
    (H N : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta (n + 1) 0 b f g =
      ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableZeroSplitIntegrand
          H N beta n b f g p
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)) := by
  classical
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let tailμ := periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n
  let μs : Fin (n + 2) → Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) := fun _ => μ
  have hMP := MeasureTheory.measurePreserving_piFinSuccAbove μs (0 : Fin (n + 2))
  unfold periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
  change
    (∫ path : Fin (n + 2) → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      f (path 0) *
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
          H N beta (n + 1) path *
        b (path (0 : Fin (n + 1)).castSucc, path (0 : Fin (n + 1)).succ) *
        g (path (Fin.last (n + 1))) ∂(Measure.pi μs)) = _
  rw [← hMP.symm.integral_comp']
  apply integral_congr_ae
  filter_upwards with p
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq]
  rw [transferSlabPairPathKernel_cons]
  simp [periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableZeroSplitIntegrand,
    Fin.cons_zero, Fin.cons_succ]
  ring

private theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableZeroSplitIntegral_fubini
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    (∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableZeroSplitIntegrand
          H N beta n b f g p
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n))) =
      ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentative
            H N beta b f (tail 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail *
          g (tail (Fin.last n))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  have hsplit :=
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableZeroSplitIntegrand_integrable
      H N hN beta hbeta n b f g
  rw [MeasureTheory.integral_prod_symm _ hsplit]
  apply integral_congr_ae
  filter_upwards with tail
  calc
    (∫ A,
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableZeroSplitIntegrand
        H N beta n b f g (A, tail) ∂μ) =
      ∫ A,
        (f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A (tail 0) * b (A, tail 0)) *
          (periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
              H N beta n tail * g (tail (Fin.last n))) ∂μ := by
        apply integral_congr_ae
        filter_upwards with A
        simp [periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableZeroSplitIntegrand]
        ring
    _ = (∫ A,
          f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A (tail 0) * b (A, tail 0) ∂μ) *
        (periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail * g (tail (Fin.last n))) := by
      rw [integral_mul_const]
    _ = periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentative
          H N beta b f (tail 0) *
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
          H N beta n tail * g (tail (Fin.last n)) := by
      unfold periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentative
      ring

private theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableZeroRepresentativeIntegral_eq_operator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    (∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
      periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentative
          H N beta b f (tail 0) *
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
          H N beta n tail * g (tail (Fin.last n))
      ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)) =
      ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
            H N hN beta hbeta b f) (tail 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail * g (tail (Fin.last n))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let tailμ := periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n
  have hTb :=
    periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_coeFn
      H N hN beta hbeta b f
  have hTbTail :
      (fun tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b f) (tail 0)) =ᵐ[tailμ]
      (fun tail =>
        periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentative
          H N beta b f (tail 0)) := by
    simpa [tailμ, periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure] using
      ((MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin (n + 1) => μ) (0 : Fin (n + 1))).quasiMeasurePreserving.ae_eq hTb)
  apply integral_congr_ae
  filter_upwards [hTbTail] with tail htail
  rw [htail]

/-- Insertion on the first slab is exactly endpoint propagation starting from
the one-slab pair-insertion operator applied to the left state. -/
theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta (n + 1) 0 b f g =
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
        H N beta n
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b f) g := by
  calc
    _ = ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableZeroSplitIntegrand
          H N beta n b f g p
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)) :=
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude_zero_split
        H N beta n b f g
    _ = ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentative
            H N beta b f (tail 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail * g (tail (Fin.last n))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n) :=
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableZeroSplitIntegral_fubini
        H N hN beta hbeta n b f g
    _ = ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
            H N hN beta hbeta b f) (tail 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail * g (tail (Fin.last n))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n) :=
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableZeroRepresentativeIntegral_eq_operator
        H N hN beta hbeta n b f g
    _ = periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
        H N beta n
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b f) g := by rfl

private noncomputable def periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableSuccSplitIntegrand
    (H N : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (j : Fin n)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n) : ℝ :=
  (f p.1 * g (p.2 (Fin.last n))) *
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta p.1 (p.2 0) *
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
        H N beta n p.2 *
      b (p.2 j.castSucc, p.2 j.succ))

private theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableSuccSplitIntegrand_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (j : Fin n)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    Integrable
      (periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableSuccSplitIntegrand
        H N beta n j b f g)
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
        (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let tailμ := periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n
  let K :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun p => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta p.1 p.2
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
        (μ := fun _ : Fin (n + 1) => μ) (i := Fin.last n) hg1)
  have hbase : Integrable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        f p.1 * g (p.2 (Fin.last n))) (μ.prod tailμ) :=
    hf1.mul_prod hgtail
  have hKmeas : Measurable K :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).measurable
  have hKfirst : Measurable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        K (p.1, p.2 0)) :=
    hKmeas.comp
      (measurable_fst.prodMk
        ((measurable_pi_apply (0 : Fin (n + 1))).comp measurable_snd))
  have hKtail : Measurable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        ∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)) :=
    (transferSlabPairFinitePathKernel_measurable K hKmeas n).comp measurable_snd
  have hbTail : Measurable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        b (p.2 j.castSucc, p.2 j.succ)) :=
    b.continuous.measurable.comp
      (((measurable_pi_apply j.castSucc).comp measurable_snd).prodMk
        ((measurable_pi_apply j.succ).comp measurable_snd))
  have hfactorMeas : AEStronglyMeasurable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        K (p.1, p.2 0) *
          (∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)) *
          b (p.2 j.castSucc, p.2 j.succ)) (μ.prod tailμ) :=
    ((hKfirst.mul hKtail).mul hbTail).aestronglyMeasurable
  have hmajor : Integrable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        ‖b‖ * (f p.1 * g (p.2 (Fin.last n)))) (μ.prod tailμ) := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.smul ‖b‖
  apply hmajor.mono (hbase.aestronglyMeasurable.mul hfactorMeas)
  filter_upwards with p
  have hk1 : |K (p.1, p.2 0)| ≤ 1 :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H N hN beta hbeta p.1 (p.2 0)
  have hkn :
      |∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)| ≤ 1 :=
    transferSlabPairFinitePathKernel_abs_le_one K
      (fun q => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H N hN beta hbeta q.1 q.2) n p.2
  have hkprod :
      |K (p.1, p.2 0) *
        ∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)| ≤ 1 := by
    rw [abs_mul]
    calc
      |K (p.1, p.2 0)| *
          |∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)| ≤ 1 * 1 := by
        exact mul_le_mul hk1 hkn (abs_nonneg _) zero_le_one
      _ = 1 := by norm_num
  have hbnd : |b (p.2 j.castSucc, p.2 j.succ)| ≤ ‖b‖ := by
    simpa [Real.norm_eq_abs] using b.norm_coe_le_norm (p.2 j.castSucc, p.2 j.succ)
  have hfac :
      |K (p.1, p.2 0) *
          (∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)) *
          b (p.2 j.castSucc, p.2 j.succ)| ≤ ‖b‖ := by
    rw [abs_mul]
    calc
      |K (p.1, p.2 0) *
          ∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)| *
          |b (p.2 j.castSucc, p.2 j.succ)| ≤ 1 * ‖b‖ := by
        exact mul_le_mul hkprod hbnd (abs_nonneg _) zero_le_one
      _ = ‖b‖ := by simp
  change
    |(f p.1 * g (p.2 (Fin.last n))) *
      (K (p.1, p.2 0) *
        (∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)) *
          b (p.2 j.castSucc, p.2 j.succ))| ≤
      |‖b‖ * (f p.1 * g (p.2 (Fin.last n)))|
  calc
    _ = |f p.1 * g (p.2 (Fin.last n))| *
        |K (p.1, p.2 0) *
          (∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)) *
            b (p.2 j.castSucc, p.2 j.succ)| := by rw [abs_mul]
    _ ≤ |f p.1 * g (p.2 (Fin.last n))| * ‖b‖ :=
      mul_le_mul_of_nonneg_left hfac (abs_nonneg _)
    _ = ‖b‖ * |f p.1 * g (p.2 (Fin.last n))| := by ring
    _ = |‖b‖ * (f p.1 * g (p.2 (Fin.last n)))| := by
      symm
      rw [abs_mul, abs_of_nonneg (norm_nonneg b), abs_mul]

private theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude_succ_split
    (H N : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (j : Fin n)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta (n + 1) j.succ b f g =
      ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableSuccSplitIntegrand
          H N beta n j b f g p
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)) := by
  classical
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let tailμ := periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n
  let μs : Fin (n + 2) → Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) := fun _ => μ
  have hMP := MeasureTheory.measurePreserving_piFinSuccAbove μs (0 : Fin (n + 2))
  unfold periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
  change
    (∫ path : Fin (n + 2) → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      f (path 0) *
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
          H N beta (n + 1) path *
        b (path j.succ.castSucc, path j.succ.succ) *
        g (path (Fin.last (n + 1))) ∂(Measure.pi μs)) = _
  rw [← hMP.symm.integral_comp']
  apply integral_congr_ae
  filter_upwards with p
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq]
  rw [transferSlabPairPathKernel_cons]
  simp [periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableSuccSplitIntegrand,
    Fin.cons_zero, Fin.cons_succ]
  ring

private theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableSuccSplitIntegral_fubini
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (j : Fin n)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    (∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableSuccSplitIntegrand
          H N beta n j b f g p
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n))) =
      ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
            H N beta f (tail 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail *
          b (tail j.castSucc, tail j.succ) *
          g (tail (Fin.last n))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  have hsplit :=
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableSuccSplitIntegrand_integrable
      H N hN beta hbeta n j b f g
  rw [MeasureTheory.integral_prod_symm _ hsplit]
  apply integral_congr_ae
  filter_upwards with tail
  calc
    (∫ A,
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableSuccSplitIntegrand
        H N beta n j b f g (A, tail) ∂μ) =
      ∫ A,
        (f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A (tail 0)) *
          (periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
              H N beta n tail * b (tail j.castSucc, tail j.succ) *
            g (tail (Fin.last n))) ∂μ := by
        apply integral_congr_ae
        filter_upwards with A
        simp [periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableSuccSplitIntegrand]
        ring
    _ = (∫ A,
          f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A (tail 0) ∂μ) *
        (periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail * b (tail j.castSucc, tail j.succ) *
          g (tail (Fin.last n))) := by
      rw [integral_mul_const]
    _ = periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
          H N beta f (tail 0) *
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
          H N beta n tail * b (tail j.castSucc, tail j.succ) *
        g (tail (Fin.last n)) := by
      unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
      ring

private theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableSuccRepresentativeIntegral_eq_transfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (j : Fin n)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    (∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
          H N beta f (tail 0) *
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
          H N beta n tail * b (tail j.castSucc, tail j.succ) *
        g (tail (Fin.last n))
      ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)) =
      ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H N hN beta hbeta f) (tail 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail * b (tail j.castSucc, tail j.succ) *
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

/-- Advancing the insertion one slab away from the initial boundary commutes
with the first ordinary Fubini integration: the left state is advanced by one
actual transfer while the pair insertion remains on the corresponding tail
slab. -/
theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude_succ
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (j : Fin n)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta (n + 1) j.succ b f g =
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta n j b
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) g := by
  calc
    _ = ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableSuccSplitIntegrand
          H N beta n j b f g p
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)) :=
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude_succ_split
        H N beta n j b f g
    _ = ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
            H N beta f (tail 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail * b (tail j.castSucc, tail j.succ) *
          g (tail (Fin.last n))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n) :=
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableSuccSplitIntegral_fubini
        H N hN beta hbeta n j b f g
    _ = ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H N hN beta hbeta f) (tail 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail * b (tail j.castSucc, tail j.succ) *
          g (tail (Fin.last n))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n) :=
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableSuccRepresentativeIntegral_eq_transfer
        H N hN beta hbeta n j b f g
    _ = periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta n j b
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) g := by rfl

/-- Canonical slab index with `left` ordinary slabs before the inserted slab and
`right` ordinary slabs after it. -/
def periodicHypercubicEvenSpecialUnitaryTransferSlabIndex
    (left right : ℕ) : Fin (left + right + 1) :=
  ⟨left, by omega⟩

/-- Actual path amplitude parametrized by the number of ordinary transfer
slabs before and after one adjacent-slice insertion. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude
    (H N : ℕ)
    (beta : ℝ)
    (left right : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
    H N beta (left + right + 1)
    (periodicHypercubicEvenSpecialUnitaryTransferSlabIndex left right) b f g

private theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude_cast
    (H N : ℕ)
    (beta : ℝ)
    {n m : ℕ}
    (h : n = m)
    (j : Fin n)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta n j b f g =
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta m (Fin.cast h j) b f g := by
  subst m
  rfl

private theorem periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude_zero_left
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (right : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude
        H N beta 0 right b f g =
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
        H N beta right
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b f) g := by
  unfold periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude
  let htotal : 0 + right + 1 = right + 1 := by omega
  let j0 := periodicHypercubicEvenSpecialUnitaryTransferSlabIndex 0 right
  let j0' : Fin (right + 1) := Fin.cast htotal j0
  have hj0 : j0' = (0 : Fin (right + 1)) := by
    apply Fin.ext
    rfl
  calc
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta (0 + right + 1) j0 b f g =
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta (right + 1) j0' b f g :=
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude_cast
        H N beta htotal j0 b f g
    _ = periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta (right + 1) 0 b f g := by rw [hj0]
    _ = periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
        H N beta right
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b f) g :=
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude_zero
        H N hN beta hbeta right b f g

private theorem periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude_succ_left
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude
        H N beta (Nat.succ left) right b f g =
      periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude
        H N beta left right b
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) g := by
  unfold periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude
  let htotal : Nat.succ left + right + 1 = (left + right + 1) + 1 := by omega
  let jSucc := periodicHypercubicEvenSpecialUnitaryTransferSlabIndex (Nat.succ left) right
  let jSucc' : Fin ((left + right + 1) + 1) := Fin.cast htotal jSucc
  let j := periodicHypercubicEvenSpecialUnitaryTransferSlabIndex left right
  have hjSucc : jSucc' = j.succ := by
    apply Fin.ext
    rfl
  calc
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta (Nat.succ left + right + 1) jSucc b f g =
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta ((left + right + 1) + 1) jSucc' b f g :=
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude_cast
        H N beta htotal jSucc b f g
    _ = periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta ((left + right + 1) + 1) j.succ b f g := by rw [hjSucc]
    _ = periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta (left + right + 1) j b
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) g :=
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude_succ
        H N hN beta hbeta (left + right + 1) j b f g

/-- Exact full-Haar transfer formula for a bounded adjacent-slice observable
inserted after `left` and before `right` ordinary one-slab transfers. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude_eq_pow_inner
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude
        H N beta left right b f g =
      inner ℝ
        (((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H N hN beta hbeta) ^ right)
          (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
            H N hN beta hbeta b
            (((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
                H N hN beta hbeta) ^ left) f))) g := by
  induction left generalizing f with
  | zero =>
      rw [periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude_zero_left
        H N hN beta hbeta]
      rw [periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude_eq_pow_inner
        H N hN beta hbeta]
      simp
  | succ left ih =>
      rw [periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude_succ_left
        H N hN beta hbeta]
      simpa [pow_succ, ContinuousLinearMap.mul_def] using
        ih (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f)

/-- Physical Gauss-law operator for a simultaneously gauge-invariant pair
observable inserted on an arbitrary transfer slab. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta) ^ right).comp
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairObservableOperator
        H N hN beta hbeta b hb).comp
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta) ^ left))

/-- Forgetting the Gauss-law subtype identifies the physical arbitrary-slab
insertion with the ambient expression `T^right T_b T^left`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator_coe
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator
        H N hN beta hbeta left right b hb f :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta) ^ right)
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b
          (((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
              H N hN beta hbeta) ^ left)
            (f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator
  simp only [ContinuousLinearMap.comp_apply]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_pow_coe
    H N hN beta hbeta right]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairObservableOperator_coe]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_pow_coe
    H N hN beta hbeta left]

/-- Physical matrix coefficients of the arbitrary-slab pair insertion are
exactly the actual finite Haar path amplitudes. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator_inner_eq_amplitude
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator
          H N hN beta hbeta left right b hb f) g =
      periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude
        H N beta left right b
        (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
        (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  rw [periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude_eq_pow_inner
    H N hN beta hbeta]
  change
    inner ℝ
      ((periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator
          H N hN beta hbeta left right b hb f :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
      (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) = _
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator_coe]

/-- Concrete physical arbitrary-slab operator obtained by inserting the actual
temporal-gauge crossing Wilson action. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator
    H N hN beta hbeta left right
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable H N)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable_gaugeInvariant
      H N)

/-- Exact time-like Wilson generator at an arbitrary transfer slab: its physical
matrix coefficient is literally the actual `(left + right + 1)`-slab Haar path
integral with the temporal crossing Wilson action inserted between slices
`left` and `left + 1`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionOperator_inner_eq_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionOperator
          H N hN beta hbeta left right f) g =
      ∫ path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath
          H N (left + right + 1),
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) (path 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta (left + right + 1) path *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N
            (path (periodicHypercubicEvenSpecialUnitaryTransferSlabIndex left right).castSucc)
            (path (periodicHypercubicEvenSpecialUnitaryTransferSlabIndex left right).succ) *
          (g : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            (path (Fin.last (left + right + 1)))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure
          H N (left + right + 1)) := by
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionOperator,
    periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude,
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator_inner_eq_amplitude
        H N hN beta hbeta left right
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable H N)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable_gaugeInvariant
          H N) f g)

/-- Audit-visible receipt for the arbitrary-transfer-slab realization of the
actual time-like Wilson crossing generator. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionInsertionPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ) : Prop where
  pairing :
    ∀ f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionOperator
            H N hN beta hbeta left right f) g =
        periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude
          H N beta left right
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable H N)
          (f : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
          (g : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  operatorFormula :
    periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionOperator
        H N hN beta hbeta left right =
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta) ^ right).comp
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTemporalCrossingActionOperator
          H N hN beta hbeta).comp
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ left))

/-- Construct the arbitrary-slab temporal-crossing insertion package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionInsertionPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionInsertionPackage
      H N hN beta hbeta left right :=
  { pairing := by
      intro f g
      simpa [periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionOperator]
        using
          (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator_inner_eq_amplitude
            H N hN beta hbeta left right
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable H N)
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable_gaugeInvariant
              H N) f g)
    operatorFormula := by
      rfl }

end

end MathlibAnalytic
end MGAP4D
