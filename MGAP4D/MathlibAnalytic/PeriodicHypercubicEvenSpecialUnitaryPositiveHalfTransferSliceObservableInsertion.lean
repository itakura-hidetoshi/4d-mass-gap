import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySpatialWilsonActionInsertion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfTransferPathIteration
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000

local instance transferSliceInsertionSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance transferSliceInsertionSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance transferSliceInsertionSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance transferSliceInsertionSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance transferSliceInsertionSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance transferSliceInsertionSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance transferSliceInsertionSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Actual `n`-slab Haar path integral with a bounded one-slice observable
inserted at the spatial slice `j`.  No transfer-operator statement is built
into this definition. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableAmplitude
    (H N : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (j : Fin (n + 1))
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) : ℝ :=
  ∫ path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
    f (path 0) *
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
        H N beta n path *
      a (path j) *
      g (path (Fin.last n))
    ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)

/-- At the initial slice, literal observable insertion is exactly endpoint
amplitude with the bounded multiplication operator applied to the left state. -/
theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableAmplitude_zero
    (H N : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableAmplitude
        H N beta n 0 a f g =
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
        H N beta n
        (periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator
          H N a f) g := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let pathμ := periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n
  have hM :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2_coeFn
      H N a f
  have hM0 :
      (fun path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator
          H N a f (path 0)) =ᵐ[pathμ]
      (fun path => a (path 0) * f (path 0)) := by
    simpa [pathμ, periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure] using
      ((MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin (n + 1) => μ) (0 : Fin (n + 1))).quasiMeasurePreserving.ae_eq hM)
  unfold periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableAmplitude
  unfold periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
  apply integral_congr_ae
  filter_upwards [hM0] with path hpath
  rw [hpath]
  ring

private theorem transferSliceFinitePathKernel_measurable
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

private theorem transferSliceFinitePathKernel_abs_le_one
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

private theorem transferSlicePathKernel_cons
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

private noncomputable def periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableSplitIntegrand
    (H N : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (j : Fin (n + 1))
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n) : ℝ :=
  (f p.1 * g (p.2 (Fin.last n))) *
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta p.1 (p.2 0) *
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
        H N beta n p.2 *
      a (p.2 j))

private theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableSplitIntegrand_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (j : Fin (n + 1))
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    Integrable
      (periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableSplitIntegrand
        H N beta n j a f g)
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
        (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let tailμ := periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n
  let K :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun p =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
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
  have hKmeas : Measurable K := by
    exact
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
    (transferSliceFinitePathKernel_measurable K hKmeas n).comp measurable_snd
  have haTail : Measurable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n => a (p.2 j)) :=
    a.continuous.measurable.comp
      ((measurable_pi_apply j).comp measurable_snd)
  have hfactorMeas : AEStronglyMeasurable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        K (p.1, p.2 0) *
          (∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)) *
          a (p.2 j)) (μ.prod tailμ) :=
    ((hKfirst.mul hKtail).mul haTail).aestronglyMeasurable
  have hmajor : Integrable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        ‖a‖ * (f p.1 * g (p.2 (Fin.last n)))) (μ.prod tailμ) := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.smul ‖a‖
  apply hmajor.mono
    (hbase.aestronglyMeasurable.mul hfactorMeas)
  filter_upwards with p
  have hk1 : |K (p.1, p.2 0)| ≤ 1 :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H N hN beta hbeta p.1 (p.2 0)
  have hkn :
      |∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)| ≤ 1 :=
    transferSliceFinitePathKernel_abs_le_one
      K
      (fun q =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
          H N hN beta hbeta q.1 q.2)
      n p.2
  have hkprod :
      |K (p.1, p.2 0) *
        ∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)| ≤ 1 := by
    rw [abs_mul]
    calc
      |K (p.1, p.2 0)| *
          |∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)| ≤ 1 * 1 :=
        mul_le_mul hk1 hkn (abs_nonneg _) zero_le_one
      _ = 1 := by norm_num
  have ha : |a (p.2 j)| ≤ ‖a‖ := by
    simpa [Real.norm_eq_abs] using a.norm_coe_le_norm (p.2 j)
  have hfac :
      |K (p.1, p.2 0) *
          (∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)) *
          a (p.2 j)| ≤ ‖a‖ := by
    rw [abs_mul]
    calc
      |K (p.1, p.2 0) *
          ∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)| * |a (p.2 j)| ≤
        1 * ‖a‖ :=
          mul_le_mul hkprod ha (abs_nonneg _) zero_le_one
      _ = ‖a‖ := by simp
  change
    |(f p.1 * g (p.2 (Fin.last n))) *
      (K (p.1, p.2 0) *
        (∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)) * a (p.2 j))| ≤
      |‖a‖ * (f p.1 * g (p.2 (Fin.last n)))|
  calc
    |(f p.1 * g (p.2 (Fin.last n))) *
        (K (p.1, p.2 0) *
          (∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)) * a (p.2 j))| =
      |f p.1 * g (p.2 (Fin.last n))| *
        |K (p.1, p.2 0) *
          (∏ i : Fin n, K (p.2 i.castSucc, p.2 i.succ)) * a (p.2 j)| := by
      rw [abs_mul]
    _ ≤ |f p.1 * g (p.2 (Fin.last n))| * ‖a‖ :=
      mul_le_mul_of_nonneg_left hfac (abs_nonneg _)
    _ = ‖a‖ * |f p.1 * g (p.2 (Fin.last n))| := by ring
    _ = |‖a‖ * (f p.1 * g (p.2 (Fin.last n)))| := by
      rw [abs_mul, abs_of_nonneg (norm_nonneg a)]

private theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableAmplitude_split
    (H N : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (j : Fin (n + 1))
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableAmplitude
        H N beta (n + 1) j.succ a f g =
      ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableSplitIntegrand
          H N beta n j a f g p
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)) := by
  classical
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let tailμ := periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n
  let μs : Fin (n + 2) → Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) := fun _ => μ
  have hMP := MeasureTheory.measurePreserving_piFinSuccAbove μs (0 : Fin (n + 2))
  unfold periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableAmplitude
  change
    (∫ path : Fin (n + 2) → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      f (path 0) *
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
          H N beta (n + 1) path *
        a (path j.succ) *
        g (path (Fin.last (n + 1))) ∂(Measure.pi μs)) =
      ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableSplitIntegrand
          H N beta n j a f g p ∂(μ.prod tailμ)
  rw [← hMP.symm.integral_comp']
  apply integral_congr_ae
  filter_upwards with p
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq]
  rw [transferSlicePathKernel_cons]
  simp [periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableSplitIntegrand,
    Fin.cons_zero, Fin.cons_succ]
  ring

private theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableSplitIntegral_fubini
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (j : Fin (n + 1))
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    (∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableSplitIntegrand
          H N beta n j a f g p
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n))) =
      ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
            H N beta f (tail 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail *
          a (tail j) *
          g (tail (Fin.last n))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  have hsplit :=
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableSplitIntegrand_integrable
      H N hN beta hbeta n j a f g
  rw [MeasureTheory.integral_prod_symm _ hsplit]
  apply integral_congr_ae
  filter_upwards with tail
  calc
    (∫ A,
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableSplitIntegrand
        H N beta n j a f g (A, tail) ∂μ) =
      ∫ A,
        (f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A (tail 0)) *
          (periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
              H N beta n tail * a (tail j) * g (tail (Fin.last n))) ∂μ := by
        apply integral_congr_ae
        filter_upwards with A
        simp [periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableSplitIntegrand]
        ring
    _ = (∫ A,
          f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A (tail 0) ∂μ) *
        (periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail * a (tail j) * g (tail (Fin.last n))) := by
      rw [integral_mul_const]
    _ = periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
          H N beta f (tail 0) *
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
          H N beta n tail *
        a (tail j) *
        g (tail (Fin.last n)) := by
      unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
      ring

private theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableRepresentativeIntegral_eq_transfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (j : Fin (n + 1))
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    (∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
          H N beta f (tail 0) *
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
          H N beta n tail *
        a (tail j) *
        g (tail (Fin.last n))
      ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)) =
      ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H N hN beta hbeta f) (tail 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail *
          a (tail j) *
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

/-- Moving the observable one slice away from the initial boundary commutes
with the first Fubini integration: the left state is advanced by one actual
one-slab transfer, while the insertion remains on the corresponding tail
slice. -/
theorem periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableAmplitude_succ
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (j : Fin (n + 1))
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableAmplitude
        H N beta (n + 1) j.succ a f g =
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableAmplitude
        H N beta n j a
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) g := by
  calc
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableAmplitude
        H N beta (n + 1) j.succ a f g =
      ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableSplitIntegrand
          H N beta n j a f g p
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n)) :=
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableAmplitude_split
        H N beta n j a f g
    _ = ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative
            H N beta f (tail 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail *
          a (tail j) *
          g (tail (Fin.last n))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n) :=
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableSplitIntegral_fubini
        H N hN beta hbeta n j a f g
    _ = ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H N hN beta hbeta f) (tail 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta n tail *
          a (tail j) *
          g (tail (Fin.last n))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n) :=
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableRepresentativeIntegral_eq_transfer
        H N hN beta hbeta n j a f g
    _ = periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableAmplitude
        H N beta n j a
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) g := by
      rfl

/-- Canonical slice index having `left` slabs before the insertion and `right`
slabs after it. -/
def periodicHypercubicEvenSpecialUnitaryTransferSliceIndex
    (left right : ℕ) : Fin (left + right + 1) :=
  ⟨left, by omega⟩

/-- Same actual inserted path integral, parametrized by the number of slabs to
the left and right of the observable.  This avoids any subtraction in the
transfer-power formula. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude
    (H N : ℕ)
    (beta : ℝ)
    (left right : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableAmplitude
    H N beta (left + right)
    (periodicHypercubicEvenSpecialUnitaryTransferSliceIndex left right) a f g

private theorem periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude_zero_left
    (H N : ℕ)
    (beta : ℝ)
    (right : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude
        H N beta 0 right a f g =
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude
        H N beta right
        (periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator
          H N a f) g := by
  unfold periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude
  convert
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableAmplitude_zero
      H N beta right a f g using 1 <;>
    simp [periodicHypercubicEvenSpecialUnitaryTransferSliceIndex]

private theorem periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude_succ_left
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude
        H N beta (Nat.succ left) right a f g =
      periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude
        H N beta left right a
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) g := by
  unfold periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude
  convert
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableAmplitude_succ
      H N hN beta hbeta (left + right)
      (periodicHypercubicEvenSpecialUnitaryTransferSliceIndex left right) a f g using 1 <;>
    simp [periodicHypercubicEvenSpecialUnitaryTransferSliceIndex, Nat.succ_add] <;>
    omega

/-- Exact arbitrary-slice transfer formula on the full Haar `L²` carrier.
With `left` slabs before and `right` slabs after the insertion, the actual
path integral is the matrix coefficient of `T^right M_a T^left`. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude_eq_pow_inner
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude
        H N beta left right a f g =
      inner ℝ
        (((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
              H N hN beta hbeta) ^ right)
          (periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator
            H N a
            (((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
                H N hN beta hbeta) ^ left) f))) g := by
  induction left generalizing f with
  | zero =>
      rw [periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude_zero_left]
      rw [periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude_eq_pow_inner
        H N hN beta hbeta]
      simp
  | succ left ih =>
      rw [periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude_succ_left
        H N hN beta hbeta]
      simpa [pow_succ, ContinuousLinearMap.mul_def] using
        ih (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f)

/-- Physical Gauss-law operator representing a bounded gauge-invariant
observable inserted after `left` and before `right` one-slab transfers. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta) ^ right).comp
    ((periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator
        H N a ha).comp
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta) ^ left))

/-- Forgetting Gauss-law subtype coercions identifies the physical insertion
operator with the literal full-Haar expression `T^right M_a T^left`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator_coe
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator
        H N hN beta hbeta left right a ha f :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta) ^ right)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator
          H N a
          (((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
              H N hN beta hbeta) ^ left)
            (f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator
  simp only [ContinuousLinearMap.comp_apply]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_pow_coe
    H N hN beta hbeta right]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator_coe]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_pow_coe
    H N hN beta hbeta left]

/-- The physical Gauss-law matrix coefficient of the arbitrary-slice
insertion operator is exactly the actual finite Haar path integral. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator_inner_eq_amplitude
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator
          H N hN beta hbeta left right a ha f) g =
      periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude
        H N beta left right a
        (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
        (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  rw [periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude_eq_pow_inner
    H N hN beta hbeta]
  change
    inner ℝ
      ((periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator
          H N hN beta hbeta left right a ha f :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
      (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) = _
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator_coe]

/-- Concrete arbitrary-slice operator obtained by inserting the actual
intrinsic spatial Wilson action. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator
    H N hN beta hbeta left right
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable H N)
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable_gaugeInvariant
      H N)

/-- Exact finite Wilson generator at an arbitrary transfer slice: its physical
matrix coefficient is literally the actual `left + right` slab Haar path
integral with `S_spatial` inserted at slice `left`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionOperator_inner_eq_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionOperator
          H N hN beta hbeta left right f) g =
      ∫ path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N (left + right),
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) (path 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta (left + right) path *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
            (path (periodicHypercubicEvenSpecialUnitaryTransferSliceIndex left right)) *
          (g : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            (path (Fin.last (left + right)))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure
          H N (left + right)) := by
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionOperator,
    periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude,
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeSliceObservableAmplitude] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator_inner_eq_amplitude
        H N hN beta hbeta left right
        (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable H N)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable_gaugeInvariant
          H N) f g)

/-- Audit-visible receipt for the arbitrary-slice finite Wilson insertion
bridge.  No continuum or full approximating-OS Hilbert identification is
asserted here. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ) : Prop where
  pairing :
    ∀ f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionOperator
            H N hN beta hbeta left right f) g =
        ∫ path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N (left + right),
          (f : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) (path 0) *
            periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
              H N beta (left + right) path *
            periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
              (path (periodicHypercubicEvenSpecialUnitaryTransferSliceIndex left right)) *
            (g : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              (path (Fin.last (left + right)))
          ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure
            H N (left + right))

/-- Construct the arbitrary-slice finite Wilson insertion package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionPackage
      H N hN beta hbeta left right :=
  { pairing :=
      periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionOperator_inner_eq_integral
        H N hN beta hbeta left right }

end

end MathlibAnalytic
end MGAP4D