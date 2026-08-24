import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairObservablePhysicalDescent
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfTransferPathIteration
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000

local instance pairObservableIntegralRepresentativeSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance pairObservableIntegralRepresentativeSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance pairObservableIntegralRepresentativeSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance pairObservableIntegralRepresentativeSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance pairObservableIntegralRepresentativeSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance pairObservableIntegralRepresentativeSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance pairObservableIntegralRepresentativeSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The left state times the actual observable-weighted one-slab kernel is
integrable on the two-boundary product Haar space. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedLeft_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        f p.1 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 * b p)
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  have hf1 : Integrable (fun A => f A) μ := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp f).mono_exponent (by norm_num)
  have hbase : Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => f p.1)
      (μ.prod μ) := hf1.comp_fst μ
  have hfactorMeas : AEStronglyMeasurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 * b p)
      (μ.prod μ) :=
    ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).mul b.continuous).aestronglyMeasurable
  have hmajor : Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        ‖b‖ * f p.1) (μ.prod μ) := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.smul ‖b‖
  have hmeas : AEStronglyMeasurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        f p.1 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 * b p)
      (μ.prod μ) := by
    simpa [mul_assoc] using
      (hbase.aestronglyMeasurable.mul hfactorMeas)
  apply hmajor.mono hmeas
  filter_upwards with p
  have hk :
      |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2| ≤ 1 :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H N hN beta hbeta p.1 p.2
  have hb : |b p| ≤ ‖b‖ := by
    simpa [Real.norm_eq_abs] using b.norm_coe_le_norm p
  change
    |f p.1 *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2 * b p| ≤
      |‖b‖ * f p.1|
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (norm_nonneg b)]
  calc
    |f p.1| *
        |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2| * |b p| ≤
      |f p.1| * 1 * ‖b‖ := by gcongr
    _ = ‖b‖ * |f p.1| := by ring

/-- Conditional Haar integral representative of the observable-weighted
one-slab operator. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentative
    (H N : ℕ)
    (beta : ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ∫ A,
    f A *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B *
      b (A, B)
    ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

/-- The conditional observable-weighted Haar integral is an actual `L²`
function of the outgoing boundary. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentative_memLp
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentative
        H N beta b f)
      2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let F := fun p :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      f p.1 *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2 * b p
  have hF : Integrable F (μ.prod μ) := by
    simpa [μ, F] using
      periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableWeightedLeft_integrable
        H N hN beta hbeta b f
  have hf1 : Integrable (fun A => f A) μ := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp f).mono_exponent (by norm_num)
  have hnormf : Integrable (fun A => ‖f A‖) μ := hf1.norm
  have hmajor : Integrable (fun A => ‖b‖ * ‖f A‖) μ := by
    simpa [Pi.smul_apply, smul_eq_mul] using hnormf.smul ‖b‖
  have hrepInt : Integrable (fun B => ∫ A, F (A, B) ∂μ) μ := hF.integral_prod_right
  apply MemLp.of_bound hrepInt.aestronglyMeasurable
    (∫ A, ‖b‖ * ‖f A‖ ∂μ)
  filter_upwards [hF.prod_left_ae] with B hB
  change
    ‖∫ A,
        f A *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B *
          b (A, B) ∂μ‖ ≤
      ∫ A, ‖b‖ * ‖f A‖ ∂μ
  calc
    ‖∫ A,
        f A *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B *
          b (A, B) ∂μ‖ ≤
      ∫ A, ‖f A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B *
        b (A, B)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ A, ‖b‖ * ‖f A‖ ∂μ := by
      apply integral_mono_ae hB.norm hmajor
      filter_upwards with A
      have hk :
          |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A B| ≤ 1 :=
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
          H N hN beta hbeta A B
      have hb : |b (A, B)| ≤ ‖b‖ := by
        simpa [Real.norm_eq_abs] using b.norm_coe_le_norm (A, B)
      change
        |f A *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B *
          b (A, B)| ≤ ‖b‖ * |f A|
      rw [abs_mul, abs_mul]
      calc
        |f A| *
            |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A B| * |b (A, B)| ≤
          |f A| * 1 * ‖b‖ := by gcongr
        _ = ‖b‖ * |f A| := by ring

/-- `L²` vector defined by the conditional observable-weighted Haar integral. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentative_memLp
    H N hN beta hbeta b f).toLp
      (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentative
        H N beta b f)

theorem periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralL2_coeFn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralL2
        H N hN beta hbeta b f =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentative
        H N beta b f :=
  (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentative_memLp
    H N hN beta hbeta b f).coeFn_toLp

/-- The conditional Haar-integral `L²` vector is exactly the Fréchet--Riesz
Hilbert--Schmidt pair-insertion operator. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralL2_eq_operator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralL2
        H N hN beta hbeta b f =
      periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
        H N hN beta hbeta b f := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  apply ext_inner_right ℝ
  intro g
  have hrep :=
    periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralL2_coeFn
      H N hN beta hbeta b f
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
        f p.1 * g p.2) (μ.prod μ) := hf1.mul_prod hg1
  have hKMeas : AEStronglyMeasurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2)
      (μ.prod μ) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).aestronglyMeasurable
  have hbMeas : AEStronglyMeasurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => b p)
      (μ.prod μ) :=
    b.continuous.aestronglyMeasurable
  have hmajor : Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        ‖b‖ * (f p.1 * g p.2)) (μ.prod μ) := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.smul ‖b‖
  have hAll : Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        f p.1 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 * b p * g p.2) (μ.prod μ) := by
    have hmeas : AEStronglyMeasurable
        (fun p :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          f p.1 *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta p.1 p.2 * b p * g p.2)
        (μ.prod μ) :=
      ((((Lp.aestronglyMeasurable f).comp_fst.mul hKMeas).mul hbMeas).mul
        (Lp.aestronglyMeasurable g).comp_snd)
    apply hmajor.mono hmeas
    filter_upwards with p
    have hk :
        |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2| ≤ 1 :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H N hN beta hbeta p.1 p.2
    have hb : |b p| ≤ ‖b‖ := by
      simpa [Real.norm_eq_abs] using b.norm_coe_le_norm p
    change
      |f p.1 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 * b p * g p.2| ≤
        |‖b‖ * (f p.1 * g p.2)|
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (norm_nonneg b)]
    calc
      |f p.1| *
          |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2| * |b p| * |g p.2| ≤
        |f p.1| * 1 * ‖b‖ * |g p.2| := by gcongr
      _ = ‖b‖ * |f p.1 * g p.2| := by
        rw [abs_mul]
        ring
  calc
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralL2
          H N hN beta hbeta b f) g =
      ∫ B,
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralL2
            H N hN beta hbeta b f B)
          (g B) ∂μ :=
      MeasureTheory.L2.inner_def
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralL2
          H N hN beta hbeta b f) g
    _ = ∫ B,
        (∫ A,
          f A *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B *
            b (A, B) ∂μ) * g B ∂μ := by
      apply integral_congr_ae
      filter_upwards [hrep] with B hB
      rw [hB, realL2Scalar_inner_eq_mul]
      rfl
    _ = ∫ p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        f p.1 *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 * b p * g p.2 ∂(μ.prod μ) := by
      rw [MeasureTheory.integral_prod_symm _ hAll]
      apply integral_congr_ae
      filter_upwards with B
      rw [integral_mul_const]
    _ = inner ℝ
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b f) g := by
      symm
      simpa [μ] using
        periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_inner_eq_integral
          H N hN beta hbeta b f g

/-- Pointwise almost-everywhere realization of the abstract pair-insertion
operator as its conditional one-boundary Haar integral. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_coeFn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
        H N hN beta hbeta b f =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentative
        H N beta b f := by
  rw [← periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralL2_eq_operator
    H N hN beta hbeta b f]
  exact
    periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralL2_coeFn
      H N hN beta hbeta b f

/-- Concrete pointwise representative for insertion of the temporal crossing
Wilson action into one slab. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabTemporalCrossingActionOperator_coeFn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryOneSlabTemporalCrossingActionOperator
        H N hN beta hbeta f =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      fun B =>
        ∫ A,
          f A *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A B
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  simpa [periodicHypercubicEvenSpecialUnitaryOneSlabTemporalCrossingActionOperator,
    periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentative] using
    (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_coeFn
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable H N)
      f)

/-- Audit-visible receipt for the conditional integral representation of every
bounded adjacent-slice insertion. -/
structure PeriodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentationPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  coeFn :
    ∀ (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
      (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)),
      periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b f =ᵐ[
            periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
        periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentative
          H N beta b f

/-- Construct the conditional pair-insertion integral-representation package. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentationPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentationPackage
      H N hN beta hbeta :=
  { coeFn := periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_coeFn
      H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
