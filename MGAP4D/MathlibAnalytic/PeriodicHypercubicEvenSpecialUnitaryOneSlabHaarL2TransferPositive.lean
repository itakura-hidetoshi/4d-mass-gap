import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2Transfer
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtGramPositiveKernel
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

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

local instance periodicHypercubicEvenSpecialUnitarySpatialSliceHaarPositive_sFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The canonical Moore--Aronszajn feature of the actual complete one-slab
kernel is continuous.  Thus no extra feature-measurability hypothesis is
introduced when passing from pointwise PSD to complete Haar-`L²` positivity. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).feature := by
  exact
    RealHilbertKernelFeature.continuous_feature_of_continuous_kernel
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        H N beta)

/-- The canonical complete one-slab RKHS feature has pointwise norm at most
one.  This is the exact diagonal consequence of the already-proved kernel
bound `0 < K_slab ≤ 1`. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_norm_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ‖(periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).feature A‖ ≤ 1 := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
      H N hN beta hbeta
  have hsq :
      ‖C.feature A‖ ^ 2 =
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A A := by
    calc
      ‖C.feature A‖ ^ 2 = inner ℝ (C.feature A) (C.feature A) :=
        (real_inner_self_eq_norm_sq (C.feature A)).symm
      _ = periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A A := (C.kernel_eq_inner A A).symm
  have hk :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta A A ≤ 1 :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_le_one
      H N hN beta hbeta A A
  have hn : 0 ≤ ‖C.feature A‖ := norm_nonneg _
  nlinarith

/-- Every Haar-`L²` boundary vector gives an integrable Hilbert-valued analyzed
feature `A ↦ f(A) • Φ(A)`.  Probability normalization supplies `L² ⊂ L¹`,
while the exact RKHS feature norm is bounded by one. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_weighted_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    Integrable
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        f A •
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
            H N hN beta hbeta).feature A)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let C :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
      H N hN beta hbeta
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hf1 : Integrable (fun A => f A) μ := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp f).mono_exponent (by norm_num)
  have hCmeas : AEStronglyMeasurable C.feature μ :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_continuous
      H N hN beta hbeta).measurable.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun A => f A • C.feature A) μ :=
    (Lp.aestronglyMeasurable f).smul hCmeas
  apply hf1.norm.mono' hmeas
  filter_upwards with A
  rw [norm_smul]
  have hC :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_norm_le_one
      H N hN beta hbeta A
  calc
    ‖f A‖ * ‖C.feature A‖ ≤ ‖f A‖ * 1 :=
      mul_le_mul_of_nonneg_left hC (norm_nonneg _)
    _ = ‖‖f A‖‖ := by simp

/-- The complete one-slab Hilbert-valued Gram integrand is integrable on the
product Haar probability. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_pair_inner_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        inner ℝ
          (f p.1 •
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
              H N hN beta hbeta).feature p.1)
          (f p.2 •
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
              H N hN beta hbeta).feature p.2))
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let C :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
      H N hN beta hbeta
  let g := fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
    f A • C.feature A
  have hg : Integrable g μ := by
    simpa [μ, C, g] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_weighted_integrable
        H N hN beta hbeta f
  have hdom : Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        ‖g p.1‖ * ‖g p.2‖)
      (μ.prod μ) := by
    simpa [smul_eq_mul] using hg.norm.smul_prod hg.norm
  have hmeas : AEStronglyMeasurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        inner ℝ (g p.1) (g p.2))
      (μ.prod μ) :=
    (hg.aestronglyMeasurable.comp_fst).inner
      (hg.aestronglyMeasurable.comp_snd)
  have hpair : Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        inner ℝ (g p.1) (g p.2))
      (μ.prod μ) := by
    apply hdom.mono' hmeas
    filter_upwards with p
    exact norm_inner_le_norm _ _
  simpa [periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
    μ, C, g] using hpair

/-- Exact complete Haar-`L²` quadratic-form identity for the actual one-slab
transfer kernel.  The Hilbert--Schmidt double integral is the squared norm of
the Bochner integral of the measurable canonical RKHS feature. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_self_eq_norm_integral_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta) f f =
      ‖∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          f A •
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
              H N hN beta hbeta).feature A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)‖ ^ 2 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let C :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
      H N hN beta hbeta
  let g := fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
    f A • C.feature A
  have hg : Integrable g μ := by
    simpa [μ, C, g] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_weighted_integrable
        H N hN beta hbeta f
  have hpair : Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        inner ℝ (g p.1) (g p.2))
      (μ.prod μ) := by
    simpa [periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      μ, C, g] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_pair_inner_integrable
        H N hN beta hbeta f
  have hK :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
      H N hN beta hbeta
  have hff := realL2ExternalTensor_coeFn (μ := μ) (ν := μ) f f
  calc
    realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta) f f =
      ∫ p :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        inner ℝ (g p.1) (g p.2) ∂(μ.prod μ) := by
      rw [realL2HilbertSchmidtKernelPairing, MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hK, hff] with p hpK hpff
      rw [hpK, hpff]
      simp only [realL2ExternalTensorFunction]
      rw [realL2Scalar_inner_eq_mul]
      rw [C.kernel_eq_inner p.1 p.2]
      simp [g, real_inner_smul_left, real_inner_smul_right]
      ring
    _ = ∫ A, ∫ B, inner ℝ (g A) (g B) ∂μ ∂μ :=
      MeasureTheory.integral_prod _ hpair
    _ = ∫ A, inner ℝ (g A) (∫ B, g B ∂μ) ∂μ := by
      apply integral_congr_ae
      filter_upwards with A
      exact integral_inner hg (g A)
    _ = ∫ A, inner ℝ (∫ B, g B ∂μ) (g A) ∂μ := by
      apply integral_congr_ae
      filter_upwards with A
      exact real_inner_comm _ _
    _ = inner ℝ (∫ B, g B ∂μ) (∫ A, g A ∂μ) := by
      exact integral_inner hg (∫ B, g B ∂μ)
    _ = ‖∫ A, g A ∂μ‖ ^ 2 := by
      simpa using real_inner_self_eq_norm_sq (∫ A, g A ∂μ)
    _ = ‖∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          f A •
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
              H N hN beta hbeta).feature A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)‖ ^ 2 := by
      rfl

/-- The actual one-slab Hilbert--Schmidt pairing is nonnegative on the complete
spatial-slice Haar `L²` Hilbert space. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_nonnegative
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    RealL2HilbertSchmidtKernelPairingNonnegative
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN beta hbeta) := by
  intro f
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_self_eq_norm_integral_sq
    H N hN beta hbeta f]
  exact sq_nonneg _

/-- The actual one-slab Hilbert--Schmidt pairing is symmetric on complete
spatial-slice Haar `L²`. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_symmetric
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    RealL2HilbertSchmidtKernelPairingSymmetric
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN beta hbeta) := by
  exact realL2HilbertSchmidtKernelPairing_symmetric_of_ae_symmetric_rep
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H N hN beta hbeta)
    (fun p =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta p.1 p.2)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_representative_symmetric
      H N hN beta hbeta)

/-- The genuine compact `SU(N)` one-slab Haar-`L²` transfer operator is
positive on the complete spatial-slice Hilbert space. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_isPositive
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
      H N hN beta hbeta :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →L[ℝ]
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →ₗ[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)).IsPositive := by
  exact realL2HilbertSchmidtKernelOperator_isPositive
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_symmetric
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_nonnegative
      H N hN beta hbeta)

/-- Audit-visible complete Haar-`L²` positivity receipt for the actual adjacent
spatial-slice one-slab Wilson transfer. -/
structure PeriodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferPositivePackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  pairingSymmetric :
    RealL2HilbertSchmidtKernelPairingSymmetric
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN beta hbeta)
  pairingNonnegative :
    RealL2HilbertSchmidtKernelPairingNonnegative
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN beta hbeta)
  operatorPositive :
    ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
      H N hN beta hbeta :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →L[ℝ]
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →ₗ[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)).IsPositive
  quadraticIdentity :
    ∀ f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      realL2HilbertSchmidtKernelPairing
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
            H N hN beta hbeta) f f =
        ‖∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
            f A •
              (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
                H N hN beta hbeta).feature A
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)‖ ^ 2

/-- Construct the complete one-slab Haar-`L²` positivity package. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferPositivePackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferPositivePackage
      H N hN beta hbeta :=
  { pairingSymmetric :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_symmetric
        H N hN beta hbeta
    pairingNonnegative :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_nonnegative
        H N hN beta hbeta
    operatorPositive :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_isPositive
        H N hN beta hbeta
    quadraticIdentity :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_self_eq_norm_integral_sq
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
