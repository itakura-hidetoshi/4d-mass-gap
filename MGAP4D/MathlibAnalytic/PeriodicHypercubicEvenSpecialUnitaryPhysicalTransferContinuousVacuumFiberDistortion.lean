import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPointwiseHarnack
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureCenteredVariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open ProbabilityTheory
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section

local instance continuousVacuumFiberDistortionSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumFiberDistortionSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumFiberDistortionSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumFiberDistortionSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumFiberDistortionSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumFiberDistortionSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

private theorem continuousVacuumFiberDistortion_integrable_mul_of_norm_le_one
    {α : Type*}
    [MeasurableSpace α]
    {μ : Measure α}
    {f k : α → ℝ}
    (hf : Integrable f μ)
    (hk : AEStronglyMeasurable k μ)
    (hbound : ∀ᵐ x ∂μ, ‖k x‖ ≤ 1) :
    Integrable (fun x => f x * k x) μ := by
  apply hf.norm.mono' (hf.aestronglyMeasurable.mul hk)
  filter_upwards [hbound] with x hx
  change ‖f x * k x‖ ≤ ‖f x‖
  rw [norm_mul]
  calc
    ‖f x‖ * ‖k x‖ ≤ ‖f x‖ * 1 :=
      mul_le_mul_of_nonneg_left hx (norm_nonneg (f x))
    _ = ‖f x‖ := mul_one _

private theorem continuousVacuumFiberDistortion_kernelSection_aestronglyMeasurable
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    AEStronglyMeasurable
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  have hPair : Continuous
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        (A, B)) :=
    continuous_id.prodMk continuous_const
  exact
    ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).comp hPair).aestronglyMeasurable

private theorem continuousVacuumFiberDistortion_kernelSection_norm_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B‖ ≤ 1 := by
  intro A
  simpa [Real.norm_eq_abs] using
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H N hN beta hbeta A B

/-- The canonical continuous physical vacuum is strictly positive at every
spatial boundary configuration.

The proof deliberately separates the qualitative finite-volume positivity
input from the quantitative Harnack estimate used below.  Compactness is used
only to obtain some positive Wilson-kernel floor, while the eventual one-link
distortion factor remains the explicit volume-independent `exp (8 * beta)`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta B := by
  let μ : Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let f : Lp ℝ 2 μ :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta).1
  let lambda : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  have hfInt : Integrable (fun A => f A) μ := by
    exact (Lp.memLp f).integrable (by norm_num)
  have hfNonneg : ∀ᵐ A ∂μ, 0 ≤ f A := by
    simpa [μ, f] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
        H N hN beta hbeta
  have hfnorm : ‖f‖ = 1 := by
    simpa [f] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
        H N hN beta hbeta
  have hfIntegralPos : 0 < ∫ A, f A ∂μ :=
    realL2_integral_pos_of_ae_nonnegative_norm_one f hfNonneg hfnorm
  obtain ⟨m, hmpos, hm⟩ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_exists_uniform_pos_lower_bound
      H N beta
  have hrightInt : Integrable
      (fun A => f A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B) μ := by
    apply continuousVacuumFiberDistortion_integrable_mul_of_norm_le_one hfInt
    · simpa [μ] using
        continuousVacuumFiberDistortion_kernelSection_aestronglyMeasurable
          H N beta B
    · filter_upwards with A
      exact continuousVacuumFiberDistortion_kernelSection_norm_le_one
        H N hN beta hbeta B A
  have hleftInt : Integrable (fun A => m * f A) μ := hfInt.const_mul m
  have hIntegralLower :
      m * (∫ A, f A ∂μ) ≤
        ∫ A, f A *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A B ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae hleftInt hrightInt
    filter_upwards [hfNonneg] with A hA
    calc
      m * f A = f A * m := by ring
      _ ≤ f A *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A B :=
        mul_le_mul_of_nonneg_left (hm A B) hA
  have hIntegralPos :
      0 < ∫ A, f A *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A B ∂μ :=
    lt_of_lt_of_le (mul_pos hmpos hfIntegralPos) hIntegralLower
  have hSynthesisPos :
      0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisFunction
        H N hN beta hbeta B := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisFunction_eq_integral_kernel]
    simpa [μ, f] using hIntegralPos
  have hlambdaPos : 0 < lambda := by
    simpa [lambda] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
        H N hN beta hbeta
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
  exact mul_pos (inv_pos.mpr hlambdaPos) hSynthesisPos

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_current
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
      H N A target (A target) = A := by
  classical
  funext e
  by_cases he : e = target
  · subst e
    simp
  · simp [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink, he]

/-- One-link replacement is continuous in the inserted `SU(N)` value. -/
theorem periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_continuous
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H N A target g) := by
  classical
  apply continuous_pi
  intro e
  by_cases he : e = target
  · subst e
    simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
      (continuous_id : Continuous (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ => g))
  · simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink, he] using
      (continuous_const : Continuous
        (fun _g : Matrix.specialUnitaryGroup (Fin N) ℂ => A e))

/-- The canonical continuous physical vacuum weight along one actual spatial
link fiber.  Unlike the older quotient-representative weight, this is a genuine
pointwise continuous function. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
        H N A target g))

/-- The continuous-vacuum fiber weight is continuous and hence measurable for
any raw one-link law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
        H N hN beta hbeta A target) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
  exact ENNReal.continuous_ofReal.comp
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H N hN beta hbeta).comp
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_continuous
        H N A target))

/-- Explicit local distortion package for the canonical continuous vacuum.
The lower and upper endpoints are anchored at the unmodified configuration
`A`; their quotient will therefore cancel the unknown vacuum amplitude in the
next Doob-variance unit. -/
structure
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberDistortionData
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (nu : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) where
  m : ℝ≥0∞
  M : ℝ≥0∞
  measurable :
    AEMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
        H N hN beta hbeta A target) nu
  lower_pos : 0 < m
  upper_finite : M < ∞
  lower : ∀ g,
    m ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
        H N hN beta hbeta A target g
  upper : ∀ g,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
        H N hN beta hbeta A target g ≤ M

/-- The pointwise Harnack theorem canonically populates the continuous-vacuum
one-link distortion data with the volume-independent factor `exp (8 * beta)`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberDistortionData
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (nu : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberDistortionData
      H N hN beta hbeta nu A target := by
  let omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let R : ℝ := Real.exp (8 * beta)
  let base : ℝ := omega A
  have hRpos : 0 < R := by
    exact Real.exp_pos _
  have hbasePos : 0 < base := by
    simpa [base, omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta A
  refine
    { m := ENNReal.ofReal (base / R)
      M := ENNReal.ofReal (R * base)
      measurable := ?_
      lower_pos := ?_
      upper_finite := ENNReal.ofReal_lt_top
      lower := ?_
      upper := ?_ }
  · exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight_continuous
        H N hN beta hbeta A target).measurable.aemeasurable
  · exact ENNReal.ofReal_pos.mpr (div_pos hbasePos hRpos)
  · intro g
    apply ENNReal.ofReal_le_ofReal
    have hH :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuousVacuumReplaceLink_le_exp_eight_mul
        H N hN beta hbeta A target (A target) g
    have hbaseLe : base ≤ R * omega
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H N A target g) := by
      simpa [base, omega, R,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_current]
        using hH
    exact (div_le_iff₀ hRpos).2 (by simpa [mul_comm] using hbaseLe)
  · intro g
    apply ENNReal.ofReal_le_ofReal
    have hH :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuousVacuumReplaceLink_le_exp_eight_mul
        H N hN beta hbeta A target g (A target)
    simpa [base, omega, R,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_current]
      using hH

end

end MathlibAnalytic
end MGAP4D
