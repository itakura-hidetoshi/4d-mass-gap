import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumLocalHarnack
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance continuousVacuumPointwiseHarnackSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumPointwiseHarnackSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumPointwiseHarnackSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumPointwiseHarnackSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumPointwiseHarnackSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumPointwiseHarnackSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

private theorem continuousVacuumPointwiseHarnackLpTwo_integrable
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    [IsFiniteMeasure μ]
    (f : Lp ℝ 2 μ) :
    Integrable (fun x => f x) μ := by
  exact (Lp.memLp f).integrable (by norm_num)

/-- For every fixed second boundary, the physical nonnegative vacuum times the
one-slab Wilson kernel is Haar-integrable.  The proof uses only `Ω ∈ L²`, the
probability normalization of Haar measure, continuity of the kernel section,
and the uniform pointwise bound `|K| ≤ 1`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumKernelProduct_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Integrable
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let μ : Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let f : Lp ℝ 2 μ :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta).1
  have hfInt : Integrable (fun A => f A) μ :=
    continuousVacuumPointwiseHarnackLpTwo_integrable μ f
  have hPairContinuous : Continuous
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        (A, B)) :=
    continuous_id.prod_mk continuous_const
  have hKContinuous : Continuous
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).comp hPairContinuous
  have hProductMeasurable : AEStronglyMeasurable
      (fun A => f A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B) μ :=
    hfInt.aestronglyMeasurable.mul hKContinuous.aestronglyMeasurable
  have hDom : ∀ᵐ A ∂μ,
      ‖f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B‖ ≤ ‖f A‖ := by
    filter_upwards with A
    rw [norm_mul]
    calc
      ‖f A‖ * ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B‖ ≤ ‖f A‖ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg (f A))
        simpa [Real.norm_eq_abs] using
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
            H N hN beta hbeta A B
      _ = ‖f A‖ := mul_one _
  have hProduct : Integrable
      (fun A => f A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B) μ :=
    hfInt.mono' hProductMeasurable hDom
  simpa [μ, f] using hProduct

/-- The unscaled continuous physical-vacuum synthesis is the literal Wilson
kernel integral against the existing nonnegative Haar-`L²` vacuum.  Pointwise
values are taken only on the newly constructed continuous synthesis side; the
old vacuum representative occurs solely under the Haar integral. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisFunction_eq_integral_kernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisFunction
        H N hN beta hbeta B =
      ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let μ : Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let C := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
    H N hN beta hbeta
  let f : Lp ℝ 2 μ :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta).1
  have hVecInt : Integrable (fun A => f A • C.feature A) μ := by
    simpa [μ, C, f] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_weighted_integrable
        H N hN beta hbeta f
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisFunction
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator_apply]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator_apply]
  change
    inner ℝ (∫ A, f A • C.feature A ∂μ) (C.feature B) =
      ∫ A, f A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B ∂μ
  calc
    inner ℝ (∫ A, f A • C.feature A ∂μ) (C.feature B) =
        inner ℝ (C.feature B) (∫ A, f A • C.feature A ∂μ) :=
      real_inner_comm _ _
    _ = ∫ A, inner ℝ (C.feature B) (f A • C.feature A) ∂μ := by
      exact (integral_inner hVecInt (C.feature B)).symm
    _ = ∫ A, f A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B ∂μ := by
      apply integral_congr_ae
      filter_upwards with A
      rw [real_inner_smul_right]
      apply congrArg (fun x : ℝ => f A * x)
      calc
        inner ℝ (C.feature B) (C.feature A) =
            inner ℝ (C.feature A) (C.feature B) := real_inner_comm _ _
        _ = periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A B := (C.kernel_eq_inner A B).symm

/-- Volume-uniform pointwise Harnack inequality for the canonical continuous
physical Wilson vacuum.  Replacing one spatial link changes the continuous
vacuum by at most the explicit factor `exp (8 * beta)`.  The proof uses no
global compactness minimum and never evaluates the old `L²` quotient vacuum at
a prescribed fiber point. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuousVacuumReplaceLink_le_exp_eight_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H N B target g) ≤
      Real.exp (8 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
            H N B target h) := by
  let μ : Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let f : Lp ℝ 2 μ :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta).1
  let Bg := periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    H N B target g
  let Bh := periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    H N B target h
  let R : ℝ := Real.exp (8 * beta)
  let lambda : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  have hIg : Integrable
      (fun A => f A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A Bg) μ := by
    simpa [μ, f, Bg] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumKernelProduct_integrable
        H N hN beta hbeta Bg
  have hIh : Integrable
      (fun A => f A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A Bh) μ := by
    simpa [μ, f, Bh] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumKernelProduct_integrable
        H N hN beta hbeta Bh
  have hScaled : Integrable
      (fun A => f A *
        (R * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A Bh)) μ := by
    have hscaled := hIh.const_mul R
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hfNonneg : ∀ᵐ A ∂μ, 0 ≤ f A := by
    simpa [μ, f] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
        H N hN beta hbeta
  have hIntegral :
      (∫ A, f A *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A Bg ∂μ) ≤
        R *
          ∫ A, f A *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A Bh ∂μ := by
    calc
      (∫ A, f A *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A Bg ∂μ) ≤
          ∫ A, f A *
            (R * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A Bh) ∂μ := by
        apply integral_mono_ae hIg hScaled
        filter_upwards [hfNonneg] with A hf
        have hK :=
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuousVacuumReplaceLink_le_exp_eight_mul
            H N hN beta hbeta A B target g h
        change
          f A *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta A Bg ≤
            f A *
              (R * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta A Bh)
        exact mul_le_mul_of_nonneg_left (by simpa [R, Bg, Bh] using hK) hf
      _ = R *
          ∫ A, f A *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A Bh ∂μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with A
        ring
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta Bg ≤
      R *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta Bh
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisFunction_eq_integral_kernel
    H N hN beta hbeta Bg]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisFunction_eq_integral_kernel
    H N hN beta hbeta Bh]
  change lambda⁻¹ *
      (∫ A, f A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A Bg ∂μ) ≤
    R *
      (lambda⁻¹ *
        ∫ A, f A *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A Bh ∂μ)
  have hlambdaPos : 0 < lambda := by
    simpa [lambda] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
        H N hN beta hbeta
  have hlambdaInv : 0 ≤ lambda⁻¹ := (inv_pos.mpr hlambdaPos).le
  have hscaled := mul_le_mul_of_nonneg_left hIntegral hlambdaInv
  simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Reverse one-link Harnack comparison with the same volume-independent
factor. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuousVacuumReplaceLink_reverse_le_exp_eight_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H N B target h) ≤
      Real.exp (8 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
            H N B target g) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuousVacuumReplaceLink_le_exp_eight_mul
      H N hN beta hbeta B target h g

end

end MathlibAnalytic
end MGAP4D
