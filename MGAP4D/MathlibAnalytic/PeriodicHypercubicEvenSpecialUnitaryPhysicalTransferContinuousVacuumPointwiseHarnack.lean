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
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  have hΩInt : Integrable (fun A => Ω.1 A) μ := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp Ω.1).mono_exponent (by norm_num)
  have hKContinuous : Continuous
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        H N beta).comp (by fun_prop)
  have hKBound :
      ∀ᵐ A ∂μ,
        ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B‖ ≤ 1 := by
    filter_upwards with A
    simpa [Real.norm_eq_abs] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H N hN beta hbeta A B
  have hMul := hΩInt.bdd_mul hKContinuous.aestronglyMeasurable hKBound
  simpa [μ, Ω, mul_comm] using hMul

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
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let C := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
    H N hN beta hbeta
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  have hVecInt : Integrable (fun A => Ω.1 A • C.feature A) μ := by
    simpa [μ, C, Ω] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_weighted_integrable
        H N hN beta hbeta Ω.1
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisFunction
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator_apply]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator_apply]
  change
    inner ℝ (∫ A, Ω.1 A • C.feature A ∂μ) (C.feature B) =
      ∫ A, Ω.1 A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B ∂μ
  calc
    inner ℝ (∫ A, Ω.1 A • C.feature A ∂μ) (C.feature B) =
        inner ℝ (C.feature B) (∫ A, Ω.1 A • C.feature A ∂μ) :=
      real_inner_comm _ _
    _ = ∫ A, inner ℝ (C.feature B) (Ω.1 A • C.feature A) ∂μ := by
      exact (integral_inner hVecInt (C.feature B)).symm
    _ = ∫ A, Ω.1 A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B ∂μ := by
      apply integral_congr_ae
      filter_upwards with A
      rw [real_inner_smul_right]
      rw [real_inner_comm (C.feature B) (C.feature A)]
      rw [← C.kernel_eq_inner A B]

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
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  let Bg := periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    H N B target g
  let Bh := periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    H N B target h
  let R := Real.exp (8 * beta)
  let lambda := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖
  have hIg : Integrable
      (fun A => Ω.1 A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A Bg) μ := by
    simpa [μ, Ω, Bg] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumKernelProduct_integrable
        H N hN beta hbeta Bg
  have hIh : Integrable
      (fun A => Ω.1 A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A Bh) μ := by
    simpa [μ, Ω, Bh] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumKernelProduct_integrable
        H N hN beta hbeta Bh
  have hScaled : Integrable
      (fun A => Ω.1 A *
        (R * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A Bh)) μ := by
    have h := hIh.const_mul R
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hΩNonneg : ∀ᵐ A ∂μ, 0 ≤ Ω.1 A := by
    simpa [μ, Ω] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
        H N hN beta hbeta
  have hIntegral :
      (∫ A, Ω.1 A *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A Bg ∂μ) ≤
        R *
          ∫ A, Ω.1 A *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A Bh ∂μ := by
    calc
      (∫ A, Ω.1 A *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A Bg ∂μ) ≤
          ∫ A, Ω.1 A *
            (R * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A Bh) ∂μ := by
        apply integral_mono_ae hIg hScaled
        filter_upwards [hΩNonneg] with A hΩ
        have hK :=
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuousVacuumReplaceLink_le_exp_eight_mul
            H N hN beta hbeta A B target g h
        change
          Ω.1 A *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta A Bg ≤
            Ω.1 A *
              (R * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta A Bh)
        exact mul_le_mul_of_nonneg_left (by simpa [R, Bg, Bh] using hK) hΩ
      _ = R *
          ∫ A, Ω.1 A *
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
      (∫ A, Ω.1 A *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A Bg ∂μ) ≤
    R *
      (lambda⁻¹ *
        ∫ A, Ω.1 A *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A Bh ∂μ)
  have hlambdaInv : 0 ≤ lambda⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have h := mul_le_mul_of_nonneg_left hIntegral hlambdaInv
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

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
