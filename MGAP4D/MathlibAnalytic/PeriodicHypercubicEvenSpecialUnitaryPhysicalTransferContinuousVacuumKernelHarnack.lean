import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetKernelHarnack
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

/-- Pointwise Moore--Aronszajn synthesis of an analyzed Haar-`L²` vector is
exactly the raw one-slab kernel integral.  This is the missing pointwise bridge
between the RKHS feature presentation and the literal Wilson kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction_analysis_eq_integral_kernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
          H N hN beta hbeta f) B =
      ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let C :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
      H N hN beta hbeta
  have hfInt : Integrable (fun A => f A • C.feature A) μ := by
    simpa [μ, C] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_weighted_integrable
        H N hN beta hbeta f
  change
    inner ℝ (∫ A, f A • C.feature A ∂μ) (C.feature B) =
      ∫ A, f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta A B ∂μ
  calc
    inner ℝ (∫ A, f A • C.feature A ∂μ) (C.feature B) =
        inner ℝ (C.feature B) (∫ A, f A • C.feature A ∂μ) :=
      real_inner_comm _ _
    _ = ∫ A, inner ℝ (C.feature B) (f A • C.feature A) ∂μ := by
      exact (integral_inner hfInt (C.feature B)).symm
    _ = ∫ A, f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta A B ∂μ := by
      apply integral_congr_ae
      filter_upwards with A
      rw [real_inner_smul_right, real_inner_comm]
      rw [← C.kernel_eq_inner A B]

/-- Multiplying a Haar-`L²` boundary vector by a fixed raw one-slab kernel
section is integrable. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Integrable
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hf1 : Integrable (fun A => f A) μ := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp f).mono_exponent (by norm_num)
  have hKmeas : AEStronglyMeasurable
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B) μ := by
    have hcont : Continuous
        (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        f A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B) μ :=
    (Lp.aestronglyMeasurable f).mul hKmeas
  apply hf1.norm.mono' hmeas
  filter_upwards with A
  have hk :
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B‖ ≤ 1 := by
    simpa [Real.norm_eq_abs] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H N hN beta hbeta A B
  rw [norm_mul]
  simpa using mul_le_mul_of_nonneg_left hk (norm_nonneg (f A))

/-- Pointwise transfer-eigenfunction equation for the canonical continuous
physical vacuum representative, expressed with the literal raw one-slab
Wilson kernel and the existing nonnegative Haar-`L²` vacuum class. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_topNorm_mul_eq_integral_kernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta B =
      ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 A *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A B
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let lambda :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  let Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta
  have hlambda : 0 < lambda := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
        H N hN beta hbeta
  change
    lambda *
        (lambda⁻¹ *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
              H N hN beta hbeta Omega) B) = _
  calc
    lambda *
        (lambda⁻¹ *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
              H N hN beta hbeta Omega) B) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H N hN beta hbeta Omega) B := by
      rw [← mul_assoc]
      simp [hlambda.ne']
    _ = ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        Omega.1 A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
      rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator_apply]
      exact
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction_analysis_eq_integral_kernel
          H N hN beta hbeta
          ((Omega : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
            Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) B
    _ = _ := by rfl

/-- The sharp raw one-link kernel Harnack bound transports to the canonical
continuous physical vacuum representative with the same volume-independent
factor `exp (8 * beta)`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_update_right_le_exp_eight_mul_update_right
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta (Function.update B target g) ≤
      Real.exp (8 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update B target h) := by
  classical
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let Omega :=
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  let Bg : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update B target g
  let Bh : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update B target h
  let c := Real.exp (8 * beta)
  let lambda :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  have hlambda : 0 < lambda := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
        H N hN beta hbeta
  have hOmegaNonneg : ∀ᵐ A ∂μ, 0 ≤ Omega A := by
    simpa [μ, Omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
        H N hN beta hbeta
  have hIntG : Integrable
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        Omega A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A Bg) μ := by
    simpa [μ, Omega, Bg] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
        H N hN beta hbeta Omega Bg
  have hIntH : Integrable
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        Omega A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A Bh) μ := by
    simpa [μ, Omega, Bh] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
        H N hN beta hbeta Omega Bh
  have hPoint : ∀ᵐ A ∂μ,
      Omega A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A Bg ≤
        c * (Omega A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A Bh) := by
    filter_upwards [hOmegaNonneg] with A hOmega
    have hK :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_le_exp_eight_mul_update_right
        H N hN beta hbeta A B target g h
    have hmul := mul_le_mul_of_nonneg_left hK hOmega
    simpa [Bg, Bh, c, mul_assoc, mul_comm, mul_left_comm] using hmul
  have hIntegral :
      (∫ A, Omega A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A Bg ∂μ) ≤
        ∫ A, c * (Omega A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A Bh) ∂μ := by
    exact integral_mono_ae hIntG (hIntH.const_mul c) hPoint
  rw [integral_const_mul] at hIntegral
  have hEigG :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_topNorm_mul_eq_integral_kernel
      H N hN beta hbeta Bg
  have hEigH :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_topNorm_mul_eq_integral_kernel
      H N hN beta hbeta Bh
  change
    (∫ A, Omega A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta A Bg ∂μ) ≤
      c * ∫ A, Omega A * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta A Bh ∂μ at hIntegral
  have hScaled :
      lambda *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta Bg ≤
        lambda *
          (c *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
              H N hN beta hbeta Bh) := by
    rw [hEigG, hEigH]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hIntegral
  have hVac := (mul_le_mul_left hlambda).mp hScaled
  simpa [Bg, Bh, c] using hVac

/-- Symmetric pairwise one-link Harnack comparison for the canonical continuous
physical vacuum representative. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_update_right_pairwise_harnack
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update B target g) ≤
        Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta (Function.update B target h) ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update B target h) ≤
        Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta (Function.update B target g) := by
  constructor
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_update_right_le_exp_eight_mul_update_right
        H N hN beta hbeta B target g h
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_update_right_le_exp_eight_mul_update_right
        H N hN beta hbeta B target h g

end

end MathlibAnalytic
end MGAP4D
