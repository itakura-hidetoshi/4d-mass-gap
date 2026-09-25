import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointFixedLeftKernelSectionFactor
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-!
# Fixed-left kernel-section weighted Fubini identity

PR #4742 orients the continuous genuine joint density as

  rho(C,A) = lambda^{-1} Omega(C) w(C,A),

with `w(C,A)` the fixed-right kernel-section weight from PR #4740.

This file inserts the scalar `lambda^{-1} Omega(C)` into the measurable
kernel-section Fubini theorem from PR #4740.  The section mass
`lambda Omega(C)` then cancels the transfer normalization exactly, leaving the
outer continuous-vacuum square

  Omega(C)^2.

Thus for every nonnegative jointly measurable observable `F` we obtain one
Markov kernel `kappa`, Haar-a.e. equal to the literal normalized fixed-right
kernel-section law, with

  int rho(C,A) F(C,A) dmu(C)dmu(A)
    = int Omega(C)^2 [int F(C,A) dkappa_C(A)] dmu(C).

No identification with the historical vacuum measure or genuine joint measure
is made yet; those are the next measure-presentation step.  No pointwise bound
of a fixed section by a global L2 norm is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance groundStateJointKernelSectionWeightedFubiniTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointKernelSectionWeightedFubiniCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointKernelSectionWeightedFubiniSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointKernelSectionWeightedFubiniMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointKernelSectionWeightedFubiniBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointKernelSectionWeightedFubiniSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Exact weighted Fubini identity for the fixed-left continuous genuine-joint
factor.  The outer density is the square of the continuous physical vacuum. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftKernelSection_exists_markovKernel_weighted_lintegral_identity
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞)
    (hF : AEMeasurable (Function.uncurry F)
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) :
    ∃ κ : Kernel
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N),
      IsMarkovKernel κ ∧
        (∀ᵐ C ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
          κ C =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta C) ∧
        (∫⁻ z,
            ENNReal.ofReal
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftKernelSectionFactor
                  H N hN beta hbeta z) *
              F z.1 z.2
          ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) =
          ∫⁻ C,
            ENNReal.ofReal
                ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
                    H N hN beta hbeta C) ^ 2) *
              (∫⁻ A, F C A ∂κ C)
            ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let lambda :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  let omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let c : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun C => ENNReal.ofReal (lambda⁻¹ * omega C)
  let scaledF :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun C A => c C * F C A

  have hlambda : 0 < lambda := by
    simpa [lambda] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
        H N hN beta hbeta
  have homega : ∀ C, 0 < omega C := by
    intro C
    simpa [omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta C
  have homegaContinuous : Continuous omega := by
    simpa [omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
        H N hN beta hbeta
  have hcRealContinuous : Continuous (fun C => lambda⁻¹ * omega C) :=
    continuous_const.mul homegaContinuous
  have hcMeasurable : Measurable c := by
    exact (ENNReal.continuous_ofReal.comp hcRealContinuous).measurable
  have hscaledF :
      AEMeasurable (Function.uncurry scaledF) (μ.prod μ) := by
    have hcPair :
        AEMeasurable
          (fun z :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            c z.1)
          (μ.prod μ) :=
      (hcMeasurable.comp measurable_fst).aemeasurable
    simpa [scaledF, Function.uncurry] using hcPair.mul hF

  obtain ⟨κ, hκ, hκae, hid⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuous_exists_markovKernel_lintegral_identity
      H N hN beta hbeta scaledF hscaledF

  have hFactor :
      ∀ C A,
        ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftKernelSectionFactor
              H N hN beta hbeta (C, A)) =
          ENNReal.ofReal
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
                H N hN beta hbeta C A) *
            c C := by
    intro C A
    have hcPos : 0 < lambda⁻¹ * omega C :=
      mul_pos (inv_pos.mpr hlambda) (homega C)
    change
      ENNReal.ofReal
          (lambda⁻¹ * omega C *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
              H N hN beta hbeta C A) =
        ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
              H N hN beta hbeta C A) *
          c C
    rw [ENNReal.ofReal_mul hcPos.le]
    simp only [c]
    ac_rfl

  have hMassScale :
      ∀ C,
        ENNReal.ofReal (lambda * omega C) * c C =
          ENNReal.ofReal ((omega C) ^ 2) := by
    intro C
    have hmPos : 0 < lambda * omega C := mul_pos hlambda (homega C)
    change
      ENNReal.ofReal (lambda * omega C) *
          ENNReal.ofReal (lambda⁻¹ * omega C) =
        ENNReal.ofReal ((omega C) ^ 2)
    rw [← ENNReal.ofReal_mul hmPos.le]
    apply congrArg ENNReal.ofReal
    calc
      (lambda * omega C) * (lambda⁻¹ * omega C) =
          (lambda * lambda⁻¹) * (omega C * omega C) := by ring
      _ = omega C * omega C := by
        rw [mul_inv_cancel₀ hlambda.ne', one_mul]
      _ = (omega C) ^ 2 := by ring

  have hcTop : ∀ C, c C ≠ ∞ := by
    intro C
    dsimp [c]
    exact ne_of_lt ENNReal.ofReal_lt_top

  have hScaledIntegral :
      ∀ C,
        (∫⁻ A, scaledF C A ∂κ C) =
          c C * (∫⁻ A, F C A ∂κ C) := by
    intro C
    simpa [scaledF] using
      (lintegral_const_mul' (μ := κ C) (c C) (F C) (hcTop C))

  refine ⟨κ, hκ, hκae, ?_⟩
  calc
    (∫⁻ z,
        ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftKernelSectionFactor
              H N hN beta hbeta z) *
          F z.1 z.2
      ∂(μ.prod μ)) =
        ∫⁻ z,
          ENNReal.ofReal
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
                H N hN beta hbeta z.1 z.2) *
            scaledF z.1 z.2
          ∂(μ.prod μ) := by
      apply lintegral_congr
      intro z
      rw [hFactor z.1 z.2]
      simp only [scaledF]
      rw [mul_assoc]
    _ =
        ∫⁻ C,
          ENNReal.ofReal (lambda * omega C) *
            (∫⁻ A, scaledF C A ∂κ C)
          ∂μ := by
      simpa [μ, lambda, omega] using hid
    _ =
        ∫⁻ C,
          ENNReal.ofReal ((omega C) ^ 2) *
            (∫⁻ A, F C A ∂κ C)
          ∂μ := by
      apply lintegral_congr
      intro C
      rw [hScaledIntegral C, ← mul_assoc, hMassScale C]
    _ =
        ∫⁻ C,
          ENNReal.ofReal
              ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
                  H N hN beta hbeta C) ^ 2) *
            (∫⁻ A, F C A ∂κ C)
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
      rfl

end

end MathlibAnalytic
end MGAP4D
