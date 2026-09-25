import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateKernelSectionExplicitMarkovKernel
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Tactic

/-!
# Genuine ground-state joint measure disintegration by kernel sections

PR #4745 constructs one explicit Markov kernel

  kappa(C,dA)
    = [w(C,A) / (lambda * Omega_cont(C))] mu_Haar(dA),

whose fiber is exactly the normalized continuous fixed-right kernel-section
probability law.

Combining this kernel with the continuous vacuum-square measure from PR #4744,
the density algebra is pointwise

  Omega_cont(C)^2 *
    w(C,A) / (lambda * Omega_cont(C))
  = lambda^{-1} Omega_cont(C) w(C,A).

The right-hand side is exactly the fixed-left continuous joint density from
PR #4742.  Mathlib's composition-product and withDensity laws therefore give
the exact measure-level disintegration

  mu_joint = mu_vacuum tensor_m kappa.

This is the first integrand-independent genuine joint/kernel-section
disintegration in the positive-beta local-response spine.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance groundStateJointKernelSectionMeasureDisintegrationTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointKernelSectionMeasureDisintegrationCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointKernelSectionMeasureDisintegrationSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointKernelSectionMeasureDisintegrationMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointKernelSectionMeasureDisintegrationBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointKernelSectionMeasureDisintegrationSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Pointwise density algebra behind the genuine measure disintegration. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_kernelSection_density_product_eq_fixedLeft
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ENNReal.ofReal
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta C) ^ 2) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovDensity
        H N hN beta hbeta C A =
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftKernelSectionFactor
          H N hN beta hbeta (C, A)) := by
  let lambda : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  let omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let w : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
      H N hN beta hbeta C A
  have hlambda : 0 < lambda := by
    simpa [lambda] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
        H N hN beta hbeta
  have homega : 0 < omega C := by
    simpa [omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta C
  have hmass : 0 < lambda * omega C := mul_pos hlambda homega
  change
    ENNReal.ofReal ((omega C) ^ 2) *
        (ENNReal.ofReal w / ENNReal.ofReal (lambda * omega C)) =
      ENNReal.ofReal (lambda⁻¹ * omega C * w)
  rw [← ENNReal.ofReal_div_of_pos hmass]
  rw [← ENNReal.ofReal_mul (sq_nonneg (omega C))]
  apply congrArg ENNReal.ofReal
  field_simp [hlambda.ne', homega.ne']
  <;> ring

/-- The genuine two-boundary ground-state joint law is exactly the composition
product of the physical vacuum boundary law and the explicit normalized
fixed-right kernel-section Markov kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_eq_vacuum_compProd_kernelSectionMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta ⊗ₘ
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel
          H N hN beta hbeta := by
  let G := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let omega : G → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let v : G → ℝ≥0∞ := fun C => ENNReal.ofReal ((omega C) ^ 2)
  let q : G → G → ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovDensity
      H N hN beta hbeta
  have homega : Continuous omega := by
    simpa [omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
        H N hN beta hbeta
  have hv : Measurable v := by
    exact
      (ENNReal.continuous_ofReal.comp (homega.pow 2)).measurable
  have hq : Measurable (Function.uncurry q) := by
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovDensity_measurable
        H N hN beta hbeta
  have hvPair :
      Measurable (fun z : G × G => v z.1) :=
    hv.comp measurable_fst
  have hDensity :
      ∀ z : G × G,
        v z.1 * q z.1 z.2 =
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftKernelSectionFactor
              H N hN beta hbeta z) := by
    intro z
    simpa [v, q, omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_kernelSection_density_product_eq_fixedLeft
        H N hN beta hbeta z.1 z.2

  letI :
      IsMarkovKernel (Kernel.withDensity (Kernel.const G μ) q) := by
    simpa [G, μ, q,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel_isMarkovKernel
        H N hN beta hbeta

  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_eq_fixedLeftContinuousMeasure,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_eq_continuousVacuumSquareMeasure]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftContinuousMeasure
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSquareMeasure
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel
  change
    (μ.prod μ).withDensity
        (fun z =>
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftKernelSectionFactor
              H N hN beta hbeta z)) =
      (μ.withDensity v) ⊗ₘ
        Kernel.withDensity (Kernel.const G μ) q
  symm
  calc
    (μ.withDensity v) ⊗ₘ
        Kernel.withDensity (Kernel.const G μ) q =
      (((μ.withDensity v) ⊗ₘ Kernel.const G μ).withDensity
        (fun z : G × G => q z.1 z.2)) := by
          exact Measure.compProd_withDensity hq
    _ = ((μ.withDensity v).prod μ).withDensity
          (fun z : G × G => q z.1 z.2) := by
        rw [Measure.compProd_const]
    _ = ((μ.prod μ).withDensity (fun z : G × G => v z.1)).withDensity
          (fun z : G × G => q z.1 z.2) := by
        rw [prod_withDensity_left hv]
    _ = (μ.prod μ).withDensity
          (fun z : G × G => v z.1 * q z.1 z.2) := by
        exact
          (withDensity_mul (μ.prod μ) hvPair hq).symm
    _ = (μ.prod μ).withDensity
          (fun z =>
            ENNReal.ofReal
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftKernelSectionFactor
                H N hN beta hbeta z)) := by
        apply withDensity_congr_ae
        exact Filter.Eventually.of_forall hDensity

end

end MathlibAnalytic
end MGAP4D
