import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointKernelSectionMeasurePresentation
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic

/-!
# Explicit Markov kernel for continuous fixed-right ground-state sections

PR #4740 proves that every continuous fixed-right kernel-section weight has
exact Haar mass

  lambda * Omega_cont(C),

and that its normalized weighted measure is a probability law.

Instead of choosing a measurable representative existentially for each later
integrand, this file packages the normalized continuous section density itself
as one explicit measurable Markov kernel

  kappa(C,dA)
    = [ w(C,A) / (lambda * Omega_cont(C)) ] mu_Haar(dA).

Its value at every retained boundary C is exactly the literal normalized
continuous kernel-section probability measure.  The construction is
integrand-independent and will be used by the genuine measure-level
disintegration theorem.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance groundStateKernelSectionExplicitMarkovKernelTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateKernelSectionExplicitMarkovKernelCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateKernelSectionExplicitMarkovKernelSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateKernelSectionExplicitMarkovKernelMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateKernelSectionExplicitMarkovKernelBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateKernelSectionExplicitMarkovKernelSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Explicit normalized ENNReal density of a fixed-right continuous
kernel-section law against spatial Haar probability. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovDensity
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ≥0∞ :=
  ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
        H N hN beta hbeta C A) /
    ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta C)

/-- The explicit normalized section density is jointly measurable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovDensity_measurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Measurable
      (Function.uncurry
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovDensity
          H N hN beta hbeta)) := by
  let G := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let omega : G → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let w : G × G → ℝ := fun p =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
      H N hN beta hbeta p.1 p.2
  let mass : G → ℝ := fun C =>
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ * omega C
  have hw : Continuous w := by
    simpa [w] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_joint_continuous
        H N hN beta hbeta
  have homega : Continuous omega := by
    simpa [omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
        H N hN beta hbeta
  have hmass : Continuous mass := by
    exact continuous_const.mul homega
  change Measurable
    (fun p : G × G =>
      ENNReal.ofReal (w p) /
        ENNReal.ofReal (mass p.1))
  exact
    (ENNReal.continuous_ofReal.comp hw).measurable.div
      ((ENNReal.continuous_ofReal.comp (hmass.comp continuous_fst)).measurable)

/-- One explicit measurable kernel whose fibers are the normalized continuous
fixed-right ground-state kernel sections. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Kernel
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  Kernel.withDensity
    (Kernel.const
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovDensity
      H N hN beta hbeta)

/-- Every fiber of the explicit kernel is exactly the literal normalized
continuous fixed-right kernel-section probability measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel
        H N hN beta hbeta C =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel,
    Kernel.withDensity_apply _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovDensity_measurable
        H N hN beta hbeta)]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
    realIntegralWeightedProbabilityMeasure
    doobWeightedMeasure
  apply withDensity_congr_ae
  filter_upwards with A
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovDensity
    doobWeightedDensity
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_doobWeightMass
      H N hN beta hbeta C]

/-- The explicit section kernel is a genuine Markov kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel_isMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsMarkovKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel
        H N hN beta hbeta) := by
  constructor
  intro C
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel_apply
      H N hN beta hbeta C]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta C

end

end MathlibAnalytic
end MGAP4D
