import MGAP4D.MathlibAnalytic.DoobWeightedMeasurableMarkovKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionContinuousDensity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumFiberDistortion
import Mathlib.Tactic

/-!
# Measurable fixed-right ground-state kernel-section Fubini bridge

The local-mean carrier from PR #4738 lives in the fixed-right ground-state
kernel-section probability law.  The genuine sweep-stage residual lives in the
two-boundary ground-state joint law.  Before comparing their energies, the
fixed-right family must be realized as a measurable kernel and its outer mass
must remain explicit.

This file supplies exactly that measure-theoretic bridge.  The canonical
continuous fixed-right section weight

  w(C,A) = Ω(A) K(A,C)

is jointly continuous.  Its Haar mass is exactly

  ||T|| * Ω(C).

Hence the generic measurable Doob-kernel theorem gives an everywhere-defined
Markov kernel agreeing Haar-a.e. with the literal normalized kernel-section
probability measures and an exact weighted Tonelli/Fubini identity.

No pointwise domination of a fixed section by a global L2 norm is asserted,
and no source/target heat-bath commutation is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

local instance groundStateKernelSectionMarkovFubiniSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateKernelSectionMarkovFubiniSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The canonical continuous fixed-right kernel-section weight is jointly
continuous in the retained right boundary and the sampled left boundary. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_joint_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Continuous
      (fun p :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
          H N hN beta hbeta p.1 p.2) := by
  let G := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let omega : G → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let kernel : G × G → ℝ := fun q =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta q.1 q.2
  have hOmega : Continuous omega := by
    simpa [omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
        H N hN beta hbeta
  have hKernel : Continuous kernel := by
    simpa [kernel] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        H N beta
  have hSwap : Continuous (fun p : G × G => (p.2, p.1)) :=
    continuous_snd.prodMk continuous_fst
  change Continuous (fun p : G × G => omega p.2 * kernel (p.2, p.1))
  exact (hOmega.comp continuous_snd).mul (hKernel.comp hSwap)

/-- Every continuous fixed-right kernel-section weight is Haar-integrable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Integrable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
        H N hN beta hbeta C)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integrable
      H N hN beta hbeta C).congr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_ae_eq_continuousWeight
        H N hN beta hbeta C)

/-- The canonical continuous fixed-right kernel-section weight is strictly
positive at every left boundary. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
        H N hN beta hbeta C A := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
  exact mul_pos
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta A)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta A C)

/-- The continuous section has the same exact physical mass as the legacy
almost-everywhere representative: top transfer norm times the continuous
vacuum value at the retained right boundary. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (∫ A,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
        H N hN beta hbeta C A
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta C := by
  calc
    (∫ A,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
        H N hN beta hbeta C A
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
      ∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
          H N hN beta hbeta C A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
          exact integral_congr_ae
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_ae_eq_continuousWeight
              H N hN beta hbeta C).symm
    _ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta C :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integral
        H N hN beta hbeta C

/-- The ENNReal Doob mass of the continuous fixed-right section is exactly the
physical section mass. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_doobWeightMass
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    doobWeightMass
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        (fun A =>
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
              H N hN beta hbeta C A)) =
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖ *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta C) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
      H N hN beta hbeta C
  have hwInt : Integrable w μ := by
    simpa [μ, w] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_integrable
        H N hN beta hbeta C
  have hwNonneg : ∀ᵐ A ∂μ, 0 ≤ w A :=
    Filter.Eventually.of_forall fun A =>
      le_of_lt
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_pos
          H N hN beta hbeta C A)
  calc
    doobWeightMass μ (fun A => ENNReal.ofReal (w A)) =
        ENNReal.ofReal (∫ A, w A ∂μ) :=
      realIntegralWeighted_doobWeightMass_eq_ofReal_integral μ w hwInt hwNonneg
    _ =
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H N hN beta hbeta‖ *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
              H N hN beta hbeta C) := by
      congr 1
      simpa [μ, w] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_integral
          H N hN beta hbeta C

/-- The fixed-right continuous kernel sections admit a measurable Markov-kernel
representative and exact weighted Fubini identity over spatial Haar measure.

The returned kernel agrees Haar-a.e. with the literal normalized fixed-right
kernel-section probability law.  The outer mass is exposed as
`||T|| * Ω(C)`, ready for the next genuine-joint disintegration step. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuous_exists_markovKernel_lintegral_identity
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
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
                  H N hN beta hbeta z.1 z.2) *
              F z.1 z.2
          ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) =
          ∫⁻ C,
            ENNReal.ofReal
                (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
                    H N hN beta hbeta‖ *
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
                    H N hN beta hbeta C) *
              (∫⁻ A, F C A ∂κ C)
            ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let w := fun
      (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
    ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
        H N hN beta hbeta C A)
  have hw : AEMeasurable (Function.uncurry w) (μ.prod μ) := by
    exact
      (ENNReal.continuous_ofReal.comp
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_joint_continuous
          H N hN beta hbeta)).measurable.aemeasurable
  have hF' : AEMeasurable (Function.uncurry F) (μ.prod μ) := by
    simpa [μ] using hF
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hμ : μ ≠ 0 := by
    intro hzero
    have huniv : μ Set.univ = 1 := measure_univ
    rw [hzero] at huniv
    simpa using huniv
  have hMass :
      ∀ᵐ C ∂μ,
        0 < doobWeightMass μ (w C) ∧ doobWeightMass μ (w C) < ∞ := by
    exact Filter.Eventually.of_forall fun C => by
      rw [show
        doobWeightMass μ (w C) =
          ENNReal.ofReal
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
                H N hN beta hbeta‖ *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
                H N hN beta hbeta C) by
          simpa [μ, w] using
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_doobWeightMass
              H N hN beta hbeta C]
      refine ⟨ENNReal.ofReal_pos.mpr ?_, ENNReal.ofReal_lt_top⟩
      exact mul_pos
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
          H N hN beta hbeta C)
  obtain ⟨κ, hκ, hκae, hid⟩ :=
    exists_doobWeightedMarkovKernel_lintegral_identity
      μ μ w F hw hF' hμ hMass
  refine ⟨κ, hκ, ?_, ?_⟩
  · simpa [μ, w,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure,
      realIntegralWeightedProbabilityMeasure] using hκae
  · have hmassEq : ∀ C,
        doobWeightMass μ (w C) =
          ENNReal.ofReal
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
                H N hN beta hbeta‖ *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
                H N hN beta hbeta C) := by
      intro C
      simpa [μ, w] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_doobWeightMass
          H N hN beta hbeta C
    simpa only [μ, w, hmassEq] using hid

end

end MathlibAnalytic
end MGAP4D
