import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferCrossBoundaryCurrentTargetVarianceStationarity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSwapSymmetry
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointKernelSectionLIntegralDisintegration
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Tactic

/-!
# Cross-boundary target variance on the genuine joint carrier

PR #4959 proves exact source-update stationarity for the current target
variance at every fixed opposite boundary.  To outer-integrate that result we
must recognize the post-stationarity average in the swapped
vacuum/kernel-section presentation and transport it back to the ordinary
orientation of the genuine joint law.

This file proves joint measurability of the current target variance by
constructing its literal target fiber as a Markov kernel over the complete
two-boundary configuration.  The exact endpoint-swap symmetry and the exact
vacuum/kernel-section disintegration then identify the swapped and ordinary
outer averages.

No estimate and no new coefficient is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance crossBoundaryTargetVarianceJointSwapSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance crossBoundaryTargetVarianceJointSwapSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance crossBoundaryTargetVarianceJointSwapSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance crossBoundaryTargetVarianceJointSwapSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance crossBoundaryTargetVarianceJointSwapSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance crossBoundaryTargetVarianceJointSwapSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Target-fiber ENNReal weight parameterized by the complete two-boundary
configuration. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberENNRealWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkENNRealWeight
    H N hN beta hbeta z.1 z.2 target g

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberENNRealWeight_measurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (Function.uncurry
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberENNRealWeight
          H N hN beta hbeta target)) := by
  let G := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let J := G × G
  let U := Matrix.specialUnitaryGroup (Fin N) ℂ
  let w : J → ℝ := fun z =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
      H N hN beta hbeta z.1 z.2
  let updateRight : J × U → G := fun p =>
    Function.update p.1.2 target p.2
  let pairMap : J × U → J := fun p => (p.1.1, updateRight p)
  have hw : Measurable w := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_joint_continuous
        H N hN beta hbeta).measurable
  have hUpdateRight : Measurable updateRight := by
    dsimp [updateRight]
    refine measurable_pi_lambda _ ?_
    intro i
    by_cases hi : i = target
    · subst i
      simpa using (measurable_snd : Measurable (fun p : J × U => p.2))
    · simpa [Function.update, hi] using
        ((measurable_pi_apply i).comp
          ((measurable_snd : Measurable (fun z : J => z.2)).comp
            (measurable_fst : Measurable (fun p : J × U => p.1))))
  have hPairMap : Measurable pairMap := by
    have hLeft : Measurable (fun p : J × U => p.1.1) :=
      (measurable_fst : Measurable (fun z : J => z.1)).comp
        (measurable_fst : Measurable (fun p : J × U => p.1))
    exact hLeft.prodMk hUpdateRight
  have hWeight : Measurable (fun p : J × U => w (pairMap p)) :=
    hw.comp hPairMap
  change Measurable (fun p : J × U => ENNReal.ofReal (w (pairMap p)))
  exact ENNReal.continuous_ofReal.measurable.comp hWeight

noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMass
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ≥0∞ :=
  doobWeightMass
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberENNRealWeight
      H N hN beta hbeta target z)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMass_measurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMass
        H N hN beta hbeta target) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMass
    doobWeightMass
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberENNRealWeight_measurable
      H N hN beta hbeta target).lintegral_kernel_prod_right
      (κ :=
        Kernel.const
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))

noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberDensity
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberENNRealWeight
      H N hN beta hbeta target z g /
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMass
      H N hN beta hbeta target z

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberDensity_measurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (Function.uncurry
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberDensity
          H N hN beta hbeta target)) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberDensity
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberENNRealWeight_measurable
      H N hN beta hbeta target).div
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMass_measurable
        H N hN beta hbeta target).comp measurable_fst)

noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Kernel
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  Kernel.withDensity
    (Kernel.const
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberDensity
      H N hN beta hbeta target)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMarkovKernel_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMarkovKernel
        H N hN beta hbeta target z =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta z.1 z.2 target := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMarkovKernel
  rw [
    Kernel.withDensity_apply _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberDensity_measurable
        H N hN beta hbeta target)]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberDensity
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMass
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
    doobWeightedMeasure
  rfl

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMarkovKernel_isMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    IsMarkovKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMarkovKernel
        H N hN beta hbeta target) := by
  constructor
  intro z
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMarkovKernel_apply
      H N hN beta hbeta target z]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedSourceFiber_isProbabilityMeasure
      H N hN beta hbeta target z.2 z.1

/-- The current target variance is strongly measurable on the genuine
two-boundary configuration space. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance_stronglyMeasurable_joint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    StronglyMeasurable
      (fun (z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
          H N hN beta hbeta target F z.1 z.2) := by
  let G := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let J := G × G
  let U := Matrix.specialUnitaryGroup (Fin N) ℂ
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMarkovKernel
      H N hN beta hbeta target
  let phi : J → U → ℝ := fun z g =>
    F (z.1, Function.update z.2 target g)
  letI : IsMarkovKernel κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMarkovKernel_isMarkovKernel
      H N hN beta hbeta target
  have hUpdateRight :
      Measurable (fun p : J × U => Function.update p.1.2 target p.2) := by
    refine measurable_pi_lambda _ ?_
    intro i
    by_cases hi : i = target
    · subst i
      simpa using (measurable_snd : Measurable (fun p : J × U => p.2))
    · simpa [Function.update, hi] using
        ((measurable_pi_apply i).comp
          ((measurable_snd : Measurable (fun z : J => z.2)).comp
            (measurable_fst : Measurable (fun p : J × U => p.1))))
  have hPair :
      Measurable (fun p : J × U =>
        (p.1.1, Function.update p.1.2 target p.2)) := by
    have hLeft : Measurable (fun p : J × U => p.1.1) :=
      (measurable_fst : Measurable (fun z : J => z.1)).comp
        (measurable_fst : Measurable (fun p : J × U => p.1))
    exact hLeft.prodMk hUpdateRight
  have hPhi :
      StronglyMeasurable (Function.uncurry phi) := by
    exact hF.comp_measurable hPair
  have hPhiSq :
      StronglyMeasurable (Function.uncurry (fun z g => (phi z g) ^ 2)) := by
    simpa only [Function.uncurry_apply_pair] using hPhi.pow 2
  have hFirst :
      StronglyMeasurable (fun z => ∫ g, phi z g ∂κ z) :=
    hPhi.integral_kernel_prod_right
  have hSecond :
      StronglyMeasurable (fun z => ∫ g, (phi z g) ^ 2 ∂κ z) :=
    hPhiSq.integral_kernel_prod_right
  have hMemLp : ∀ z : J, MemLp (phi z) 2 (κ z) := by
    intro z
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMarkovKernel_apply
        H N hN beta hbeta target z]
    simpa [phi] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection_memLp_two
        H N hN beta hbeta target target F hF bound hbound
        z.1 z.2 (z.1 target)
  have hEq :
      (fun (z : J) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
          H N hN beta hbeta target F z.1 z.2) =
        fun (z : J) =>
          (∫ g, (phi z g) ^ 2 ∂κ z) -
            (∫ g, phi z g ∂κ z) ^ 2 := by
    funext z
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
    rw [
      ← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMarkovKernel_apply
        H N hN beta hbeta target z]
    simpa only [phi, Pi.pow_apply] using variance_eq_sub (hMemLp z)
  rw [hEq]
  exact hSecond.sub (hFirst.pow 2)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance_ofReal_measurable_joint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    Measurable
      (fun (z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
            H N hN beta hbeta target F z.1 z.2)) := by
  exact
    ENNReal.continuous_ofReal.measurable.comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance_stronglyMeasurable_joint
        H N hN beta hbeta target F hF bound hbound).measurable

/-- The current target variance has the same vacuum/kernel-section average in
the swapped and ordinary endpoint orientations. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance_swapped_vacuum_kernelSection_lintegral_eq_normal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ A,
      (∫⁻ B,
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
            H N hN beta hbeta target F B A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      ∫⁻ B,
        (∫⁻ A,
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
              H N hN beta hbeta target F B A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta B)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
  let Phi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
          H N hN beta hbeta target F z.1 z.2)
  have hPhi : Measurable Phi := by
    simpa [Phi] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance_ofReal_measurable_joint
        H N hN beta hbeta target F hF bound hbound
  have hNormal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_lintegral_eq_vacuum_kernelSection
      H N hN beta hbeta Phi hPhi
  have hSwapped :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_lintegral_eq_vacuum_kernelSection
      H N hN beta hbeta (fun z => Phi z.swap) (hPhi.comp measurable_swap)
  have hSym :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_lintegral_swap
      H N hN beta hbeta Phi
  calc
    (∫⁻ A,
      (∫⁻ B,
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
            H N hN beta hbeta target F B A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      ∫⁻ z, Phi z.swap
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta := by
      simpa [Phi] using hSwapped.symm
    _ =
      ∫⁻ z, Phi z
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta := hSym
    _ =
      ∫⁻ B,
        (∫⁻ A,
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
              H N hN beta hbeta target F B A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta B)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
      simpa [Phi] using hNormal

/-- After source heat-bath averaging, the cross-boundary target-variance RHS
returns exactly to the ordinary joint orientation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance_sourceUpdate_vacuum_lintegral_eq_normal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ A,
      (∫⁻ B,
        (∫⁻ k,
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
              H N hN beta hbeta target F
              (Function.update B source k) A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
            H N hN beta hbeta A B source)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      ∫⁻ B,
        (∫⁻ A,
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
              H N hN beta hbeta target F B A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta B)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
  calc
    (∫⁻ A,
      (∫⁻ B,
        (∫⁻ k,
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
              H N hN beta hbeta target F
              (Function.update B source k) A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
            H N hN beta hbeta A B source)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      ∫⁻ A,
        (∫⁻ B,
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
              H N hN beta hbeta target F B A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
      apply lintegral_congr
      intro A
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance_sourceUpdate_lintegral_eq_current
          H N hN beta hbeta source target F hF bound hbound A
    _ =
      ∫⁻ B,
        (∫⁻ A,
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
              H N hN beta hbeta target F B A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta B)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance_swapped_vacuum_kernelSection_lintegral_eq_normal
        H N hN beta hbeta target F hF bound hbound

end

end MathlibAnalytic
end MGAP4D
