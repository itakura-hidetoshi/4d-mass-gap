import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferCrossBoundaryTargetVarianceGenuineResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedJointLeakage
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSwapOneLinkConjugacy
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-!
# Cross-boundary current target mean on the genuine swap carrier

The right-hand side of the cross-boundary estimate is closed by PR #4961.
This file identifies the left-hand source-profile variance with a genuine
joint one-link leakage.

The current target mean is first identified pointwise with the existing
fixed-boundary target mean.  Its jointly measurable bounded L2 class is then
shown to be exactly the genuine right-target conditional expectation.  After
endpoint swap, the corresponding concrete function therefore represents the
swap of that genuine target projection.

Finally, the source-coordinate variance occurring in the cross-boundary
estimate is recognized pointwise as the ordinary right-source target variance
of this swapped mean.  The existing canonical-variance identity and exact
swap conjugacy turn its vacuum average into

  || P_right,target f - P_left,source (P_right,target f) ||^2.

No coefficient, cutoff, factor two, link-count factor, or volume factor is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance crossBoundaryCurrentTargetMeanSwapCarrierSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance crossBoundaryCurrentTargetMeanSwapCarrierSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance crossBoundaryCurrentTargetMeanSwapCarrierSecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance crossBoundaryCurrentTargetMeanSwapCarrierMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance crossBoundaryCurrentTargetMeanSwapCarrierBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance crossBoundaryCurrentTargetMeanSwapCarrierSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- At the actual current source value, the cross-boundary target mean is
literally the already-established fixed-boundary target mean.  The source
parameter disappears pointwise here; no source-invariance premise is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_eq_targetMean
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
        H N hN beta hbeta source target F B A =
      GroundStateSourceFixedPairEnergy.targetMean
        H N hN beta hbeta target F B A := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
    GroundStateSourceFixedPairEnergy.targetMean
  simp

/-- The current target mean is strongly measurable jointly in the two boundary
configurations. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_stronglyMeasurable_joint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) :
    StronglyMeasurable
      (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
          H N hN beta hbeta source target F z.1 z.2) := by
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
      StronglyMeasurable (Function.uncurry phi) :=
    hF.comp_measurable hPair
  have hInt :
      StronglyMeasurable (fun z => ∫ g, phi z g ∂κ z) :=
    hPhi.integral_kernel_prod_right
  have hEq :
      (fun z : J =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
          H N hN beta hbeta source target F z.1 z.2) =
        fun z => ∫ g, phi z g ∂κ z := by
    funext z
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryJointTargetFiberMarkovKernel_apply
        H N hN beta hbeta target z]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
      phi
    simp
  rw [hEq]
  exact hInt

/-- The current target mean retains the original bounded-core pointwise bound,
with the same real bound rather than its absolute value. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
        H N hN beta hbeta source target F B A‖ ≤ bound := by
  have hboundNonneg : 0 ≤ bound :=
    (norm_nonneg (F (B, A))).trans (hbound (B, A))
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_eq_targetMean
      H N hN beta hbeta source target F B A]
  simpa [abs_of_nonneg hboundNonneg] using
    GroundStateSourceFixedPairEnergy.targetMean_norm_le
      H N hN beta hbeta target F bound hbound B A

/-- The current target mean agrees joint-almost-everywhere with the canonical
mean representing the genuine right-target conditional expectation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_ae_eq_canonicalMean
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) :
    (fun z :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
        H N hN beta hbeta source target F z.1 z.2) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta]
      GroundStateCanonicalMean.canonicalMean
        H N hN beta hbeta target F := by
  let G := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let J := G × G
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
      H N hN beta hbeta
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel
      H N hN beta hbeta
  let M : J → ℝ := fun z =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
      H N hN beta hbeta source target F z.1 z.2
  let C : J → ℝ :=
    GroundStateCanonicalMean.canonicalMean
      H N hN beta hbeta target F
  letI : IsMarkovKernel κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel_isMarkovKernel
      H N hN beta hbeta
  have hM : StronglyMeasurable M := by
    simpa [M] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_stronglyMeasurable_joint
        H N hN beta hbeta source target F hF
  have hC : StronglyMeasurable C := by
    simpa [C] using
      GroundStateCanonicalMean.canonicalMean_stronglyMeasurable
        H N hN beta hbeta target F hF
  have hBase :=
    GroundStateSourceFixedPairEnergy.canonicalMean_ae_eq_targetMean
      H N hN beta hbeta target F hF
  have hNested :
      ∀ᵐ B ∂ν, ∀ᵐ A ∂κ B, M (B, A) = C (B, A) := by
    filter_upwards [hBase] with B hB
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel_apply
        H N hN beta hbeta B]
    filter_upwards [hB] with A hBA
    have hCurrent :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_eq_targetMean
        H N hN beta hbeta source target F B A
    exact hCurrent.trans hBA.symm
  have hComp :
      M =ᵐ[ν ⊗ₘ κ] C :=
    Measure.ae_compProd_of_ae_ae
      (measurableSet_eq_fun hM.measurable hC.measurable)
      hNested
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_eq_vacuum_compProd_kernelSectionMarkovKernel
      H N hN beta hbeta]
  exact hComp

/-- Concrete L2 carrier of the current target mean. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMeanL2
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
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
    H N hN beta hbeta
    (fun z =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
        H N hN beta hbeta source target F z.1 z.2)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_stronglyMeasurable_joint
      H N hN beta hbeta source target F hF)
    bound
    (fun z =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_norm_le
        H N hN beta hbeta source target F bound hbound z.1 z.2)

/-- The concrete current-target-mean L2 carrier is exactly the genuine
right-target one-link conditional expectation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMeanL2_eq_targetCondExpL2
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
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMeanL2
        H N hN beta hbeta source target F hF bound hbound =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN beta hbeta target
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound) := by
  let μJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let M := fun z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
      H N hN beta hbeta source target F z.1 z.2
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMeanL2
      H N hN beta hbeta source target F hF bound hbound
  let f :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
      H N hN beta hbeta F hF bound hbound
  let p :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta target f
  have hq :
      (fun z => q z) =ᵐ[μJ] M := by
    simpa [q, M,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMeanL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
        H N hN beta hbeta M
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_stronglyMeasurable_joint
          H N hN beta hbeta source target F hF)
        bound
        (fun z =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_norm_le
            H N hN beta hbeta source target F bound hbound z.1 z.2)
  have hp :
      (fun z => p z) =ᵐ[μJ]
        GroundStateCanonicalMean.canonicalMean
          H N hN beta hbeta target F := by
    simpa [p, f, μJ] using
      GroundStateCanonicalMean.condExpL2_coeFn_eq_canonicalMean
        H N hN beta hbeta target F hF bound hbound
  have hMC :
      M =ᵐ[μJ]
        GroundStateCanonicalMean.canonicalMean
          H N hN beta hbeta target F := by
    simpa [M, μJ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_ae_eq_canonicalMean
        H N hN beta hbeta source target F hF
  apply Lp.ext
  filter_upwards [hq, hp, hMC] with z hqz hpz hMCz
  change q z = p z
  rw [hqz, hpz, hMCz]

/-- Swap the current target mean as a concrete function on the joint carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
    H N hN beta hbeta source target F z.2 z.1

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean_stronglyMeasurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) :
    StronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean
        H N hN beta hbeta source target F) := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean]
    using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_stronglyMeasurable_joint
        H N hN beta hbeta source target F hF).comp_measurable measurable_swap

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean
        H N hN beta hbeta source target F z‖ ≤ bound := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_norm_le
      H N hN beta hbeta source target F bound hbound z.2 z.1

noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMeanL2
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
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
    H N hN beta hbeta
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean
      H N hN beta hbeta source target F)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean_stronglyMeasurable
      H N hN beta hbeta source target F hF)
    bound
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean_norm_le
      H N hN beta hbeta source target F bound hbound)

/-- The swapped concrete carrier is exactly endpoint swap applied to the
current-target-mean L2 carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMeanL2_eq_swap_currentTargetMeanL2
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
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMeanL2
        H N hN beta hbeta source target F hF bound hbound =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMeanL2
          H N hN beta hbeta source target F hF bound hbound) := by
  let μJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let hs :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_swap_measurePreserving
      H N hN beta hbeta
  let M := fun z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
      H N hN beta hbeta source target F z.1 z.2
  let MS :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean
      H N hN beta hbeta source target F
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMeanL2
      H N hN beta hbeta source target F hF bound hbound
  let qS :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMeanL2
      H N hN beta hbeta source target F hF bound hbound
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
      H N hN beta hbeta
  have hq :
      (fun z => q z) =ᵐ[μJ] M := by
    simpa [q, M,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMeanL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
        H N hN beta hbeta M
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_stronglyMeasurable_joint
          H N hN beta hbeta source target F hF)
        bound
        (fun z =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_norm_le
            H N hN beta hbeta source target F bound hbound z.1 z.2)
  have hqS :
      (fun z => qS z) =ᵐ[μJ] MS := by
    simpa [qS, MS,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMeanL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean
          H N hN beta hbeta source target F)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean_stronglyMeasurable
          H N hN beta hbeta source target F hF)
        bound
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean_norm_le
          H N hN beta hbeta source target F bound hbound)
  have hqSwap :
      (fun z => q z.swap) =ᵐ[μJ] (fun z => M z.swap) := by
    simpa [Function.comp_def] using
      hs.quasiMeasurePreserving.ae_eq_comp hq
  have hEcoe :
      (fun z => E q z) =ᵐ[μJ] (fun z => q z.swap) := by
    change
      (MeasureTheory.Lp.compMeasurePreserving Prod.swap hs q) =ᵐ[μJ]
        (fun z => q z.swap)
    simpa [Function.comp_def] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving q hs)
  apply Lp.ext
  filter_upwards [hqS, hEcoe, hqSwap] with z hqSz hEz hqz
  change qS z = E q z
  rw [hqSz, hEz, hqz]
  rfl

/-- Hence the swapped current-target-mean carrier is exactly the swap of the
genuine right-target conditional expectation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMeanL2_eq_swap_targetCondExpL2
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
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMeanL2
        H N hN beta hbeta source target F hF bound hbound =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta F hF bound hbound)) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMeanL2_eq_swap_currentTargetMeanL2
      H N hN beta hbeta source target F hF bound hbound,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMeanL2_eq_targetCondExpL2
      H N hN beta hbeta source target F hF bound hbound]

/-- Pointwise, the cross-boundary source variance is the ordinary source-link
conditional variance of the swapped current target mean. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_sourceSection_variance_eq_swappedCurrentTargetVariance
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    variance
        (fun k =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
            H N hN beta hbeta source target F
            (Function.update B source k) A)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta A B source) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
        H N hN beta hbeta source
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean
          H N hN beta hbeta source target F)
        A B := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean
  rfl

/-- Vacuum/section averaging of the cross-boundary source variance is exactly
the canonical source fiber variance of the swapped current target mean. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_sourceSection_variance_vacuum_lintegral_eq_canonicalFiberVarianceFunctional
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
        ENNReal.ofReal
          (variance
            (fun k =>
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
                H N hN beta hbeta source target F
                (Function.update B source k) A)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
              H N hN beta hbeta A B source))
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta source
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean
          H N hN beta hbeta source target F) := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean
      H N hN beta hbeta source target F
  have hS :
      StronglyMeasurable S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean_stronglyMeasurable
      H N hN beta hbeta source target F hF
  have hSb : ∀ z, ‖S z‖ ≤ bound :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean_norm_le
      H N hN beta hbeta source target F bound hbound
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance_vacuum_lintegral_eq_canonicalFiberVarianceFunctional
      H N hN beta hbeta source S hS bound hSb
  calc
    (∫⁻ A,
      (∫⁻ B,
        ENNReal.ofReal
          (variance
            (fun k =>
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
                H N hN beta hbeta source target F
                (Function.update B source k) A)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
              H N hN beta hbeta A B source))
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      ∫⁻ A,
        (∫⁻ B,
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
              H N hN beta hbeta source S A B)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
      apply lintegral_congr
      intro A
      apply lintegral_congr
      intro B
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_sourceSection_variance_eq_swappedCurrentTargetVariance
          H N hN beta hbeta source target F A B]
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta source S := by
      simpa [S] using hBase
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta source
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean
          H N hN beta hbeta source target F) := by
      rfl

/-- Exact LHS bridge: the vacuum-averaged cross-boundary source variance is the
genuine left-source leakage of the genuine right-target projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_sourceSection_variance_vacuum_lintegral_eq_leftLeakageNormSq
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
        ENNReal.ofReal
          (variance
            (fun k =>
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
                H N hN beta hbeta source target F
                (Function.update B source k) A)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
              H N hN beta hbeta A B source))
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound) -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
              H N hN beta hbeta source
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                H N hN beta hbeta target
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                  H N hN beta hbeta F hF bound hbound))‖ ^ 2) := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean
      H N hN beta hbeta source target F
  let hS :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean_stronglyMeasurable
      H N hN beta hbeta source target F hF
  let hSb :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMean_norm_le
      H N hN beta hbeta source target F bound hbound
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMeanL2
      H N hN beta hbeta source target F hF bound hbound
  let f :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
      H N hN beta hbeta F hF bound hbound
  let g :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta target f
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
      H N hN beta hbeta
  have hVariance :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_sourceSection_variance_vacuum_lintegral_eq_canonicalFiberVarianceFunctional
      H N hN beta hbeta source target F hF bound hbound
  have hq :
      q = E g := by
    simpa [q, E, g, f] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedCurrentTargetMeanL2_eq_swap_targetCondExpL2
        H N hN beta hbeta source target F hF bound hbound
  rw [hVariance]
  rw [
    GroundStateCanonicalMean.canonicalVariance_eq_condExpResidualNormSq
      H N hN beta hbeta source S hS bound hSb]
  change ENNReal.ofReal
      (‖q -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta source q‖ ^ 2) =
    ENNReal.ofReal
      (‖g -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
            H N hN beta hbeta source g‖ ^ 2)
  rw [hq]
  have hNorm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightResidual_norm_eq_left
      H N hN beta hbeta source (E g)
  have hNorm' :
      ‖E g -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta source (E g)‖ =
        ‖g -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
            H N hN beta hbeta source g‖ := by
    simpa [E] using hNorm.symm
  rw [hNorm']

end

end MathlibAnalytic
end MGAP4D
