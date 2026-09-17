import MGAP4D.MathlibAnalytic.FinitePositiveWeightCanonicalVariationDefiniteness
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioTwoStepRemoteResidualColumn
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateIterateSuperposition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

/-- Finite-coordinate telescoping needs only a finite coordinate carrier, not a
finite value space.  This is the continuous-state analogue needed for SU(N)
boundary configurations. -/
theorem finiteProductUpdateVariation_difference_abs_le_sum
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    (f : (ι → G) → ℝ)
    (variation : ι → ℝ)
    (hVariation :
      ∀ (e : ι) (C : ι → G) (u v : G),
        |f (Function.update C e u) - f (Function.update C e v)| ≤ variation e)
    (A B : ι → G) :
    |f A - f B| ≤ ∑ e : ι, variation e := by
  classical
  have hAgreeBound
      (e : ι)
      (X Y : ι → G)
      (hAgree : FiniteProductAgreeOff X Y e) :
      |f X - f Y| ≤ variation e := by
    have hRaw := hVariation e X (X e) (Y e)
    rw [
      finiteProductUpdate_current,
      finiteProductUpdate_right_of_agreeOff X Y e hAgree] at hRaw
    exact hRaw
  have hPatch :
      ∀ s : Finset ι,
        |f A - f (finiteProductPatch A B s)| ≤
          ∑ e ∈ s, variation e := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert e s he ih =>
        have hStep :
            |f (finiteProductPatch A B s) -
                f (finiteProductPatch A B (insert e s))| ≤
              variation e :=
          hAgreeBound e
            (finiteProductPatch A B s)
            (finiteProductPatch A B (insert e s))
            (finiteProductPatch_agreeOff_insert A B s e)
        have hSplit :
            f A - f (finiteProductPatch A B (insert e s)) =
              (f A - f (finiteProductPatch A B s)) +
                (f (finiteProductPatch A B s) -
                  f (finiteProductPatch A B (insert e s))) := by
          ring
        rw [hSplit]
        calc
          |(f A - f (finiteProductPatch A B s)) +
              (f (finiteProductPatch A B s) -
                f (finiteProductPatch A B (insert e s)))| ≤
              |f A - f (finiteProductPatch A B s)| +
                |f (finiteProductPatch A B s) -
                  f (finiteProductPatch A B (insert e s))| :=
            abs_add_le _ _
          _ ≤ (∑ i ∈ s, variation i) + variation e :=
            add_le_add ih hStep
          _ = ∑ i ∈ insert e s, variation i := by
            rw [Finset.sum_insert he]
            ring
  simpa using hPatch Finset.univ

/-- If a strongly measurable observable has a declared coordinatewise update
variation profile on a finite coordinate carrier, then its expectations under
any two probability measures differ by at most twice the total variation
profile.  The value space itself may be infinite or continuous. -/
theorem probabilityMeasure_integral_difference_abs_le_two_mul_updateVariationSum
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [MeasurableSpace G]
    (f : (ι → G) → ℝ)
    (hF : StronglyMeasurable f)
    (variation : ι → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (hVariation :
      ∀ (e : ι) (C : ι → G) (u v : G),
        |f (Function.update C e u) - f (Function.update C e v)| ≤ variation e)
    (μ ν : Measure (ι → G))
    (hμ : IsProbabilityMeasure μ)
    (hν : IsProbabilityMeasure ν)
    (A₀ : ι → G) :
    |(∫ A, f A ∂μ) - (∫ A, f A ∂ν)| ≤
      2 * ∑ e : ι, variation e := by
  classical
  let M : ℝ := ∑ e : ι, variation e
  letI : IsProbabilityMeasure μ := hμ
  letI : IsProbabilityMeasure ν := hν
  have hMNonneg : 0 ≤ M := by
    dsimp [M]
    exact Finset.sum_nonneg (fun e _ => hVariationNonneg e)
  have hGlobal (A : ι → G) : |f A - f A₀| ≤ M := by
    dsimp [M]
    exact
      finiteProductUpdateVariation_difference_abs_le_sum
        f variation hVariation A A₀
  have hCenteredMeas :
      StronglyMeasurable (fun A : ι → G => f A - f A₀) :=
    hF.sub stronglyMeasurable_const
  have hCenteredIntMu : Integrable (fun A : ι → G => f A - f A₀) μ := by
    apply (integrable_const M).mono hCenteredMeas.aestronglyMeasurable
    filter_upwards with A
    simpa [Real.norm_eq_abs, abs_of_nonneg hMNonneg] using hGlobal A
  have hCenteredIntNu : Integrable (fun A : ι → G => f A - f A₀) ν := by
    apply (integrable_const M).mono hCenteredMeas.aestronglyMeasurable
    filter_upwards with A
    simpa [Real.norm_eq_abs, abs_of_nonneg hMNonneg] using hGlobal A
  have hFIntMu : Integrable f μ := by
    have hSum := hCenteredIntMu.add (integrable_const (μ := μ) (f A₀))
    simpa using hSum
  have hFIntNu : Integrable f ν := by
    have hSum := hCenteredIntNu.add (integrable_const (μ := ν) (f A₀))
    simpa using hSum
  have hCenterEqMu :
      (∫ A : ι → G, f A - f A₀ ∂μ) =
        (∫ A : ι → G, f A ∂μ) - f A₀ := by
    rw [integral_sub hFIntMu (integrable_const (μ := μ) (f A₀))]
    simp
  have hCenterEqNu :
      (∫ A : ι → G, f A - f A₀ ∂ν) =
        (∫ A : ι → G, f A ∂ν) - f A₀ := by
    rw [integral_sub hFIntNu (integrable_const (μ := ν) (f A₀))]
    simp
  have hCenteredBoundMu :
      |∫ A : ι → G, f A - f A₀ ∂μ| ≤ M := by
    have hNorm :=
      norm_integral_le_of_norm_le_const
        (μ := μ)
        (C := M)
        (f := fun A : ι → G => f A - f A₀)
        (ae_of_all _ fun A => by
          simpa [Real.norm_eq_abs] using hGlobal A)
    simpa [Real.norm_eq_abs] using hNorm
  have hCenteredBoundNu :
      |∫ A : ι → G, f A - f A₀ ∂ν| ≤ M := by
    have hNorm :=
      norm_integral_le_of_norm_le_const
        (μ := ν)
        (C := M)
        (f := fun A : ι → G => f A - f A₀)
        (ae_of_all _ fun A => by
          simpa [Real.norm_eq_abs] using hGlobal A)
    simpa [Real.norm_eq_abs] using hNorm
  have hRewrite :
      (∫ A : ι → G, f A ∂μ) - (∫ A : ι → G, f A ∂ν) =
        (∫ A : ι → G, f A - f A₀ ∂μ) -
          (∫ A : ι → G, f A - f A₀ ∂ν) := by
    rw [hCenterEqMu, hCenterEqNu]
    ring
  rw [hRewrite]
  calc
    |(∫ A : ι → G, f A - f A₀ ∂μ) -
        (∫ A : ι → G, f A - f A₀ ∂ν)| ≤
      |∫ A : ι → G, f A - f A₀ ∂μ| +
        |∫ A : ι → G, f A - f A₀ ∂ν| := by
          simpa using
            abs_sub_le
              (∫ A : ι → G, f A - f A₀ ∂μ)
              0
              (∫ A : ι → G, f A - f A₀ ∂ν)
    _ ≤ M + M := add_le_add hCenteredBoundMu hCenteredBoundNu
    _ = 2 * M := by ring
    _ = 2 * ∑ e : ι, variation e := by rfl

local instance fixedRightTargetRatioTwoStepTerminalLeftVariationMassSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance fixedRightTargetRatioTwoStepTerminalLeftVariationMassSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance fixedRightTargetRatioTwoStepTerminalLeftVariationMassSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance fixedRightTargetRatioTwoStepTerminalLeftVariationMassSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance fixedRightTargetRatioTwoStepTerminalLeftVariationMassSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance fixedRightTargetRatioTwoStepTerminalLeftVariationMassSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The exact two-step terminal response for one target is controlled by the
left-coordinate total mass of the propagated singleton target-ratio variation.
This removes the opaque stationary-measure response without assuming a global
contraction or a finite SU(N) state space. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs_le_two_mul_leftVariationTotal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs
        H N hN beta hbeta B target source g₁ g₂ h k ≤
      2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
              H beta target)
            2 (Sum.inl e) := by
  rfl

/-- Summing the targetwise terminal descent over the remote C5 set and using
exact finite superposition turns the whole two-step terminal remote column into
one aggregate propagated left-total-mass obstruction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalRemoteColumn_le_two_mul_remoteAggregateLeftVariationTotal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalRemoteColumn
        H N hN beta hbeta B source distinguishedTarget g₁ g₂ h k ≤
      2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
              H beta source distinguishedTarget)
            2 (Sum.inl e) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
