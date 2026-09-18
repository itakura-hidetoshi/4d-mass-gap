import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRemoteVacuumOnlyDoobBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTargetWorstCaseCrossRatioInfluenceMajorant
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureCrossRatioInfluenceMajorant
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumFiberDistortion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance remoteConditionalCrossRatioSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance remoteConditionalCrossRatioSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance remoteConditionalCrossRatioSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance remoteConditionalCrossRatioSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance remoteConditionalCrossRatioSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- For two geometrically remote spatial links, changing the source value in
the continuous vacuum fiber weight changes the normalized one-link Doob law by
at most the targetwise worst-case transformed cross-ratio majorant.

The raw one-slab law is kept fixed.  The theorem therefore isolates exactly
the model-specific normalization step needed to turn the continuous-vacuum
cross-ratio estimate into bounded-test control.  No supremum attainment or
compactness maximizer is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRemoteDoob_boundedTest_integral_difference_abs_le_worstCaseCrossRatioInfluenceMajorant
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : StronglyMeasurable phi)
    (hphiBound : ∀ g, |phi g| ≤ 1) :
    |(∫ g, phi g ∂doobWeightedMeasure
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure
            H N beta C A target)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
            H N hN beta hbeta (Function.update A source u) target)) -
      (∫ g, phi g ∂doobWeightedMeasure
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure
            H N beta C A target)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
            H N hN beta hbeta (Function.update A source v) target))| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
        H N hN beta hbeta A target source := by
  classical
  let μ : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure
      H N beta C A target
  let w : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
      H N hN beta hbeta (Function.update A source u) target
  let vWeight : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
      H N hN beta hbeta (Function.update A source v) target
  let radius :
      Matrix.specialUnitaryGroup (Fin N) ℂ →
      Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun x y =>
      Real.log
        (1 + Real.exp (16 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
            H N hN beta hbeta A target source x y u v)
  let M : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
      H N hN beta hbeta A target source
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure_isProbabilityMeasure
      H N hN beta hbeta C A target
  let dW :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberDistortionData
      H N hN beta hbeta μ (Function.update A source u) target
  let dV :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberDistortionData
      H N hN beta hbeta μ (Function.update A source v) target
  have hMNonneg : 0 ≤ M := by
    have hChosenNonneg :
        0 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant
            H N hN beta hbeta A target source 1 1 1 1 := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant
      exact
        finitePositiveWeightCrossRatioInfluenceTransform_nonneg _
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioRadius_nonneg
            H N hN beta hbeta A target source 1 1 1 1)
    have hChosenLe :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant_le_worstCase
        H N hN beta hbeta A target source 1 1 1 1
    exact hChosenNonneg.trans (by simpa [M] using hChosenLe)
  have hMLeTwo : M ≤ 2 := by
    dsimp [M]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
    apply csSup_le
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorantSet_nonempty
        H N hN beta hbeta A target source)
    intro x hx
    rcases hx with ⟨g₁, g₂, h, k, rfl⟩
    exact
      (finitePositiveWeightCrossRatioInfluenceTransform_lt_two
        (Real.log
          (1 + Real.exp (16 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
              H N hN beta hbeta A target source g₁ g₂ h k))).le
  have hRadiusNonneg : ∀ x y, 0 ≤ radius x y := by
    intro x y
    simpa [radius] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioRadius_nonneg
        H N hN beta hbeta A target source x y u v
  have hInfluence : ∀ x y,
      finitePositiveWeightCrossRatioInfluenceTransform (radius x y) ≤ M := by
    intro x y
    simpa [
      radius,
      M,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant_le_worstCase
        H N hN beta hbeta A target source x y u v
  have hwtop : ∀ x, w x ≠ ∞ := by
    intro x
    have hx :
        w x ≤ dW.M := by
      simpa [w, dW] using dW.upper x
    exact ne_of_lt (lt_of_le_of_lt hx dW.upper_finite)
  have hvtop : ∀ x, vWeight x ≠ ∞ := by
    intro x
    have hx :
        vWeight x ≤ dV.M := by
      simpa [vWeight, dV] using dV.upper x
    exact ne_of_lt (lt_of_le_of_lt hx dV.upper_finite)
  have hMassW0 : doobWeightMass μ w ≠ 0 := by
    have hLower : dW.m ≤ doobWeightMass μ w := by
      apply doobWeightMass_lower_bound
      intro x
      simpa [w, dW] using dW.lower x
    exact ne_of_gt (lt_of_lt_of_le dW.lower_pos hLower)
  have hMassWtop : doobWeightMass μ w ≠ ∞ := by
    have hUpper : doobWeightMass μ w ≤ dW.M := by
      apply doobWeightMass_upper_bound
      intro x
      simpa [w, dW] using dW.upper x
    exact ne_of_lt (lt_of_le_of_lt hUpper dW.upper_finite)
  have hMassV0 : doobWeightMass μ vWeight ≠ 0 := by
    have hLower : dV.m ≤ doobWeightMass μ vWeight := by
      apply doobWeightMass_lower_bound
      intro x
      simpa [vWeight, dV] using dV.lower x
    exact ne_of_gt (lt_of_lt_of_le dV.lower_pos hLower)
  have hMassVtop : doobWeightMass μ vWeight ≠ ∞ := by
    have hUpper : doobWeightMass μ vWeight ≤ dV.M := by
      apply doobWeightMass_upper_bound
      intro x
      simpa [vWeight, dV] using dV.upper x
    exact ne_of_lt (lt_of_le_of_lt hUpper dV.upper_finite)
  have hcross : ∀ x y,
      w x * vWeight y ≤
        ENNReal.ofReal (Real.exp (radius x y)) * vWeight x * w y := by
    intro x y
    let omega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta
    let a : ℝ :=
      omega (Function.update (Function.update A source u) target x)
    let b : ℝ :=
      omega (Function.update (Function.update A source v) target y)
    let c : ℝ :=
      omega (Function.update (Function.update A source v) target x)
    let d : ℝ :=
      omega (Function.update (Function.update A source u) target y)
    have ha : 0 < a := by
      simpa [a, omega] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
          H N hN beta hbeta
          (Function.update (Function.update A source u) target x)
    have hb : 0 < b := by
      simpa [b, omega] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
          H N hN beta hbeta
          (Function.update (Function.update A source v) target y)
    have hc : 0 < c := by
      simpa [c, omega] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
          H N hN beta hbeta
          (Function.update (Function.update A source v) target x)
    have hd : 0 < d := by
      simpa [d, omega] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
          H N hN beta hbeta
          (Function.update (Function.update A source u) target y)
    have hRatio :
        a * b / (c * d) ≤ Real.exp (radius x y) := by
      simpa [a, b, c, d, omega, radius] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_crossRatio_le_exp_log_one_add_exp_sixteen_mul_fixedRightTargetRatioResponseAbs
          H N hN beta hbeta A hne hNoShare u v x y
    have hMul :
        a * b ≤ Real.exp (radius x y) * (c * d) := by
      exact (div_le_iff₀ (mul_pos hc hd)).mp hRatio
    have hENN :
        ENNReal.ofReal a * ENNReal.ofReal b ≤
          ENNReal.ofReal (Real.exp (radius x y)) *
            ENNReal.ofReal c * ENNReal.ofReal d := by
      calc
        ENNReal.ofReal a * ENNReal.ofReal b =
            ENNReal.ofReal (a * b) := by
              rw [ENNReal.ofReal_mul ha.le]
        _ ≤ ENNReal.ofReal (Real.exp (radius x y) * (c * d)) :=
          ENNReal.ofReal_le_ofReal hMul
        _ = ENNReal.ofReal (Real.exp (radius x y)) *
              ENNReal.ofReal c * ENNReal.ofReal d := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
          rw [ENNReal.ofReal_mul hc.le]
          ac_rfl
    simpa [
      w,
      vWeight,
      a,
      b,
      c,
      d,
      omega,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using hENN
  have hDoob :=
    doobWeightedMeasure_boundedTest_integral_difference_abs_le_crossRatioInfluenceMajorant
      μ w vWeight radius M
      hMNonneg hMLeTwo hRadiusNonneg hInfluence
      hwtop hvtop
      hMassW0 hMassWtop hMassV0 hMassVtop
      hcross phi hphi hphiBound
  simpa [μ, w, vWeight, M] using hDoob

/-- The actual off-target one-link reference conditional laws inherit the same
remote bounded-test bound.  The two source-updated laws are first rewritten to
a common raw one-slab law with two continuous-vacuum Doob weights; the preceding
theorem then supplies the targetwise worst-case cross-ratio control.

The outer fixed-right reference parameters select the common raw law only.
The influence majorant is attached to the actual updated pair
`(fiber, backgroundFiber)` in the base configuration `A`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_remote_boundedTest_integral_difference_abs_le_worstCaseCrossRatioInfluenceMajorant
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedTarget distinguishedSource fiber backgroundFiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hFiberTarget : fiber ≠ distinguishedTarget)
    (hBackgroundFiberDistinct : backgroundFiber ≠ fiber)
    (hNoShare : ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H fiber backgroundFiber)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : StronglyMeasurable phi) (hphiBound : ∀ g, |phi g| ≤ 1) :
    |(∫ g, phi g ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
        (Function.update A backgroundFiber u)) -
      (∫ g, phi g ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
        (Function.update A backgroundFiber v))| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
        H N hN beta hbeta A fiber backgroundFiber := by

  have hPair :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_remote_pair_eq_commonRaw_vacuumDoob
      H N hN beta hbeta B
      distinguishedTarget distinguishedSource fiber backgroundFiber
      hFiberTarget hBackgroundFiberDistinct hNoShare
      k g₂ u v A
  rw [hPair.1, hPair.2]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRemoteDoob_boundedTest_integral_difference_abs_le_worstCaseCrossRatioInfluenceMajorant
      H N hN beta hbeta
      (Function.update B distinguishedSource k) A
      (target := fiber) (source := backgroundFiber)
      hBackgroundFiberDistinct.symm hNoShare u v
      phi hphi hphiBound

end

end MathlibAnalytic
end MGAP4D
