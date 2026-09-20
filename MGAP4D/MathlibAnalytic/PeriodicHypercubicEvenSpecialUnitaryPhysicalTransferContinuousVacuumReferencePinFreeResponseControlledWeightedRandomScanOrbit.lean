import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceResponseControlledWeightedRandomScanOrbit
import Mathlib.Tactic

/-!
# Pin-free response-controlled weighted random-scan orbit

The distinguished-target remote cross-ratio theorem removes the artificial
target pin from the response-controlled physical left kernel.  This file
propagates that improvement into the weighted-column random-scan machinery.

For the target-centered exponential weight
  W_T(x) = s ^ dist(T,x)
and a nonnegative fixed-right response profile R satisfying
  sum_x R(x,y) W_T(x) <= M W_T(y),
the pin-free kernel has weighted-column coefficient
  c_R^pf = 18 * eta(beta) * s^2 + exp(16 beta) * M.

There is no standalone eta(beta) term.

The file then defines the corresponding abstract random-scan variation update
and iterate, and proves the one-step and finite-step weighted bounds with the
pin-free coefficient.  No contraction, response closure, covariance decay,
coercivity, or mass-gap input is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance pinFreeResponseControlledWeightedRandomScanOrbitSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Pin-free weighted-column coefficient for the response-controlled physical
left kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
    (beta s responseCoefficient : ℝ) : ℝ :=
  18 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta *
    s ^ 2 +
    Real.exp (16 * beta) * responseCoefficient

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient_nonneg
    (beta s responseCoefficient : ℝ)
    (hbeta : 0 ≤ beta)
    (hResponseCoefficient : 0 ≤ responseCoefficient) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
        beta s responseCoefficient := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
  have hEta :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
      beta hbeta
  positivity

/-- The pin-free response-controlled physical left kernel inherits a
volume-independent weighted-column bound from the response profile itself,
with no distinguished-target pin contribution. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel_exponentialWeightedColumn_le
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (distinguishedTarget source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (responseCoefficient : ℝ)
    (hResponseWeighted :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s distinguishedTarget R responseCoefficient) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta R hRNonneg).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget target) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
          beta s responseCoefficient *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget source := by
  classical
  let Klocal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s distinguishedTarget
  have hsNonneg : 0 ≤ s := le_trans (by norm_num) hs
  have hWeightNonneg : ∀ target, 0 ≤ W target := by
    intro target
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s hsNonneg distinguishedTarget target
  have hPointwise :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
            H beta hbeta R hRNonneg).influence target source * W target ≤
          (Klocal.influence target source +
            Real.exp (16 * beta) * R target source) * W target := by
    intro target
    exact
      mul_le_mul_of_nonneg_right
        (by
          simpa [Klocal] using
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel_le_local_add_response
              H beta hbeta R hRNonneg target source)
        (hWeightNonneg target)
  have hLocal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_exponentialWeightedColumnSum_le
      H beta hbeta s hs distinguishedTarget source
  have hResponse := hResponseWeighted source
  have hExpNonneg : 0 ≤ Real.exp (16 * beta) := (Real.exp_pos _).le
  calc
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta R hRNonneg).influence target source * W target) ≤
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (Klocal.influence target source +
          Real.exp (16 * beta) * R target source) * W target := by
        exact Finset.sum_le_sum fun target _ => hPointwise target
    _ =
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        Klocal.influence target source * W target) +
      Real.exp (16 * beta) *
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          R target source * W target) := by
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        apply congrArg₂ (· + ·) rfl
        apply Finset.sum_congr rfl
        intro target _hTarget
        ring
    _ ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2) * W source +
      Real.exp (16 * beta) * (responseCoefficient * W source) := by
        exact
          add_le_add hLocal
            (mul_le_mul_of_nonneg_left hResponse hExpNonneg)
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
          beta s responseCoefficient * W source := by
        simp only [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient]
        ring

/-- One abstract pin-free response-controlled random-scan update of a left
variation profile. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanUpdatedVariation
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta R hRNonneg)
    (fun fiber : PeriodicHypercubicEvenSpatialSliceLink H => fiber)
    variation source

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanUpdatedVariation_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ source, 0 ≤ variation source)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanUpdatedVariation
        H beta hbeta R hRNonneg variation source := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanUpdatedVariation
  exact
    finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta R hRNonneg)
      (fun fiber : PeriodicHypercubicEvenSpatialSliceLink H => fiber)
      variation hVariationNonneg source

/-- Iterated abstract pin-free response-controlled random-scan variation
profile. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    ℕ → PeriodicHypercubicEvenSpatialSliceLink H → ℝ
  | 0 => variation
  | n + 1 =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanUpdatedVariation
        H beta hbeta R hRNonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
          H beta hbeta R hRNonneg variation n)

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate_zero
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
        H beta hbeta R hRNonneg variation 0 =
      variation := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate_succ
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
        H beta hbeta R hRNonneg variation (n + 1) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanUpdatedVariation
        H beta hbeta R hRNonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
          H beta hbeta R hRNonneg variation n) := by
  rfl

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ source, 0 ≤ variation source)
    (n : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
        H beta hbeta R hRNonneg variation n source := by
  induction n generalizing source with
  | zero =>
      simpa using hVariationNonneg source
  | succ n ih =>
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate_succ]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanUpdatedVariation_nonneg
          H beta hbeta R hRNonneg
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
            H beta hbeta R hRNonneg variation n)
          (fun e => ih e) source

/-- One pin-free response-controlled random-scan step preserves a
target-centered weighted bound with the improved reciprocal rate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanUpdatedVariation_le_weightedRate_mul
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (distinguishedTarget :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (responseCoefficient : ℝ)
    (hResponseWeighted :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s distinguishedTarget R responseCoefficient)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        variation e ≤
          bound *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s distinguishedTarget e)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanUpdatedVariation
        H beta hbeta R hRNonneg variation source ≤
      finiteInfluenceKernelReciprocalRandomScanRate
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
          beta s responseCoefficient) *
      bound *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s distinguishedTarget source := by
  classical
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta R hRNonneg
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s distinguishedTarget
  let coefficient :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
      beta s responseCoefficient
  let n : ℝ := Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  have hCardNat :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Fintype.card_pos_iff.mpr ⟨distinguishedTarget⟩
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast hCardNat
  have hColumn :
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        K.influence target source * W target) ≤
        coefficient * W source := by
    simpa [K, W, coefficient] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel_exponentialWeightedColumn_le
        H beta hbeta s hs distinguishedTarget source R hRNonneg
        responseCoefficient hResponseWeighted
  have hWeighted :
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        K.influence target source * variation target) ≤
        coefficient * bound * W source := by
    calc
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        K.influence target source * variation target) ≤
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          K.influence target source * (bound * W target) := by
            apply Finset.sum_le_sum
            intro target _hTarget
            exact
              mul_le_mul_of_nonneg_left
                (by simpa [W] using hVariationBound target)
                (K.influence_nonneg target source)
      _ =
        bound *
          (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            K.influence target source * W target) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro target _hTarget
            ring
      _ ≤ bound * (coefficient * W source) :=
        mul_le_mul_of_nonneg_left hColumn hBoundNonneg
      _ = coefficient * bound * W source := by ring
  have hDirect :
      n * variation source - variation source ≤
        (n - 1) * (bound * W source) := by
    have hScale :=
      mul_le_mul_of_nonneg_left
        (by simpa [W] using hVariationBound source)
        (by
          have hnOne : 1 ≤ n := by
            dsimp [n]
            exact_mod_cast hCardNat
          linarith : 0 ≤ n - 1)
    nlinarith
  have hTargetSum :
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        finiteInfluenceKernelUpdatedVariation K variation target source) ≤
        (n - 1 + coefficient) * bound * W source := by
    rw [finiteInfluenceKernelUpdatedVariation_sum_target_eq]
    change
      n * variation source +
          (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            K.influence target source * variation target) -
          variation source ≤
        _
    nlinarith
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanUpdatedVariation
    finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
    finiteInfluenceKernelReciprocalRandomScanRate
  change
    n⁻¹ *
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          finiteInfluenceKernelUpdatedVariation K variation target source) ≤
      n⁻¹ * (n - 1 + coefficient) * bound * W source
  simpa [mul_assoc] using
    (mul_le_mul_of_nonneg_left hTargetSum (le_of_lt (inv_pos.mpr hn)))

/-- The complete abstract pin-free response-controlled random-scan orbit obeys
the improved target-centered geometric weighted bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate_le_weightedRate_pow_mul
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (distinguishedTarget :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (responseCoefficient : ℝ)
    (hResponseCoefficient : 0 ≤ responseCoefficient)
    (hResponseWeighted :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s distinguishedTarget R responseCoefficient)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        variation e ≤
          bound *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s distinguishedTarget e)
    (n : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
        H beta hbeta R hRNonneg variation n source ≤
      (finiteInfluenceKernelReciprocalRandomScanRate
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
          beta s responseCoefficient)) ^ n *
      bound *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s distinguishedTarget source := by
  let rate :=
    finiteInfluenceKernelReciprocalRandomScanRate
      (PeriodicHypercubicEvenSpatialSliceLink H)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
        beta s responseCoefficient)
  have hCardNat :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Fintype.card_pos_iff.mpr ⟨distinguishedTarget⟩
  have hCoefficientNonneg :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
          beta s responseCoefficient :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient_nonneg
      beta s responseCoefficient hbeta hResponseCoefficient
  have hRateNonneg : 0 ≤ rate := by
    exact
      finiteInfluenceKernelReciprocalRandomScanRate_nonneg
        hCardNat
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
          beta s responseCoefficient)
        hCoefficientNonneg
  induction n generalizing source with
  | zero =>
      simpa [rate] using hVariationBound source
  | succ n ih =>
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate_succ]
      have hIterNonneg :
          ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
            0 ≤
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
                H beta hbeta R hRNonneg variation n e := by
        intro e
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate_nonneg
            H beta hbeta R hRNonneg variation hVariationNonneg n e
      have hStep :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanUpdatedVariation_le_weightedRate_mul
          H beta hbeta s hs distinguishedTarget R hRNonneg
          responseCoefficient hResponseWeighted
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
            H beta hbeta R hRNonneg variation n)
          hIterNonneg
          (rate ^ n * bound)
          (mul_nonneg (pow_nonneg hRateNonneg n) hBoundNonneg)
          (fun e => by simpa [rate, mul_assoc] using ih e)
          source
      calc
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanUpdatedVariation
            H beta hbeta R hRNonneg
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
              H beta hbeta R hRNonneg variation n)
            source ≤
          rate * (rate ^ n * bound) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s distinguishedTarget source := by
                simpa [rate, mul_assoc] using hStep
        _ =
          rate ^ (n + 1) * bound *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s distinguishedTarget source := by
                rw [pow_succ]
                ring

end

end MathlibAnalytic
end MGAP4D
