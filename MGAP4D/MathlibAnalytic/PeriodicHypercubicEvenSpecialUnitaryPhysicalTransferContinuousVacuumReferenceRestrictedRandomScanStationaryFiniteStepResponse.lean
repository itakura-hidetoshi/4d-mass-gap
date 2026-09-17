import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRestrictedRandomScanStationaryResponseResidual
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance referenceRestrictedRandomScanStationaryFiniteStepResponseSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceRestrictedRandomScanStationaryFiniteStepResponseSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceRestrictedRandomScanStationaryFiniteStepResponseSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceRestrictedRandomScanStationaryFiniteStepResponseSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceRestrictedRandomScanStationaryFiniteStepResponseSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceRestrictedRandomScanStationaryFiniteStepResponseSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The physical spatial-link carrier is nonempty.  This is used only to
cancel the normalization factor in the uniform restricted random scan. -/
theorem
    periodicHypercubicEvenSpatialSliceLink_card_pos_for_stationaryFiniteStepResponse
    (H : ℕ) :
    0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) := by
  exact Fintype.card_pos_iff.mpr ⟨
    (⟨(fun _ => 0), by
        simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
      ⟨1, by norm_num⟩)⟩

/-- One actual restricted random-scan step preserves integrability under its
matching normalized continuous-C5 reference law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : Integrable F
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂)) :
    Integrable
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
          H N hN beta hbeta B target source g₂ k A F)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂) := by
  classical
  have hEach :
      ∀ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        Integrable
          (fun A =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k A F)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
            H N hN beta hbeta B target source k g₂) := by
    intro fiber
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_integrable
        H N hN beta hbeta B target source g₂ k F hF [fiber]
  have hSum :
      Integrable
        (fun A =>
          ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k A F)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂) := by
    exact integrable_finset_sum _ (fun fiber _ => hEach fiber)
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation] using
    hSum.const_mul
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹

/-- One actual restricted random-scan step preserves the expectation of every
integrable observable under the matching normalized continuous-C5 reference
law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_integral_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : Integrable F
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂)) :
    (∫ A,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
        H N hN beta hbeta B target source g₂ k A F
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂) =
      ∫ A, F A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂ := by
  classical
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B target source k g₂
  have hEach :
      ∀ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        Integrable
          (fun A =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k A F) μ := by
    intro fiber
    dsimp [μ]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_integrable
        H N hN beta hbeta B target source g₂ k F hF [fiber]
  have hCardNe :
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≠ 0 := by
    exact_mod_cast
      (Nat.ne_of_gt
        (periodicHypercubicEvenSpatialSliceLink_card_pos_for_stationaryFiniteStepResponse H))
  have hCardUniv :
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).card =
        Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) := by
    exact Finset.card_univ
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
  rw [integral_const_mul]
  rw [integral_finset_sum _ (fun fiber _ => hEach fiber)]
  calc
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          ∫ A,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k A F
            ∂μ) =
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        (∑ _fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          ∫ A, F A ∂μ) := by
        congr 1
        apply Finset.sum_congr rfl
        intro fiber _
        dsimp [μ]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_integral_eq
            H N hN beta hbeta B target source g₂ k F hF [fiber]
    _ = (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          ∫ A, F A ∂μ) := by
        rw [Finset.sum_const, nsmul_eq_mul, hCardUniv]
    _ = ∫ A, F A ∂μ := by
        rw [← mul_assoc, inv_mul_cancel₀ hCardNe, one_mul]

/-- Every finite actual restricted random-scan iterate preserves integrability
under its matching normalized reference law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : Integrable F
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂)) :
    ∀ n : ℕ,
      Integrable
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k F n)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂) := by
  intro n
  induction n with
  | zero => simpa using hF
  | succ n ih =>
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_integrable
          H N hN beta hbeta B target source g₂ k
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g₂ k F n)
          ih

/-- Every finite actual restricted random-scan iterate preserves expectation
under its matching normalized reference law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_integral_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : Integrable F
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂)) :
    ∀ n : ℕ,
      (∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k F n A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂) =
        ∫ A, F A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
            H N hN beta hbeta B target source k g₂ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hPrev :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_integrable
          H N hN beta hbeta B target source g₂ k F hF n
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ]
      calc
        (∫ A,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
            H N hN beta hbeta B target source g₂ k A
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
              H N hN beta hbeta B target source g₂ k F n)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
            H N hN beta hbeta B target source k g₂) =
          ∫ A,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
              H N hN beta hbeta B target source g₂ k F n A
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
              H N hN beta hbeta B target source k g₂ := by
                exact
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_integral_eq
                    H N hN beta hbeta B target source g₂ k
                    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                      H N hN beta hbeta B target source g₂ k F n)
                    hPrev
        _ = ∫ A, F A
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
              H N hN beta hbeta B target source k g₂ := ih

/-- Finite-step stationary response decomposition for the actual restricted
continuous-C5 random scan.  The first term is the accumulated source forcing
already carried by the tagged physical transport iterate.  The second term is
the terminal response of the common `k`-boundary smoothed observable.

This is the concrete continuous-state `R ≤ D + Q R` finite-step interface. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_response_abs_le_taggedTransport_add_terminal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (hFh : Integrable F
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source h g₂))
    (hFk : Integrable F
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂))
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (hVariation :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update C e u) - F (Function.update C e v)| ≤ variation e)
    (n : ℕ) :
    |(∫ A, F A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source h g₂) -
      (∫ A, F A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂)| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
          H beta hbeta variation n (Sum.inr source) +
        |(∫ A,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
              H N hN beta hbeta B target source g₂ k F n A
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
              H N hN beta hbeta B target source h g₂) -
          (∫ A,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
              H N hN beta hbeta B target source g₂ k F n A
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
              H N hN beta hbeta B target source k g₂)| := by
  classical
  let μh :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B target source h g₂
  let μk :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B target source k g₂
  let Sh :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
      H N hN beta hbeta B target source g₂ h F n
  let Sk :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
      H N hN beta hbeta B target source g₂ k F n
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
      H beta hbeta variation n (Sum.inr source)
  letI : IsProbabilityMeasure μh := by
    dsimp [μh]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target source h g₂
  letI : IsProbabilityMeasure μk := by
    dsimp [μk]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target source k g₂
  have hStatH : (∫ A, Sh A ∂μh) = ∫ A, F A ∂μh := by
    dsimp [Sh, μh]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_integral_eq
        H N hN beta hbeta B target source g₂ h F hFh n
  have hStatK : (∫ A, Sk A ∂μk) = ∫ A, F A ∂μk := by
    dsimp [Sk, μk]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_integral_eq
        H N hN beta hbeta B target source g₂ k F hFk n
  have hShInt : Integrable Sh μh := by
    dsimp [Sh, μh]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_integrable
        H N hN beta hbeta B target source g₂ h F hFh n
  have hShMeas : StronglyMeasurable Sh := by
    dsimp [Sh]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
        H N hN beta hbeta B target source g₂ h F hF n
  have hSkMeas : StronglyMeasurable Sk := by
    dsimp [Sk]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
        H N hN beta hbeta B target source g₂ k F hF n
  have hTNonneg : 0 ≤ T := by
    dsimp [T]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_nonneg
        H beta hbeta variation hVariationNonneg n (Sum.inr source)
  have hTransport : ∀ A, |Sh A - Sk A| ≤ T := by
    intro A
    dsimp [Sh, Sk, T]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_transport_le
        H N hN beta hbeta B target source g₂ h k F hF variation
        hVariationNonneg hVariation n A
  have hDiffInt : Integrable (fun A => Sh A - Sk A) μh := by
    apply (integrable_const T).mono (hShMeas.sub hSkMeas).aestronglyMeasurable
    filter_upwards with A
    simpa [Real.norm_eq_abs, abs_of_nonneg hTNonneg] using hTransport A
  have hSkIntH : Integrable Sk μh := by
    have hAux : Integrable (fun A => Sh A - (Sh A - Sk A)) μh :=
      hShInt.sub hDiffInt
    exact hAux.congr (ae_of_all _ fun A => by ring)
  have hFirst : |(∫ A, Sh A ∂μh) - (∫ A, Sk A ∂μh)| ≤ T := by
    calc
      |(∫ A, Sh A ∂μh) - (∫ A, Sk A ∂μh)| =
          |∫ A, (Sh A - Sk A) ∂μh| := by
            rw [integral_sub hShInt hSkIntH]
      _ = ‖∫ A, (Sh A - Sk A) ∂μh‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ∫ A, ‖Sh A - Sk A‖ ∂μh :=
            norm_integral_le_integral_norm _
      _ ≤ ∫ _A, T ∂μh := by
            apply integral_mono_ae hDiffInt.norm (integrable_const T)
            filter_upwards with A
            simpa [Real.norm_eq_abs] using hTransport A
      _ = T := by simp
  change |(∫ A, F A ∂μh) - (∫ A, F A ∂μk)| ≤
    T + |(∫ A, Sk A ∂μh) - (∫ A, Sk A ∂μk)|
  rw [← hStatH, ← hStatK]
  have hSplit :
      (∫ A, Sh A ∂μh) - (∫ A, Sk A ∂μk) =
        ((∫ A, Sh A ∂μh) - (∫ A, Sk A ∂μh)) +
          ((∫ A, Sk A ∂μh) - (∫ A, Sk A ∂μk)) := by
    ring
  rw [hSplit]
  calc
    |((∫ A, Sh A ∂μh) - (∫ A, Sk A ∂μh)) +
        ((∫ A, Sk A ∂μh) - (∫ A, Sk A ∂μk))| ≤
      |(∫ A, Sh A ∂μh) - (∫ A, Sk A ∂μh)| +
        |(∫ A, Sk A ∂μh) - (∫ A, Sk A ∂μk)| := by
          simpa [Real.norm_eq_abs] using
            norm_add_le
              ((∫ A, Sh A ∂μh) - (∫ A, Sk A ∂μh))
              ((∫ A, Sk A ∂μh) - (∫ A, Sk A ∂μk))
    _ ≤ T + |(∫ A, Sk A ∂μh) - (∫ A, Sk A ∂μk)| :=
      add_le_add hFirst (le_refl _)

end

end MathlibAnalytic
end MGAP4D
