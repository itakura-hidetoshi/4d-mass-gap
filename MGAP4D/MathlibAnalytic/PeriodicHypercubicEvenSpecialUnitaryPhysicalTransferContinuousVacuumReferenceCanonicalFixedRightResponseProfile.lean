import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceResponseControlledStationaryResolventResponse
import Mathlib.Tactic

/-!
# Canonical fixed-right response profile

The response-controlled stationary resolvent theorem is intentionally stated
for an arbitrary nonnegative profile R that uniformly dominates every literal
fixed-right target-ratio response.  To close the route without circularly
assuming the desired response, this file constructs the canonical pointwise
least supremum profile directly from the actual response values.

At fixed H,N,beta,target,source let S(target,source) be the set of all literal
ResponseAbs values over the base configuration and four SU(N) test values.
The target-ratio observable is positive and bounded above by exp(16 beta), so
each probability expectation lies in [0, exp(16 beta)] and therefore each
absolute response difference is at most exp(16 beta).

We define
  R_can(target,source) = max 0 (sSup S(target,source)).
Then R_can is nonnegative, bounded by exp(16 beta), and uniformly dominates
every actual response.  No contraction, weighted closure, covariance decay,
or remote kappa assumption is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance canonicalFixedRightResponseProfileSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance canonicalFixedRightResponseProfileSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalFixedRightResponseProfileSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalFixedRightResponseProfileSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalFixedRightResponseProfileSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalFixedRightResponseProfileSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Every literal fixed-right response is at most exp(16 beta).  This is only a
coarse boundedness theorem used to make the canonical supremum profile
well-defined; it is not the spatial estimate sought downstream. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_le_exp_sixteen
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
        H N hN beta hbeta B target source g₁ g₂ h k ≤
      Real.exp (16 * beta) := by
  let F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun A =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₁ /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₂
  let μh :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source h) target g₂)
  let μk :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g₂)
  letI : IsProbabilityMeasure μh := by
    dsimp [μh]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source h) target g₂)
  letI : IsProbabilityMeasure μk := by
    dsimp [μk]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g₂)
  have hFh : Integrable F μh := by
    simpa [F] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_integrable
        H N hN beta hbeta B target g₁ g₂ μh
  have hFk : Integrable F μk := by
    simpa [F] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_integrable
        H N hN beta hbeta B target g₁ g₂ μk
  have hFNonneg : ∀ A, 0 ≤ F A := by
    intro A
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_pos
        H N beta A B target g₁ g₂).le
  have hFLe : ∀ A, F A ≤ Real.exp (16 * beta) := by
    intro A
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_le_exp_sixteen
        H N hN beta hbeta A B target g₁ g₂
  have hIntHNonneg : 0 ≤ ∫ A, F A ∂μh :=
    integral_nonneg (Filter.Eventually.of_forall hFNonneg)
  have hIntKNonneg : 0 ≤ ∫ A, F A ∂μk :=
    integral_nonneg (Filter.Eventually.of_forall hFNonneg)
  have hIntHLe : (∫ A, F A ∂μh) ≤ Real.exp (16 * beta) := by
    calc
      (∫ A, F A ∂μh) ≤ ∫ _A, Real.exp (16 * beta) ∂μh := by
        exact integral_mono_ae hFh (integrable_const _) (Filter.Eventually.of_forall hFLe)
      _ = Real.exp (16 * beta) := by simp
  have hIntKLe : (∫ A, F A ∂μk) ≤ Real.exp (16 * beta) := by
    calc
      (∫ A, F A ∂μk) ≤ ∫ _A, Real.exp (16 * beta) ∂μk := by
        exact integral_mono_ae hFk (integrable_const _) (Filter.Eventually.of_forall hFLe)
      _ = Real.exp (16 * beta) := by simp
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
  change |(∫ A, F A ∂μh) - (∫ A, F A ∂μk)| ≤ Real.exp (16 * beta)
  rw [abs_le]
  constructor <;> linarith

/-- Set of all literal fixed-right response values for one ordered pair. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : Set ℝ :=
  {x | ∃
      (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ),
      x =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
          H N hN beta hbeta B target source g₁ g₂ h k}

/-- The actual-response value set is bounded above by exp(16 beta). -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet_bddAbove
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    BddAbove
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet
        H N hN beta hbeta target source) := by
  refine ⟨Real.exp (16 * beta), ?_⟩
  intro x hx
  rcases hx with ⟨B, g₁, g₂, h, k, rfl⟩
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_le_exp_sixteen
      H N hN beta hbeta B target source g₁ g₂ h k

/-- The actual-response value set is nonempty. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet_nonempty
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet
      H N hN beta hbeta target source).Nonempty := by
  let B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    fun _ => 1
  refine ⟨
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
      H N hN beta hbeta B target source 1 1 1 1, ?_⟩
  exact ⟨B, 1, 1, 1, 1, rfl⟩

/-- Canonical minimal supremum profile generated by the actual fixed-right
responses themselves.  The max with zero makes nonnegativity definitional even
before any use of a witness. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpatialSliceLink H →
      PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
  fun target source =>
    max 0
      (sSup
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet
          H N hN beta hbeta target source))

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∀ target source,
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta target source := by
  intro target source
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
  exact le_max_left _ _

/-- Every actual fixed-right response is bounded by the canonical profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_le_canonicalProfile
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
        H N hN beta hbeta B target source g₁ g₂ h k ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta target source := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet
      H N hN beta hbeta target source
  have hMem :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
          H N hN beta hbeta B target source g₁ g₂ h k ∈ S := by
    exact ⟨B, g₁, g₂, h, k, rfl⟩
  have hSup :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
          H N hN beta hbeta B target source g₁ g₂ h k ≤ sSup S := by
    exact le_csSup
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet_bddAbove
        H N hN beta hbeta target source)
      hMem
  exact hSup.trans (le_max_right _ _)

/-- The canonical profile remains under the same coarse exp(16 beta) bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_le_exp_sixteen
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta target source ≤
      Real.exp (16 * beta) := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet
      H N hN beta hbeta target source
  have hSup :
      sSup S ≤ Real.exp (16 * beta) := by
    apply csSup_le
    · exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet_nonempty
          H N hN beta hbeta target source
    · intro x hx
      rcases hx with ⟨B, g₁, g₂, h, k, rfl⟩
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_le_exp_sixteen
          H N hN beta hbeta B target source g₁ g₂ h k
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
  exact max_le (Real.exp_pos _).le hSup

/-- The canonical supremum profile is a valid configuration-independent
uniform response profile, without any assumed response coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_uniformBound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta) := by
  intro B target source g₁ g₂ h k
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_le_canonicalProfile
      H N hN beta hbeta B target source g₁ g₂ h k

end

end MathlibAnalytic
end MGAP4D
