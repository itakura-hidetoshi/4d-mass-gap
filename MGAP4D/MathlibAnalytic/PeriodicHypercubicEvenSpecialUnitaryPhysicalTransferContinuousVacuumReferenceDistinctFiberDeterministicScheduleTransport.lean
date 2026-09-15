import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberDeterministicScheduleCarrierLemmas
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance referenceDistinctFiberDeterministicScheduleTransportSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceDistinctFiberDeterministicScheduleTransportSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceDistinctFiberDeterministicScheduleTransportSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceDistinctFiberDeterministicScheduleTransportSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceDistinctFiberDeterministicScheduleTransportSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceDistinctFiberDeterministicScheduleTransportSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Literal sequential continuous-C5 heat-bath expectation for an ordered
finite physical-fiber schedule.  The head fiber is updated first in state
space; equivalently, the tail observable action is formed first and the head
one-link conditional expectation acts outside it. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    List (PeriodicHypercubicEvenSpatialSliceLink H) →
      Matrix.specialUnitaryGroup (Fin N) ℂ →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) → ℝ
  | [], _k, A, F => F A
  | fiber :: fibers, k, A, F =>
      ∫ C,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
          H N hN beta hbeta B target source g₂ fibers k C F
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
          H N hN beta hbeta B target source fiber k g₂ A

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_nil
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
        H N hN beta hbeta B target source g₂ [] k A F = F A := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_cons
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
        H N hN beta hbeta B target source g₂ (fiber :: fibers) k A F =
      ∫ C,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
          H N hN beta hbeta B target source g₂ fibers k C F
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
          H N hN beta hbeta B target source fiber k g₂ A := by
  rfl

/-- The finite deterministic schedule expectation is strongly measurable as a
function of the initial configuration whenever the terminal observable is. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_stronglyMeasurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F) :
    StronglyMeasurable
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
          H N hN beta hbeta B target source g₂ fibers k A F) := by
  induction fibers with
  | nil =>
      simpa using hF
  | cons fiber fibers ih =>
      simp only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_cons]
      exact ih.integral_kernel

/-- Fixed-boundary-parameter variation propagation through an arbitrary finite
literal continuous-C5 heat-bath schedule.  Repeated fibers require no distinctness
assumption: varying the coordinate currently resampled is killed exactly by the
one-link update; varying a different coordinate is transported by the explicit
literal-C5 off-fiber coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_fiberVariation_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (hVariation :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update A e u) - F (Function.update A e v)| ≤ variation e) :
    ∀ (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H))
      (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
      |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
          H N hN beta hbeta B target source g₂ fibers k
          (Function.update A e u) F -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
          H N hN beta hbeta B target source g₂ fibers k
          (Function.update A e v) F| ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
          H beta hbeta variation fibers (Sum.inl e) := by
  intro fibers
  induction fibers with
  | nil =>
      intro e A u v
      simpa using hVariation e A u v
  | cons fiber fibers ih =>
      intro e A u v
      let G : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
        fun C =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
            H N hN beta hbeta B target source g₂ fibers k C F
      let tailVariation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
        fun background =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
            H beta hbeta variation fibers (Sum.inl background)
      have hG : StronglyMeasurable G := by
        dsimp [G]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_stronglyMeasurable
            H N hN beta hbeta B target source g₂ k fibers F hF
      have hTailNonneg : ∀ background, 0 ≤ tailVariation background := by
        intro background
        dsimp [tailVariation]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation_nonneg
            H beta hbeta variation hVariationNonneg fibers (Sum.inl background)
      have hTailVariation :
          ∀ (background : PeriodicHypercubicEvenSpatialSliceLink H)
            (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
            (a b : Matrix.specialUnitaryGroup (Fin N) ℂ),
            |G (Function.update C background a) -
              G (Function.update C background b)| ≤ tailVariation background := by
        intro background C a b
        simpa [G, tailVariation] using ih background C a b
      simp only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_cons]
      by_cases hEq : e = fiber
      · subst e
        rw [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_update_fiber
            H N hN beta hbeta B target source fiber k g₂ A u,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_update_fiber
            H N hN beta hbeta B target source fiber k g₂ A v]
        simp [finiteInfluenceKernelUpdatedVariation]
      · have hBound :=
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_distinctBackground_variation_le
            H N hN beta hbeta B target source fiber e hEq
            k g₂ A u v G hG tailVariation hTailNonneg hTailVariation
        rw [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation_cons_left_of_ne
            H beta hbeta variation fiber e fibers hEq]
        simpa [G, tailVariation] using hBound

/-- Boundary-parameter transport through an arbitrary finite ordered literal-C5
heat-bath schedule is dominated by the exact deterministic action of the
explicit augmented tagged carrier.  No pairwise-distinctness hypothesis is
needed; therefore this theorem strictly contains the requested distinct-fiber
finite schedule case. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_transport_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k₁ k₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (hVariation :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update C e u) - F (Function.update C e v)| ≤ variation e) :
    ∀ fibers : List (PeriodicHypercubicEvenSpatialSliceLink H),
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
        H N hN beta hbeta B target source g₂ fibers k₁ A F -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
        H N hN beta hbeta B target source g₂ fibers k₂ A F| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
        H beta hbeta variation fibers (Sum.inr source) := by
  intro fibers
  induction fibers generalizing A with
  | nil =>
      simp [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation]
  | cons fiber fibers ih =>
      let K₁ :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
          H N hN beta hbeta B target source fiber k₁ g₂
      let K₂ :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
          H N hN beta hbeta B target source fiber k₂ g₂
      let G₁ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
        fun C =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
            H N hN beta hbeta B target source g₂ fibers k₁ C F
      let G₂ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
        fun C =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
            H N hN beta hbeta B target source g₂ fibers k₂ C F
      let tailVariation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
        fun background =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
            H beta hbeta variation fibers (Sum.inl background)
      let tailBound : ℝ :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
          H beta hbeta variation fibers (Sum.inr source)
      have hG₁ : StronglyMeasurable G₁ := by
        dsimp [G₁]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_stronglyMeasurable
            H N hN beta hbeta B target source g₂ k₁ fibers F hF
      have hG₂ : StronglyMeasurable G₂ := by
        dsimp [G₂]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_stronglyMeasurable
            H N hN beta hbeta B target source g₂ k₂ fibers F hF
      have hTailNonneg : ∀ background, 0 ≤ tailVariation background := by
        intro background
        dsimp [tailVariation]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation_nonneg
            H beta hbeta variation hVariationNonneg fibers (Sum.inl background)
      have hTailVariation₁ :
          ∀ (background : PeriodicHypercubicEvenSpatialSliceLink H)
            (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
            (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
            |G₁ (Function.update C background u) -
              G₁ (Function.update C background v)| ≤ tailVariation background := by
        intro background C u v
        simpa [G₁, tailVariation] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_fiberVariation_le
            H N hN beta hbeta B target source g₂ k₁ F hF variation
            hVariationNonneg hVariation fibers background C u v
      have hTailVariation₂ :
          ∀ (background : PeriodicHypercubicEvenSpatialSliceLink H)
            (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
            (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
            |G₂ (Function.update C background u) -
              G₂ (Function.update C background v)| ≤ tailVariation background := by
        intro background C u v
        simpa [G₂, tailVariation] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_fiberVariation_le
            H N hN beta hbeta B target source g₂ k₂ F hF variation
            hVariationNonneg hVariation fibers background C u v
      have hHead :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_fiberVariation_influence_le_crossBoundaryMajorant_mul
          H N hN beta hbeta B target source fiber k₁ k₂ g₂ A G₁ hG₁
          (tailVariation fiber) (hTailNonneg fiber) (hTailVariation₁ fiber A)
      have hG₁Int : Integrable G₁ (K₂ A) := by
        dsimp [K₂]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_integrable_of_fiberVariation
            H N hN beta hbeta B target source fiber k₂ g₂ A G₁ hG₁
            (tailVariation fiber) (hTailNonneg fiber) (hTailVariation₁ fiber A)
      have hG₂Int : Integrable G₂ (K₂ A) := by
        dsimp [K₂]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_integrable_of_fiberVariation
            H N hN beta hbeta B target source fiber k₂ g₂ A G₂ hG₂
            (tailVariation fiber) (hTailNonneg fiber) (hTailVariation₂ fiber A)
      have hTailPoint : ∀ C, |G₁ C - G₂ C| ≤ tailBound := by
        intro C
        simpa [G₁, G₂, tailBound] using ih C
      have hDiffInt : Integrable (fun C => G₁ C - G₂ C) (K₂ A) :=
        hG₁Int.sub hG₂Int
      have hAverage :
          |(∫ C, G₁ C ∂K₂ A) - (∫ C, G₂ C ∂K₂ A)| ≤ tailBound := by
        calc
          |(∫ C, G₁ C ∂K₂ A) - (∫ C, G₂ C ∂K₂ A)| =
              |∫ C, (G₁ C - G₂ C) ∂K₂ A| := by
            rw [integral_sub hG₁Int hG₂Int]
          _ = ‖∫ C, (G₁ C - G₂ C) ∂K₂ A‖ := by
            rw [Real.norm_eq_abs]
          _ ≤ ∫ C, ‖G₁ C - G₂ C‖ ∂K₂ A :=
            norm_integral_le_integral_norm _
          _ ≤ ∫ _C, tailBound ∂K₂ A := by
            apply integral_mono_ae hDiffInt.norm (integrable_const tailBound)
            filter_upwards with C
            simpa [Real.norm_eq_abs] using hTailPoint C
          _ = tailBound := by
            simp
      simp only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_cons]
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation_cons_right]
      let x := ∫ C, G₁ C ∂K₁ A
      let y := ∫ C, G₁ C ∂K₂ A
      let z := ∫ C, G₂ C ∂K₂ A
      have hEq : x - z = (x - y) + (y - z) := by ring
      change |x - z| ≤ tailBound +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
            beta fiber source * tailVariation fiber
      rw [hEq]
      calc
        |(x - y) + (y - z)| ≤ |x - y| + |y - z| := by
          simpa [Real.norm_eq_abs] using norm_add_le (x - y) (y - z)
        _ ≤
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
                beta fiber source * tailVariation fiber + tailBound := by
          exact add_le_add hHead hAverage
        _ = tailBound +
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
                beta fiber source * tailVariation fiber := by
          ring

end

end MathlibAnalytic
end MGAP4D
