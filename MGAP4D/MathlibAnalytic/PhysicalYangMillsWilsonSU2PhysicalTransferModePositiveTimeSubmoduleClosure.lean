import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalTransferModePositiveHalfSynthesisClosure
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PositiveTimeSubmoduleRangeClosure
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

private theorem physicalTransferModePositiveTimeSubmoduleTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance physicalTransferModePositiveTimeSubmoduleSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

private abbrev physicalTransferModePositiveTimeSubmodulePreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta
    Q.toWeakStarBridge hInvariant n

/-- Canonical positive-time-submodule translation, obtained by transporting the
already-constructed observable translation across the carrier/submodule
repackaging equivalence.  This introduces no new Hilbert-space equivalence: the
carrier equivalence is the existing definitional wrapper equivalence. -/
noncomputable def positiveTimeSubmoduleTranslationLinearMap
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal) :
    D.positiveTimeSubalgebra.toSubmodule →ₗ[ℝ]
      D.positiveTimeSubalgebra.toSubmodule := by
  let P := physicalTransferModePositiveTimeSubmodulePreHilbert Q hInvariant n
  exact
    P.carrierPositiveTimeLinearEquiv.toLinearMap.comp
      ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation t).comp
      P.carrierPositiveTimeLinearEquiv.symm.toLinearMap

/-- Pulling a positive-time submodule vector back through the wrapper equivalence
and then applying the carrier-level `L²` map is exactly the direct
positive-time-submodule `L²` map. -/
theorem positiveHalfL2LinearMap_carrierEquiv_symm
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) (F : D.positiveTimeSubalgebra.toSubmodule) :
    Q.positiveHalfL2LinearMap hInvariant n
        ((physicalTransferModePositiveTimeSubmodulePreHilbert Q hInvariant n).carrierPositiveTimeLinearEquiv.symm F) =
      Q.positiveTimeSubmoduleL2LinearMap n F := by
  rw [Q.positiveHalfL2LinearMap_apply_eq_positiveTimeSubmoduleL2LinearMap]
  have h :=
    (physicalTransferModePositiveTimeSubmodulePreHilbert Q hInvariant n).carrierPositiveTimeLinearEquiv.apply_symm_apply F
  exact congrArg (fun x => Q.positiveTimeSubmoduleL2LinearMap n x) h

/-- The same compatibility holds after one of the canonical positive-time
translations. -/
theorem positiveHalfL2LinearMap_carrierTranslation_carrierEquiv_symm
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal) (F : D.positiveTimeSubalgebra.toSubmodule) :
    Q.positiveHalfL2LinearMap hInvariant n
        ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation t
          ((physicalTransferModePositiveTimeSubmodulePreHilbert Q hInvariant n).carrierPositiveTimeLinearEquiv.symm F)) =
      Q.positiveTimeSubmoduleL2LinearMap n
        (Q.positiveTimeSubmoduleTranslationLinearMap hInvariant C n t F) := by
  rw [Q.positiveHalfL2LinearMap_apply_eq_positiveTimeSubmoduleL2LinearMap]
  rfl

/-- The completed physical boundary image may therefore be written with no OS
carrier wrapper at all: it is the closure of actual synthesis applied to the
direct positive-time-submodule pullback range. -/
theorem range_physicalHilbertBoundaryMomentLinearIsometry_eq_closure_actualSynthesis_positiveTimeSubmodule
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    Set.range (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n) =
      closure (Set.range (fun F : D.positiveTimeSubalgebra.toSubmodule =>
        physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
          halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta n
          (Q.positiveTimeSubmoduleL2LinearMap n F))) := by
  rw [Q.range_physicalHilbertBoundaryMomentLinearIsometry_eq_closure_actualSynthesis_positiveHalf]
  congr 1
  ext x
  constructor
  · rintro ⟨F, rfl⟩
    refine ⟨(physicalTransferModePositiveTimeSubmodulePreHilbert Q hInvariant n).carrierToPositiveTimeLinearMap F, ?_⟩
    rw [Q.positiveHalfL2LinearMap_apply_eq_positiveTimeSubmoduleL2LinearMap]
  · rintro ⟨F, rfl⟩
    rcases
        (physicalTransferModePositiveTimeSubmodulePreHilbert Q hInvariant n).carrierToPositiveTimeLinearMap_surjective F with
      ⟨G, hG⟩
    refine ⟨G, ?_⟩
    rw [Q.positiveHalfL2LinearMap_apply_eq_positiveTimeSubmoduleL2LinearMap]
    exact congrArg
      (fun x =>
        physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
          halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta n
          (Q.positiveTimeSubmoduleL2LinearMap n x)) hG.symm

/-- Wrapper-free positive-time-submodule realization of the one-sided endpoint
pair.  The model-facing sequence now lives directly in the positive-time
submodule, and both time-zero and time-one convergence are stated before
boundary synthesis. -/
structure OneSidedPositiveTimeSubmoduleSynthesisClosureAt
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f omega fOne omegaOne : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
        (halfExtent n) 2)) where
  approximants : ℕ → D.positiveTimeSubalgebra.toSubmodule
  positiveHalfLimit : PhysicalYangMillsEvenPeriodicWilsonOSOpenHalfFeatureL2
    halfExtent 2 n
  translatedPositiveHalfLimit : PhysicalYangMillsEvenPeriodicWilsonOSOpenHalfFeatureL2
    halfExtent 2 n
  positiveHalfTendsto : Tendsto
    (fun k => Q.positiveTimeSubmoduleL2LinearMap n (approximants k))
    atTop (𝓝 positiveHalfLimit)
  translatedPositiveHalfTendsto : Tendsto
    (fun k => Q.positiveTimeSubmoduleL2LinearMap n
      (Q.positiveTimeSubmoduleTranslationLinearMap hInvariant C n 1 (approximants k)))
    atTop (𝓝 translatedPositiveHalfLimit)
  synthesisZero :
    physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta n positiveHalfLimit =
      periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
        (halfExtent n) 2 f omega
  synthesisOne :
    physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta n translatedPositiveHalfLimit =
      periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
        (halfExtent n) 2 fOne omegaOne

/-- The wrapper-free positive-time-submodule datum canonically generates the
carrier-level positive-half synthesis datum already used by the generic
finite-OS eigenlift. -/
def OneSidedPositiveTimeSubmoduleSynthesisClosureAt.toOneSidedPositiveHalfSynthesisClosureAt
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f omega fOne omegaOne : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
        (halfExtent n) 2))
    (W : OneSidedPositiveTimeSubmoduleSynthesisClosureAt
      Q hInvariant C n f omega fOne omegaOne) :
    OneSidedPositiveHalfSynthesisClosureAt
      Q hInvariant C n f omega fOne omegaOne := by
  refine
    { approximants := fun k =>
        (physicalTransferModePositiveTimeSubmodulePreHilbert Q hInvariant n).carrierPositiveTimeLinearEquiv.symm
          (W.approximants k)
      positiveHalfLimit := W.positiveHalfLimit
      translatedPositiveHalfLimit := W.translatedPositiveHalfLimit
      positiveHalfTendsto := ?_
      translatedPositiveHalfTendsto := ?_
      synthesisZero := W.synthesisZero
      synthesisOne := W.synthesisOne }
  · simpa only [Q.positiveHalfL2LinearMap_carrierEquiv_symm] using W.positiveHalfTendsto
  · simpa only [Q.positiveHalfL2LinearMap_carrierTranslation_carrierEquiv_symm] using
      W.translatedPositiveHalfTendsto

/-- Wrapper-free positive-time-submodule closure specialized to the normalized
physical SU(2) one-slice transfer mode. -/
abbrev PhysicalTransferModePositiveTimeSubmoduleSynthesisClosureAt
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2) :=
  OneSidedPositiveTimeSubmoduleSynthesisClosureAt Q hInvariant C n
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
      (halfExtent n) 2 f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
      (halfExtent n) 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive
        (beta n) (hbeta n))
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
      (halfExtent n) 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive
        (beta n) (hbeta n) f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
      (halfExtent n) 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive
        (beta n) (hbeta n))

/-- A normalized physical SU(2) one-slice transfer eigenmode lifts to a genuine
finite Wilson OS Hilbert eigenvector from a closure hypothesis stated entirely
on the positive-time submodule.  The opaque OS carrier is absent from the
model-facing assumption. -/
theorem exists_finiteOperator_one_eigen_of_normalizedPhysicalTransferModePositiveTimeSubmoduleSynthesisClosure
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2)
    (mu : ℝ)
    (hf : periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive
        (beta n) (hbeta n) f = mu • f)
    (W : PhysicalTransferModePositiveTimeSubmoduleSynthesisClosureAt
      Q hInvariant C n f) :
    ∃ psi :
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive
            beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert,
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi =
          periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
            (halfExtent n) 2
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
              (halfExtent n) 2 f)
            (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
              (halfExtent n) 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive
                (beta n) (hbeta n)) ∧
      C.finiteOperator n 1 psi = mu • psi := by
  exact
    Q.exists_finiteOperator_one_eigen_of_normalizedPhysicalTransferModePositiveHalfSynthesisClosure
      hInvariant C n f mu hf
      (OneSidedPositiveTimeSubmoduleSynthesisClosureAt.toOneSidedPositiveHalfSynthesisClosureAt
        Q hInvariant C n
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
          (halfExtent n) 2 f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
          (halfExtent n) 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive
            (beta n) (hbeta n))
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
          (halfExtent n) 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive
            (beta n) (hbeta n) f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
          (halfExtent n) 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive
            (beta n) (hbeta n)) W)

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end MathlibAnalytic
end MGAP4D
