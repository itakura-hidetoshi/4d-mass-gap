import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalTransferModePositiveHalfSynthesisClosure
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

private theorem physicalTransferModePositiveTimeSubmoduleTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance physicalTransferModePositiveTimeSubmoduleSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance physicalTransferModePositiveTimeSubmoduleTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance physicalTransferModePositiveTimeSubmoduleCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance physicalTransferModePositiveTimeSubmoduleSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance physicalTransferModePositiveTimeSubmoduleMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance physicalTransferModePositiveTimeSubmoduleBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance physicalTransferModePositiveTimeSubmoduleOpenHalfHaarFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

local instance physicalTransferModePositiveTimeSubmoduleSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- Forget the OS carrier wrapper when forming the physical-transfer closure
interface.  This is only the tautological positive-time repackaging map. -/
def physicalTransferCarrierToPositiveTimeLinearMap (P : D.OSPreHilbertData) :
    P.Carrier →ₗ[ℝ] D.positiveTimeSubalgebra.toSubmodule where
  toFun := P.toPositiveTime
  map_add' := P.toPositiveTime_add
  map_smul' := P.toPositiveTime_smul

@[simp] theorem physicalTransferCarrierToPositiveTimeLinearMap_apply
    (P : D.OSPreHilbertData) (F : P.Carrier) :
    P.physicalTransferCarrierToPositiveTimeLinearMap F = P.toPositiveTime F := rfl

private theorem physicalTransferCarrierToPositiveTimeLinearMap_injective
    (P : D.OSPreHilbertData) :
    Function.Injective P.physicalTransferCarrierToPositiveTimeLinearMap := by
  intro F G hFG
  apply Carrier.observable_injective P
  exact congrArg
    (fun x : D.positiveTimeSubalgebra.toSubmodule => x.1.1) hFG

/-- Every positive-time submodule vector has its tautological OS carrier
representative.  This is wrapper surjectivity, not Wilson-pullback surjectivity. -/
theorem physicalTransferCarrierToPositiveTimeLinearMap_surjective
    (P : D.OSPreHilbertData) :
    Function.Surjective P.physicalTransferCarrierToPositiveTimeLinearMap := by
  intro x
  let F : P.Carrier :=
    { observable := x.1.1
      gaugeInvariant := x.1.2
      positiveTime := x.2 }
  exact ⟨F, rfl⟩

/-- Canonical linear equivalence removing only the definitional OS carrier
wrapper.  No ambient Hilbert-space equivalence is introduced. -/
noncomputable def physicalTransferCarrierPositiveTimeLinearEquiv
    (P : D.OSPreHilbertData) :
    P.Carrier ≃ₗ[ℝ] D.positiveTimeSubalgebra.toSubmodule :=
  LinearEquiv.ofBijective P.physicalTransferCarrierToPositiveTimeLinearMap
    ⟨P.physicalTransferCarrierToPositiveTimeLinearMap_injective,
      P.physicalTransferCarrierToPositiveTimeLinearMap_surjective⟩

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

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

/-- Apply the coherent finite-Wilson positive-half pullback directly to the
positive-time submodule and then enter open-half Haar `L²`. -/
noncomputable def physicalTransferPositiveTimeSubmoduleL2LinearMap
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta)
    (n : ℕ) :
    D.positiveTimeSubalgebra.toSubmodule →ₗ[ℝ]
      PhysicalYangMillsEvenPeriodicWilsonOSOpenHalfFeatureL2 halfExtent 2 n :=
  (BoundedContinuousFunction.toLp
      (E := ℝ) 2
      (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) 2) ℝ).toLinearMap.comp
    (Q.positiveHalfPullback n)

@[simp] theorem physicalTransferPositiveTimeSubmoduleL2LinearMap_apply
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta)
    (n : ℕ) (F : D.positiveTimeSubalgebra.toSubmodule) :
    Q.physicalTransferPositiveTimeSubmoduleL2LinearMap n F =
      BoundedContinuousFunction.toLp
        (E := ℝ) 2
        (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) 2) ℝ
        (Q.positiveHalfPullback n F) := rfl

/-- Pointwise factorization of the existing carrier-level positive-half `L²`
map through the tautological positive-time wrapper removal. -/
theorem positiveHalfL2LinearMap_apply_eq_physicalTransferPositiveTimeSubmoduleL2LinearMap
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) (F : (physicalTransferModePositiveTimeSubmodulePreHilbert Q hInvariant n).Carrier) :
    Q.positiveHalfL2LinearMap hInvariant n F =
      Q.physicalTransferPositiveTimeSubmoduleL2LinearMap n
        ((physicalTransferModePositiveTimeSubmodulePreHilbert Q hInvariant n).toPositiveTime F) := by
  rw [Q.positiveHalfL2LinearMap_apply]
  change
    periodicHypercubicEvenWilsonOpenHalfObservableL2 (halfExtent n) 2
        (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
          S D halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive
          beta hbeta Q.toWeakStarBridge hInvariant n F) =
      BoundedContinuousFunction.toLp
        (E := ℝ) 2
        (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) 2) ℝ
        (Q.positiveHalfPullback n
          ((physicalTransferModePositiveTimeSubmodulePreHilbert Q hInvariant n).toPositiveTime F))
  rw [Q.finitePositiveHalfObservable_eq_positiveHalfPullback hInvariant n F]
  rfl

/-- Canonical positive-time-submodule translation, obtained by transporting the
already-constructed observable translation across the carrier/submodule
repackaging equivalence.  This introduces no new Hilbert-space equivalence. -/
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
    P.physicalTransferCarrierPositiveTimeLinearEquiv.toLinearMap.comp
      ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation t).comp
      P.physicalTransferCarrierPositiveTimeLinearEquiv.symm.toLinearMap

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
        ((physicalTransferModePositiveTimeSubmodulePreHilbert Q hInvariant n).physicalTransferCarrierPositiveTimeLinearEquiv.symm F) =
      Q.physicalTransferPositiveTimeSubmoduleL2LinearMap n F := by
  rw [Q.positiveHalfL2LinearMap_apply_eq_physicalTransferPositiveTimeSubmoduleL2LinearMap]
  have h :=
    (physicalTransferModePositiveTimeSubmodulePreHilbert Q hInvariant n).physicalTransferCarrierPositiveTimeLinearEquiv.apply_symm_apply F
  exact congrArg (fun x => Q.physicalTransferPositiveTimeSubmoduleL2LinearMap n x) h

/-- The same compatibility holds after one canonical positive-time translation. -/
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
          ((physicalTransferModePositiveTimeSubmodulePreHilbert Q hInvariant n).physicalTransferCarrierPositiveTimeLinearEquiv.symm F)) =
      Q.physicalTransferPositiveTimeSubmoduleL2LinearMap n
        (Q.positiveTimeSubmoduleTranslationLinearMap hInvariant C n t F) := by
  rw [Q.positiveHalfL2LinearMap_apply_eq_physicalTransferPositiveTimeSubmoduleL2LinearMap]
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
          (Q.physicalTransferPositiveTimeSubmoduleL2LinearMap n F))) := by
  rw [Q.range_physicalHilbertBoundaryMomentLinearIsometry_eq_closure_actualSynthesis_positiveHalf]
  congr 1
  ext x
  constructor
  · rintro ⟨F, rfl⟩
    refine ⟨(physicalTransferModePositiveTimeSubmodulePreHilbert Q hInvariant n).physicalTransferCarrierToPositiveTimeLinearMap F, ?_⟩
    rw [Q.positiveHalfL2LinearMap_apply_eq_physicalTransferPositiveTimeSubmoduleL2LinearMap]
  · rintro ⟨F, rfl⟩
    rcases
        (physicalTransferModePositiveTimeSubmodulePreHilbert Q hInvariant n).physicalTransferCarrierToPositiveTimeLinearMap_surjective F with
      ⟨G, hG⟩
    refine ⟨G, ?_⟩
    rw [Q.positiveHalfL2LinearMap_apply_eq_physicalTransferPositiveTimeSubmoduleL2LinearMap]
    exact congrArg
      (fun x =>
        physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
          halfExtent 2 physicalTransferModePositiveTimeSubmoduleTwoRankPositive beta hbeta n
          (Q.physicalTransferPositiveTimeSubmoduleL2LinearMap n x)) hG

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
    (fun k => Q.physicalTransferPositiveTimeSubmoduleL2LinearMap n (approximants k))
    atTop (𝓝 positiveHalfLimit)
  translatedPositiveHalfTendsto : Tendsto
    (fun k => Q.physicalTransferPositiveTimeSubmoduleL2LinearMap n
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
        (physicalTransferModePositiveTimeSubmodulePreHilbert Q hInvariant n).physicalTransferCarrierPositiveTimeLinearEquiv.symm
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