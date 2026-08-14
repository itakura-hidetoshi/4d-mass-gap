import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2RawActualAnalysisRangeClosureDerivedRayleighMass
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProduct InnerProductSpace

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- The opaque OS carrier is only a repackaging of the positive-time submodule:
forgetting the carrier wrapper is a real-linear map. -/
def carrierToPositiveTimeLinearMap (P : D.OSPreHilbertData) :
    P.Carrier →ₗ[ℝ] D.positiveTimeSubalgebra.toSubmodule where
  toFun := P.toPositiveTime
  map_add' := P.toPositiveTime_add
  map_smul' := P.toPositiveTime_smul

@[simp] theorem carrierToPositiveTimeLinearMap_apply
    (P : D.OSPreHilbertData) (F : P.Carrier) :
    P.carrierToPositiveTimeLinearMap F = P.toPositiveTime F := rfl

/-- No information is lost by forgetting the carrier wrapper. -/
theorem carrierToPositiveTimeLinearMap_injective (P : D.OSPreHilbertData) :
    Function.Injective P.carrierToPositiveTimeLinearMap := by
  intro F G hFG
  apply Carrier.observable_injective P
  exact congrArg
    (fun x : D.positiveTimeSubalgebra.toSubmodule => x.1.1) hFG

/-- Every positive-time submodule element has the tautological OS carrier
representative carrying the same bounded-continuous observable and proofs. -/
theorem carrierToPositiveTimeLinearMap_surjective (P : D.OSPreHilbertData) :
    Function.Surjective P.carrierToPositiveTimeLinearMap := by
  intro x
  let F : P.Carrier :=
    { observable := x.1.1
      gaugeInvariant := x.1.2
      positiveTime := x.2 }
  exact ⟨F, rfl⟩

/-- The OS carrier and the positive-time submodule are canonically linearly
equivalent.  This is definitional repackaging, not a new density or
surjectivity hypothesis on the finite Wilson pullback. -/
noncomputable def carrierPositiveTimeLinearEquiv (P : D.OSPreHilbertData) :
    P.Carrier ≃ₗ[ℝ] D.positiveTimeSubalgebra.toSubmodule :=
  LinearEquiv.ofBijective P.carrierToPositiveTimeLinearMap
    ⟨P.carrierToPositiveTimeLinearMap_injective,
      P.carrierToPositiveTimeLinearMap_surjective⟩

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

private theorem positiveTimeSubmoduleRangeClosureTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance positiveTimeSubmoduleRangeClosureTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance positiveTimeSubmoduleRangeClosureCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance positiveTimeSubmoduleRangeClosureSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance positiveTimeSubmoduleRangeClosureMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance positiveTimeSubmoduleRangeClosureBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance positiveTimeSubmoduleRangeClosureOpenHalfHaarFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

local instance positiveTimeSubmoduleRangeClosureSU2Nontrivial :
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

private abbrev positiveTimeSubmoduleRangeClosurePreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveTimeSubmoduleRangeClosureTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 positiveTimeSubmoduleRangeClosureTwoRankPositive beta hbeta
    Q.toWeakStarBridge hInvariant n

/-- Apply the coherent finite-Wilson positive-half pullback directly on the
positive-time submodule, then use Mathlib's canonical bounded-continuous to
open-half Haar `L²` map. -/
noncomputable def positiveTimeSubmoduleL2LinearMap
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveTimeSubmoduleRangeClosureTwoRankPositive beta hbeta)
    (n : ℕ) :
    D.positiveTimeSubalgebra.toSubmodule →ₗ[ℝ]
      PhysicalYangMillsEvenPeriodicWilsonOSOpenHalfFeatureL2 halfExtent 2 n :=
  (BoundedContinuousFunction.toLp
      (E := ℝ) 2
      (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) 2) ℝ).toLinearMap.comp
    (Q.positiveHalfPullback n)

@[simp] theorem positiveTimeSubmoduleL2LinearMap_apply
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveTimeSubmoduleRangeClosureTwoRankPositive beta hbeta)
    (n : ℕ) (F : D.positiveTimeSubalgebra.toSubmodule) :
    Q.positiveTimeSubmoduleL2LinearMap n F =
      BoundedContinuousFunction.toLp
        (E := ℝ) 2
        (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) 2) ℝ
        (Q.positiveHalfPullback n F) := rfl

/-- Pointwise form of the carrier-to-positive-time factorization. -/
theorem positiveHalfL2LinearMap_apply_eq_positiveTimeSubmoduleL2LinearMap
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveTimeSubmoduleRangeClosureTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) (F : (positiveTimeSubmoduleRangeClosurePreHilbert Q hInvariant n).Carrier) :
    Q.positiveHalfL2LinearMap hInvariant n F =
      Q.positiveTimeSubmoduleL2LinearMap n
        ((positiveTimeSubmoduleRangeClosurePreHilbert Q hInvariant n).toPositiveTime F) := by
  rw [Q.positiveHalfL2LinearMap_apply]
  change
    periodicHypercubicEvenWilsonOpenHalfObservableL2 (halfExtent n) 2
        (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
          S D halfExtent 2 positiveTimeSubmoduleRangeClosureTwoRankPositive
          beta hbeta Q.toWeakStarBridge hInvariant n F) =
      BoundedContinuousFunction.toLp
        (E := ℝ) 2
        (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) 2) ℝ
        (Q.positiveHalfPullback n
          ((positiveTimeSubmoduleRangeClosurePreHilbert Q hInvariant n).toPositiveTime F))
  rw [Q.finitePositiveHalfObservable_eq_positiveHalfPullback hInvariant n F]
  rfl

/-- The carrier-level open-half `L²` map is exactly the direct positive-time
submodule map after the canonical carrier-to-positive-time equivalence. -/
theorem positiveHalfL2LinearMap_eq_positiveTimeSubmodule_comp
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveTimeSubmoduleRangeClosureTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    Q.positiveHalfL2LinearMap hInvariant n =
      (Q.positiveTimeSubmoduleL2LinearMap n).comp
        (positiveTimeSubmoduleRangeClosurePreHilbert Q hInvariant n).carrierToPositiveTimeLinearMap := by
  apply LinearMap.ext
  intro F
  exact Q.positiveHalfL2LinearMap_apply_eq_positiveTimeSubmoduleL2LinearMap
    hInvariant n F

/-- Consequently the carrier-level and direct positive-time-submodule pullbacks
have exactly the same `L²` range.  The surjectivity used here is only the
canonical wrapper equivalence above, not surjectivity of the Wilson pullback. -/
theorem range_positiveHalfL2LinearMap_eq_range_positiveTimeSubmoduleL2LinearMap
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveTimeSubmoduleRangeClosureTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    LinearMap.range (Q.positiveHalfL2LinearMap hInvariant n) =
      LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n) := by
  ext y
  constructor
  · rintro ⟨F, rfl⟩
    refine ⟨(positiveTimeSubmoduleRangeClosurePreHilbert Q hInvariant n).toPositiveTime F, ?_⟩
    exact (Q.positiveHalfL2LinearMap_apply_eq_positiveTimeSubmoduleL2LinearMap
      hInvariant n F).symm
  · rintro ⟨G, rfl⟩
    rcases (positiveTimeSubmoduleRangeClosurePreHilbert Q hInvariant n).carrierToPositiveTimeLinearMap_surjective G with
      ⟨F, hF⟩
    refine ⟨F, ?_⟩
    calc
      Q.positiveHalfL2LinearMap hInvariant n F =
          Q.positiveTimeSubmoduleL2LinearMap n
            ((positiveTimeSubmoduleRangeClosurePreHilbert Q hInvariant n).toPositiveTime F) :=
        Q.positiveHalfL2LinearMap_apply_eq_positiveTimeSubmoduleL2LinearMap hInvariant n F
      _ = Q.positiveTimeSubmoduleL2LinearMap n G := by
        exact congrArg (fun x => Q.positiveTimeSubmoduleL2LinearMap n x) hF

/-- The raw actual-analysis realizability frontier can now be stated entirely
at the positive-time-submodule level, independently of the OS carrier wrapper. -/
theorem normalizedTracePolynomial_rawActualAnalysis_mem_carrierRangeClosure_of_mem_positiveTimeRangeClosure
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveTimeSubmoduleRangeClosureTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ) (c : Fin (k + 1) → ℝ)
    (hClosure : periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
      (halfExtent n) (beta n) (hbeta n) k c ∈ closure
        (LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n))) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈ closure
      (LinearMap.range (Q.positiveHalfL2LinearMap hInvariant n)) := by
  rw [Q.range_positiveHalfL2LinearMap_eq_range_positiveTimeSubmoduleL2LinearMap hInvariant n]
  exact hClosure

/-- Thus direct positive-time-submodule `L²` closure realizability is sufficient
for nonnegativity of the reconstructed physical Yang--Mills variational mass. -/
theorem normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_rawActualAnalysis_mem_positiveTimeRangeClosure
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 positiveTimeSubmoduleRangeClosureTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility Q hInvariant)
    (n k : ℕ) (c : Fin (k + 1) → ℝ) (hH : 1 < halfExtent n) (hbetaPos : 0 < beta n) (hc : c ≠ 0)
    (hzero : inner ℝ (periodicHypercubicEvenBoundaryMarginalVacuumL2 (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2 (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hClosure : periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
      (halfExtent n) (beta n) (hbeta n) k c ∈ closure (LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)))
    (T : (positiveTimeSubmoduleRangeClosurePreHilbert Q hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) : 0 ≤ T.physicalYangMillsMass := by
  have hCarrierClosure :=
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_carrierRangeClosure_of_mem_positiveTimeRangeClosure
      hInvariant n k c hClosure
  exact Q.normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_rawActualAnalysis_mem_rangeClosure
    hInvariant U n k c hH hbetaPos hc hzero hCarrierClosure T hSelf

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
