import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PhysicalTransferModePositiveTimeBoundaryPairClosure
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

private theorem positiveTimeBoundaryPairGraphTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance positiveTimeBoundaryPairGraphSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance positiveTimeBoundaryPairGraphTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance positiveTimeBoundaryPairGraphCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance positiveTimeBoundaryPairGraphSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance positiveTimeBoundaryPairGraphMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance positiveTimeBoundaryPairGraphBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance positiveTimeBoundaryPairGraphOpenHalfHaarFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]

private abbrev positiveTimeBoundaryPairGraphPreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveTimeBoundaryPairGraphTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 positiveTimeBoundaryPairGraphTwoRankPositive beta hbeta
    Q.toWeakStarBridge hInvariant n

/-- On the dense represented OS carrier, the direct positive-time boundary-pair
map is exactly the completed finite Wilson transfer graph after applying the
canonical completed boundary isometry.

This is only a compatibility theorem: the positive-time submodule is the
existing carrier with its wrapper removed, and the second component is the
already-constructed completed finite transfer operator at one unit of time. -/
theorem physicalTransferPositiveTimeBoundaryPair_toPositiveTime_eq_completedGraph
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveTimeBoundaryPairGraphTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 positiveTimeBoundaryPairGraphTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (F : (positiveTimeBoundaryPairGraphPreHilbert Q hInvariant n).Carrier) :
    Q.physicalTransferPositiveTimeBoundaryPair hInvariant C n
        ((positiveTimeBoundaryPairGraphPreHilbert Q hInvariant n).physicalTransferCarrierPositiveTimeLinearEquiv F) =
      (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          ((positiveTimeBoundaryPairGraphPreHilbert Q hInvariant n).physicalState F),
       Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (C.finiteOperator n 1
            ((positiveTimeBoundaryPairGraphPreHilbert Q hInvariant n).physicalState F))) := by
  let P := positiveTimeBoundaryPairGraphPreHilbert Q hInvariant n
  let E := P.physicalTransferCarrierPositiveTimeLinearEquiv
  let Tn := C.toPositiveTimeObservableContractionSemigroup n
  have hEF : E F = P.toPositiveTime F := by
    rfl
  have hDirect :
      Q.positiveHalfL2LinearMap hInvariant n F =
        Q.physicalTransferPositiveTimeSubmoduleL2LinearMap n (E F) := by
    rw [hEF]
    exact
      Q.positiveHalfL2LinearMap_apply_eq_physicalTransferPositiveTimeSubmoduleL2LinearMap
        hInvariant n F
  have hTranslated :
      Q.positiveHalfL2LinearMap hInvariant n (Tn.carrierTranslation 1 F) =
        Q.physicalTransferPositiveTimeSubmoduleL2LinearMap n
          (Q.positiveTimeSubmoduleTranslationLinearMap hInvariant C n 1 (E F)) := by
    have h :=
      Q.positiveHalfL2LinearMap_carrierTranslation_carrierEquiv_symm
        hInvariant C n 1 (E F)
    simpa [E] using h
  have hFiniteOperator :
      C.finiteOperator n 1 (P.physicalState F) =
        P.physicalState (Tn.carrierTranslation 1 F) := by
    exact
      Tn.toCarrierSemigroup.physicalOperator_on_physicalState 1 F
  apply Prod.ext
  · change
      physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
          halfExtent 2 positiveTimeBoundaryPairGraphTwoRankPositive beta hbeta n
          (Q.physicalTransferPositiveTimeSubmoduleL2LinearMap n (E F)) =
        Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n (P.physicalState F)
    rw [← hDirect]
    exact
      (Q.physicalHilbertBoundaryMomentLinearIsometry_physicalState_eq_actualSynthesis
        hInvariant n F).symm
  · change
      physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
          halfExtent 2 positiveTimeBoundaryPairGraphTwoRankPositive beta hbeta n
          (Q.physicalTransferPositiveTimeSubmoduleL2LinearMap n
            (Q.positiveTimeSubmoduleTranslationLinearMap hInvariant C n 1 (E F))) =
        Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (C.finiteOperator n 1 (P.physicalState F))
    rw [← hTranslated]
    rw [hFiniteOperator]
    exact
      (Q.physicalHilbertBoundaryMomentLinearIsometry_physicalState_eq_actualSynthesis
        hInvariant n (Tn.carrierTranslation 1 F)).symm

/-- Every point of the completed finite Wilson transfer graph is already a
limit of direct positive-time-submodule boundary pairs.

In symbols, for every completed finite OS state `psi`,

`(J psi, J (C(1) psi)) ∈ closure (range boundaryPair)`.

The proof uses only density of represented positive-time states, continuity of
the completed transfer, and continuity of the completed boundary isometry. No
finite transfer eigen-equation, boundary surjectivity, or extra Hilbert-space
equivalence is assumed. -/
theorem completedPhysicalTransferGraph_mem_closure_positiveTimeBoundaryPair
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveTimeBoundaryPairGraphTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 positiveTimeBoundaryPairGraphTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (psi : (positiveTimeBoundaryPairGraphPreHilbert Q hInvariant n).PhysicalHilbert) :
    (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi,
     Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
       (C.finiteOperator n 1 psi)) ∈
      closure (Set.range (Q.physicalTransferPositiveTimeBoundaryPair hInvariant C n)) := by
  let P := positiveTimeBoundaryPairGraphPreHilbert Q hInvariant n
  let J := Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
  let E := P.physicalTransferCarrierPositiveTimeLinearEquiv
  have hDense : psi ∈ closure (Set.range P.physicalStateLinearMap) := by
    rw [P.closure_range_physicalStateLinearMap]
    exact Set.mem_univ psi
  rw [mem_closure_iff_seq_limit] at hDense
  rcases hDense with ⟨u, huRange, huTendsto⟩
  choose F hF using fun k => huRange k
  have hState :
      Tendsto (fun k => P.physicalState (F k)) atTop (𝓝 psi) := by
    apply huTendsto.congr'
    filter_upwards with k
    rw [← P.physicalStateLinearMap_apply]
    exact hF k
  have hZero :
      Tendsto (fun k => J (P.physicalState (F k))) atTop (𝓝 (J psi)) :=
    J.continuous.continuousAt.comp hState
  have hTransferredState :
      Tendsto (fun k => C.finiteOperator n 1 (P.physicalState (F k))) atTop
        (𝓝 (C.finiteOperator n 1 psi)) :=
    (C.finiteOperator n 1).continuous.continuousAt.comp hState
  have hOne :
      Tendsto
        (fun k => J (C.finiteOperator n 1 (P.physicalState (F k))))
        atTop
        (𝓝 (J (C.finiteOperator n 1 psi))) :=
    J.continuous.continuousAt.comp hTransferredState
  have hPair :
      Tendsto
        (fun k =>
          (J (P.physicalState (F k)),
           J (C.finiteOperator n 1 (P.physicalState (F k)))))
        atTop
        (𝓝 (J psi, J (C.finiteOperator n 1 psi))) := by
    rw [nhds_prod_eq]
    exact hZero.prodMk hOne
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun k => Q.physicalTransferPositiveTimeBoundaryPair hInvariant C n (E (F k)), ?_, ?_⟩
  · intro k
    exact ⟨E (F k), rfl⟩
  · have hEq :
        (fun k => Q.physicalTransferPositiveTimeBoundaryPair hInvariant C n (E (F k))) =
          (fun k =>
            (J (P.physicalState (F k)),
             J (C.finiteOperator n 1 (P.physicalState (F k))))) := by
      funext k
      exact
        Q.physicalTransferPositiveTimeBoundaryPair_toPositiveTime_eq_completedGraph
          hInvariant C n (F k)
    rw [hEq]
    exact hPair

/-- A model-facing endpoint pair satisfies the positive-time boundary-pair
closure condition as soon as it is identified with one actual completed finite
Wilson transfer-graph point.

Thus the former closure seam can be discharged by two concrete boundary
identities: one at time zero and one after the genuine completed unit transfer. -/
theorem oneSidedPositiveTimeSubmoduleBoundaryPairClosureAt_of_completedTransferGraph
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveTimeBoundaryPairGraphTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 positiveTimeBoundaryPairGraphTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f omega fOne omegaOne : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
        (halfExtent n) 2))
    (psi : (positiveTimeBoundaryPairGraphPreHilbert Q hInvariant n).PhysicalHilbert)
    (hZero :
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi =
        periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
          (halfExtent n) 2 f omega)
    (hOne :
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (C.finiteOperator n 1 psi) =
        periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
          (halfExtent n) 2 fOne omegaOne) :
    OneSidedPositiveTimeSubmoduleBoundaryPairClosureAt
      Q hInvariant C n f omega fOne omegaOne := by
  rw [OneSidedPositiveTimeSubmoduleBoundaryPairClosureAt]
  rw [← hZero, ← hOne]
  exact
    Q.completedPhysicalTransferGraph_mem_closure_positiveTimeBoundaryPair
      hInvariant C n psi

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end MathlibAnalytic
end MGAP4D
