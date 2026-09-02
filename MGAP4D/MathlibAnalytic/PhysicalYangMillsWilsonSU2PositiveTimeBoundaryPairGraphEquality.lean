import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PositiveTimeBoundaryPairGraphClosure
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

private theorem positiveTimeBoundaryPairGraphEqualityTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance positiveTimeBoundaryPairGraphEqualitySideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance positiveTimeBoundaryPairGraphEqualityTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance positiveTimeBoundaryPairGraphEqualityCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance positiveTimeBoundaryPairGraphEqualitySecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance positiveTimeBoundaryPairGraphEqualityMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance positiveTimeBoundaryPairGraphEqualityBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance positiveTimeBoundaryPairGraphEqualityOpenHalfHaarFinite (H : ℕ) :
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

private abbrev positiveTimeBoundaryPairGraphEqualityPreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveTimeBoundaryPairGraphEqualityTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 positiveTimeBoundaryPairGraphEqualityTwoRankPositive beta hbeta
    Q.toWeakStarBridge hInvariant n

/-- The closure of the direct positive-time-submodule boundary-pair range is
exactly the graph of the genuine completed finite Wilson time-one transfer,
written in the canonical completed boundary isometry.

The forward inclusion is the substantive direction. A convergent sequence of
boundary pairs has a first component converging inside the closed range of the
boundary isometry. The isometry then recovers convergence of the represented OS
states themselves, and continuity of the completed finite transfer forces the
second component to be the corresponding transferred boundary state.

Thus product-space closure introduces no extra boundary pairs beyond the actual
completed transfer graph. -/
theorem closure_range_physicalTransferPositiveTimeBoundaryPair_eq_range_completedPhysicalTransferGraph
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveTimeBoundaryPairGraphEqualityTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 positiveTimeBoundaryPairGraphEqualityTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ) :
    closure (Set.range (Q.physicalTransferPositiveTimeBoundaryPair hInvariant C n)) =
      Set.range (fun psi :
        (positiveTimeBoundaryPairGraphEqualityPreHilbert Q hInvariant n).PhysicalHilbert =>
          (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi,
           Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
             (C.finiteOperator n 1 psi))) := by
  let P := positiveTimeBoundaryPairGraphEqualityPreHilbert Q hInvariant n
  let J := Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
  let E := P.physicalTransferCarrierPositiveTimeLinearEquiv
  apply Set.Subset.antisymm
  · intro z hz
    rw [mem_closure_iff_seq_limit] at hz
    rcases hz with ⟨u, huRange, huTendsto⟩
    choose G hG using fun k => huRange k
    let v : ℕ → P.PhysicalHilbert := fun k => P.physicalState (E.symm (G k))
    have hPairEq : ∀ k,
        u k = (J (v k), J (C.finiteOperator n 1 (v k))) := by
      intro k
      have h :=
        Q.physicalTransferPositiveTimeBoundaryPair_toPositiveTime_eq_completedGraph
          hInvariant C n (E.symm (G k))
      have h' :
          Q.physicalTransferPositiveTimeBoundaryPair hInvariant C n (G k) =
            (J (v k), J (C.finiteOperator n 1 (v k))) := by
        simpa [P, J, E, v] using h
      exact (hG k).symm.trans h'
    have hGraphTendsto :
        Tendsto (fun k => (J (v k), J (C.finiteOperator n 1 (v k))))
          atTop (𝓝 z) := by
      apply huTendsto.congr'
      exact Filter.Eventually.of_forall hPairEq
    have hFirst : Tendsto (fun k => J (v k)) atTop (𝓝 z.1) := by
      simpa only [Function.comp_apply] using
        (continuous_fst.tendsto z).comp hGraphTendsto
    have hzFirstRange : z.1 ∈ Set.range J := by
      exact
        (Q.isClosed_range_physicalHilbertBoundaryMomentLinearIsometry hInvariant n).mem_of_tendsto
          hFirst (Filter.Eventually.of_forall fun k => ⟨v k, rfl⟩)
    rcases hzFirstRange with ⟨psi, hpsi⟩
    have hJState : Tendsto (fun k => J (v k)) atTop (𝓝 (J psi)) := by
      simpa [hpsi] using hFirst
    have hState : Tendsto v atTop (𝓝 psi) := by
      apply (J.isometry.tendsto_nhds_iff).2
      simpa only [Function.comp_apply] using hJState
    have hTransferred :
        Tendsto (fun k => C.finiteOperator n 1 (v k)) atTop
          (𝓝 (C.finiteOperator n 1 psi)) :=
      (C.finiteOperator n 1).continuous.continuousAt.tendsto.comp hState
    have hSecondGraph :
        Tendsto (fun k => J (C.finiteOperator n 1 (v k))) atTop
          (𝓝 (J (C.finiteOperator n 1 psi))) :=
      J.continuous.continuousAt.tendsto.comp hTransferred
    have hSecondLimit :
        Tendsto (fun k => J (C.finiteOperator n 1 (v k))) atTop (𝓝 z.2) := by
      simpa only [Function.comp_apply] using
        (continuous_snd.tendsto z).comp hGraphTendsto
    have hzSecond : J (C.finiteOperator n 1 psi) = z.2 :=
      tendsto_nhds_unique hSecondGraph hSecondLimit
    refine ⟨psi, ?_⟩
    apply Prod.ext
    · exact hpsi
    · exact hzSecond
  · rintro z ⟨psi, rfl⟩
    exact
      Q.completedPhysicalTransferGraph_mem_closure_positiveTimeBoundaryPair
        hInvariant C n psi

/-- The model-facing positive-time boundary-pair closure condition is therefore
not an opaque density assumption: it is equivalent to exact membership in the
completed finite Wilson transfer graph.

Equivalently, the two desired endpoint vectors must be the time-zero and
unit-time boundary realizations of one and the same completed finite OS state. -/
theorem oneSidedPositiveTimeSubmoduleBoundaryPairClosureAt_iff_exists_completedTransferGraph
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveTimeBoundaryPairGraphEqualityTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 positiveTimeBoundaryPairGraphEqualityTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f omega fOne omegaOne : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
        (halfExtent n) 2)) :
    OneSidedPositiveTimeSubmoduleBoundaryPairClosureAt
        Q hInvariant C n f omega fOne omegaOne ↔
      ∃ psi : (positiveTimeBoundaryPairGraphEqualityPreHilbert Q hInvariant n).PhysicalHilbert,
        Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi =
          periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
            (halfExtent n) 2 f omega ∧
        Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
            (C.finiteOperator n 1 psi) =
          periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
            (halfExtent n) 2 fOne omegaOne := by
  rw [OneSidedPositiveTimeSubmoduleBoundaryPairClosureAt,
    Q.closure_range_physicalTransferPositiveTimeBoundaryPair_eq_range_completedPhysicalTransferGraph
      hInvariant C n]
  constructor
  · rintro ⟨psi, hpsi⟩
    refine ⟨psi, ?_, ?_⟩
    · exact congrArg Prod.fst hpsi
    · exact congrArg Prod.snd hpsi
  · rintro ⟨psi, hZero, hOne⟩
    refine ⟨psi, ?_⟩
    apply Prod.ext
    · exact hZero
    · exact hOne

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end MathlibAnalytic
end MGAP4D
