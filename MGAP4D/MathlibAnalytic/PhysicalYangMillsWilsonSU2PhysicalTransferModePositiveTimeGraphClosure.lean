import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PhysicalTransferModePositiveTimeSubmoduleClosure
import Mathlib.Topology.Sequences
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

private theorem physicalTransferModePositiveTimeGraphTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance physicalTransferModePositiveTimeGraphSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance physicalTransferModePositiveTimeGraphTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance physicalTransferModePositiveTimeGraphCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance physicalTransferModePositiveTimeGraphSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance physicalTransferModePositiveTimeGraphMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance physicalTransferModePositiveTimeGraphBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance physicalTransferModePositiveTimeGraphOpenHalfHaarFinite (H : ℕ) :
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

private abbrev physicalTransferModePositiveTimeGraphOpenHalfL2
    (halfExtent : ℕ → ℕ) (n : ℕ) :=
  PhysicalYangMillsEvenPeriodicWilsonOSOpenHalfFeatureL2 halfExtent 2 n

/-- The actual positive-time readout together with its one-step translated
readout. Its range is the graph-level realizability object needed for a common
approximating sequence. -/
noncomputable def physicalTransferPositiveTimeGraphL2LinearMap
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeGraphTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 physicalTransferModePositiveTimeGraphTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ) :
    D.positiveTimeSubalgebra.toSubmodule →ₗ[ℝ]
      (physicalTransferModePositiveTimeGraphOpenHalfL2 halfExtent n ×
        physicalTransferModePositiveTimeGraphOpenHalfL2 halfExtent n) where
  toFun := fun F =>
    (Q.physicalTransferPositiveTimeSubmoduleL2LinearMap n F,
      Q.physicalTransferPositiveTimeSubmoduleL2LinearMap n
        (Q.positiveTimeSubmoduleTranslationLinearMap hInvariant C n 1 F))
  map_add' := by
    intro F G
    ext <;> simp
  map_smul' := by
    intro c F
    ext <;> simp

@[simp] theorem physicalTransferPositiveTimeGraphL2LinearMap_fst
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeGraphTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 physicalTransferModePositiveTimeGraphTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ) (F : D.positiveTimeSubalgebra.toSubmodule) :
    (Q.physicalTransferPositiveTimeGraphL2LinearMap hInvariant C n F).1 =
      Q.physicalTransferPositiveTimeSubmoduleL2LinearMap n F := rfl

@[simp] theorem physicalTransferPositiveTimeGraphL2LinearMap_snd
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeGraphTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 physicalTransferModePositiveTimeGraphTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ) (F : D.positiveTimeSubalgebra.toSubmodule) :
    (Q.physicalTransferPositiveTimeGraphL2LinearMap hInvariant C n F).2 =
      Q.physicalTransferPositiveTimeSubmoduleL2LinearMap n
        (Q.positiveTimeSubmoduleTranslationLinearMap hInvariant C n 1 F) := rfl

/-- Graph-closure formulation of one-sided endpoint realizability. Unlike the
sequence-based synthesis closure, this datum does not choose approximants: it
only asks that the desired time-zero/time-one pair lie in the closure of the
single actual graph range. -/
structure OneSidedPositiveTimeSubmoduleGraphClosureAt
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeGraphTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 physicalTransferModePositiveTimeGraphTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f omega fOne omegaOne : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
        (halfExtent n) 2)) where
  positiveHalfLimit : physicalTransferModePositiveTimeGraphOpenHalfL2 halfExtent n
  translatedPositiveHalfLimit : physicalTransferModePositiveTimeGraphOpenHalfL2 halfExtent n
  pair_mem_closure :
    (positiveHalfLimit, translatedPositiveHalfLimit) ∈ closure
      (LinearMap.range (Q.physicalTransferPositiveTimeGraphL2LinearMap
        hInvariant C n))
  synthesisZero :
    physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent 2 physicalTransferModePositiveTimeGraphTwoRankPositive beta hbeta n
        positiveHalfLimit =
      periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
        (halfExtent n) 2 f omega
  synthesisOne :
    physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent 2 physicalTransferModePositiveTimeGraphTwoRankPositive beta hbeta n
        translatedPositiveHalfLimit =
      periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
        (halfExtent n) 2 fOne omegaOne

/-- Mathlib's sequential characterization of closure extracts one common
positive-time sequence from graph closure. Projecting convergence in the
product gives the two limits required by the already-canonical synthesis
closure interface. -/
noncomputable def OneSidedPositiveTimeSubmoduleGraphClosureAt.toSynthesisClosureAt
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeGraphTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 physicalTransferModePositiveTimeGraphTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f omega fOne omegaOne : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
        (halfExtent n) 2))
    (W : OneSidedPositiveTimeSubmoduleGraphClosureAt
      Q hInvariant C n f omega fOne omegaOne) :
    OneSidedPositiveTimeSubmoduleSynthesisClosureAt
      Q hInvariant C n f omega fOne omegaOne := by
  let G := Q.physicalTransferPositiveTimeGraphL2LinearMap hInvariant C n
  let hSeq := mem_closure_iff_seq_limit.mp W.pair_mem_closure
  let u := Classical.choose hSeq
  have huSpec := Classical.choose_spec hSeq
  have huRange : ∀ k, u k ∈ LinearMap.range G := huSpec.1
  have huTendsto : Tendsto u atTop
      (𝓝 (W.positiveHalfLimit, W.translatedPositiveHalfLimit)) := huSpec.2
  let Fseq : ℕ → D.positiveTimeSubalgebra.toSubmodule := fun k =>
    Classical.choose (huRange k)
  have hFseq (k : ℕ) : G (Fseq k) = u k :=
    Classical.choose_spec (huRange k)
  have hSeqEq : (fun k => G (Fseq k)) = u := by
    funext k
    exact hFseq k
  have hPairTendsto : Tendsto (fun k => G (Fseq k)) atTop
      (𝓝 (W.positiveHalfLimit, W.translatedPositiveHalfLimit)) := by
    rw [hSeqEq]
    exact huTendsto
  have hZero : Tendsto (fun k => (G (Fseq k)).1) atTop
      (𝓝 W.positiveHalfLimit) := by
    simpa only [Function.comp_apply] using
      (continuous_fst.tendsto
        (W.positiveHalfLimit, W.translatedPositiveHalfLimit)).comp hPairTendsto
  have hOne : Tendsto (fun k => (G (Fseq k)).2) atTop
      (𝓝 W.translatedPositiveHalfLimit) := by
    simpa only [Function.comp_apply] using
      (continuous_snd.tendsto
        (W.positiveHalfLimit, W.translatedPositiveHalfLimit)).comp hPairTendsto
  refine
    { approximants := Fseq
      positiveHalfLimit := W.positiveHalfLimit
      translatedPositiveHalfLimit := W.translatedPositiveHalfLimit
      positiveHalfTendsto := ?_
      translatedPositiveHalfTendsto := ?_
      synthesisZero := W.synthesisZero
      synthesisOne := W.synthesisOne }
  · simpa [G] using hZero
  · simpa [G] using hOne

/-- Graph-closure realizability specialized to the normalized physical SU(2)
one-slice transfer mode. -/
abbrev PhysicalTransferModePositiveTimeSubmoduleGraphClosureAt
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeGraphTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 physicalTransferModePositiveTimeGraphTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2) :=
  OneSidedPositiveTimeSubmoduleGraphClosureAt Q hInvariant C n
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
      (halfExtent n) 2 f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
      (halfExtent n) 2 physicalTransferModePositiveTimeGraphTwoRankPositive
        (beta n) (hbeta n))
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
      (halfExtent n) 2 physicalTransferModePositiveTimeGraphTwoRankPositive
        (beta n) (hbeta n) f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
      (halfExtent n) 2 physicalTransferModePositiveTimeGraphTwoRankPositive
        (beta n) (hbeta n))

/-- A normalized physical SU(2) transfer eigenmode therefore lifts to a genuine
finite Wilson OS Hilbert eigenvector from a single graph-closure membership.
No approximating sequence is supplied by the model-facing hypothesis. -/
theorem exists_finiteOperator_one_eigen_of_normalizedPhysicalTransferModePositiveTimeGraphClosure
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 physicalTransferModePositiveTimeGraphTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 physicalTransferModePositiveTimeGraphTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2)
    (mu : ℝ)
    (hf : periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) 2 physicalTransferModePositiveTimeGraphTwoRankPositive
        (beta n) (hbeta n) f = mu • f)
    (W : PhysicalTransferModePositiveTimeSubmoduleGraphClosureAt
      Q hInvariant C n f) :
    ∃ psi :
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent 2 physicalTransferModePositiveTimeGraphTwoRankPositive
            beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert,
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi =
          periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
            (halfExtent n) 2
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
              (halfExtent n) 2 f)
            (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
              (halfExtent n) 2 physicalTransferModePositiveTimeGraphTwoRankPositive
                (beta n) (hbeta n)) ∧
      C.finiteOperator n 1 psi = mu • psi := by
  exact
    Q.exists_finiteOperator_one_eigen_of_normalizedPhysicalTransferModePositiveTimeSubmoduleSynthesisClosure
      hInvariant C n f mu hf
      (OneSidedPositiveTimeSubmoduleGraphClosureAt.toSynthesisClosureAt
        Q hInvariant C n
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
          (halfExtent n) 2 f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
          (halfExtent n) 2 physicalTransferModePositiveTimeGraphTwoRankPositive
            (beta n) (hbeta n))
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
          (halfExtent n) 2 physicalTransferModePositiveTimeGraphTwoRankPositive
            (beta n) (hbeta n) f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
          (halfExtent n) 2 physicalTransferModePositiveTimeGraphTwoRankPositive
            (beta n) (hbeta n)) W)

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end MathlibAnalytic
end MGAP4D
