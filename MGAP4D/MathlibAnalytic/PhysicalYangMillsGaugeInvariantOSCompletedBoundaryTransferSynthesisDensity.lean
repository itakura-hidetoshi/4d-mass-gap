import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCompletedBoundaryTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDenseStateMap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryTransferSpatialSlicePair
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance completedBoundarySynthesisDensitySideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance completedBoundarySynthesisDensitySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance completedBoundarySynthesisDensitySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance completedBoundarySynthesisDensitySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance completedBoundarySynthesisDensitySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance completedBoundarySynthesisDensitySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- Every completed finite Wilson OS boundary-transfer value is a norm limit of
actual Wilson adjoint-synthesis outputs of translated positive-half vectors.

This is a completion theorem, not a new model assumption.  The represented raw
OS states are dense in the completed physical Hilbert space.  On each such
state, `completedBoundaryTransfer_apply_canonicalBoundaryMoment_eq_actualSynthesis`
already identifies the completed transfer with the actual Wilson synthesis
`A_φ† U_{n,t}`.  Continuity then passes that exact identity to completion.

The theorem deliberately retains `Q.translatedPositiveHalfL2LinearMap ... C`.
It therefore does not identify the abstract common finite-time action in `C`
with a concrete integer lattice translation. -/
theorem exists_actualSynthesis_translatedPositiveHalf_tendsto_completedBoundaryTransfer
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal)
    (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert) :
    ∃ F : ℕ →
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier,
      Tendsto
          (fun k =>
            (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
              S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState
              (F k))
          atTop (𝓝 psi) ∧
        Tendsto
          (fun k =>
            physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
              halfExtent N hN beta hbeta n
              (Q.translatedPositiveHalfL2LinearMap hInvariant C n t (F k)))
          atTop
          (𝓝
            (Q.completedBoundaryTransfer hInvariant C n t
              (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi))) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  have hmem : psi ∈ closure (Set.range Pn.physicalStateLinearMap) := by
    rw [Pn.closure_range_physicalStateLinearMap]
    exact Set.mem_univ psi
  rw [mem_closure_iff_seq_limit] at hmem
  rcases hmem with ⟨u, huRange, huTendsto⟩
  choose F hF using huRange
  have hstate : Tendsto (fun k => Pn.physicalState (F k)) atTop (𝓝 psi) := by
    have hfun : (fun k => Pn.physicalState (F k)) = u := by
      funext k
      rw [← Pn.physicalStateLinearMap_apply]
      exact hF k
    rw [hfun]
    exact huTendsto
  refine ⟨F, hstate, ?_⟩
  let J := Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
  let K := Q.completedBoundaryTransfer hInvariant C n t
  have hJ : Tendsto
      (fun k => J (Pn.physicalState (F k))) atTop (𝓝 (J psi)) :=
    J.continuous.continuousAt.tendsto.comp hstate
  have hK : Tendsto
      (fun k => K (J (Pn.physicalState (F k)))) atTop
      (𝓝 (K (J psi))) :=
    K.continuous.continuousAt.tendsto.comp hJ
  have hfun :
      (fun k =>
        physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
          halfExtent N hN beta hbeta n
          (Q.translatedPositiveHalfL2LinearMap hInvariant C n t (F k))) =
        (fun k => K (J (Pn.physicalState (F k)))) := by
    funext k
    dsimp only [J, K]
    rw [Q.physicalHilbertBoundaryMomentLinearIsometry_physicalState]
    exact
      (Q.completedBoundaryTransfer_apply_canonicalBoundaryMoment_eq_actualSynthesis
        hInvariant C n t (F k)).symm
  rw [hfun]
  exact hK

/-- Scalar version of the preceding completion theorem in the exact endpoint-pair
coordinates used by the one-slab physical-transfer lane.

For every fixed ambient pair-Haar test vector `z`, the completed transfer matrix
coefficient is the limit of matrix coefficients of actual Wilson
adjoint-synthesis outputs.  No pure-tensor density theorem is needed. -/
theorem exists_actualSynthesis_translatedPositiveHalf_pair_inner_tendsto_completedBoundaryTransfer
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal)
    (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N) :
    ∃ F : ℕ →
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier,
      Tendsto
          (fun k =>
            (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
              S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState
              (F k))
          atTop (𝓝 psi) ∧
        Tendsto
          (fun k =>
            inner ℝ
              (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
                (halfExtent n) N
                (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
                  halfExtent N hN beta hbeta n
                  (Q.translatedPositiveHalfL2LinearMap hInvariant C n t (F k)))) z)
          atTop
          (𝓝
            (inner ℝ
              (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
                (halfExtent n) N
                (Q.completedBoundaryTransfer hInvariant C n t
                  (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi))) z)) := by
  rcases Q.exists_actualSynthesis_translatedPositiveHalf_tendsto_completedBoundaryTransfer
      hInvariant C n t psi with ⟨F, hstate, hvec⟩
  refine ⟨F, hstate, ?_⟩
  have hpair : Tendsto
      (fun k =>
        periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
          (halfExtent n) N
          (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
            halfExtent N hN beta hbeta n
            (Q.translatedPositiveHalfL2LinearMap hInvariant C n t (F k))))
      atTop
      (𝓝
        (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
          (halfExtent n) N
          (Q.completedBoundaryTransfer hInvariant C n t
            (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi)))) :=
    (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
      (halfExtent n) N).continuous.continuousAt.tendsto.comp hvec
  exact hpair.inner tendsto_const_nhds

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end MathlibAnalytic
end MGAP4D

end
