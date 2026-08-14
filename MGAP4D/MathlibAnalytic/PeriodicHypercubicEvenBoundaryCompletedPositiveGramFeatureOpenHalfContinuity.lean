import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedPositiveContinuity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryDensityGramKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTemporalCrossingHalfSectors
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance boundaryCompletedPositiveOpenHalfContinuityNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryCompletedPositiveOpenHalfContinuityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryCompletedPositiveOpenHalfContinuityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryCompletedPositiveOpenHalfContinuitySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

/-- Any finite proposition-selected sum of periodic Wilson plaquette energies is
continuous on the full finite configuration space.  This packages the common
finite-sum argument used by the positive bulk and positive-boundary temporal
sectors. -/
private theorem periodicHypercubicEvenWilsonIndicatorAction_continuous
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (selected : PeriodicHypercubicEvenPlaquette H → Prop) :
    Continuous
      (fun A : PeriodicHypercubicEvenEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ =>
        ∑ p ∈ (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)),
          propositionIndicator (selected p)
            (specialUnitaryWilsonPlaquetteEnergy N
              (periodicHypercubicPlaquetteHolonomy A p))) := by
  classical
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN 0 (by positivity)
  apply continuous_finset_sum
  intro p _hp
  by_cases hs : selected p
  · simp only [propositionIndicator, if_pos hs]
    have hHol : Continuous
        (fun A : PeriodicHypercubicEvenEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          periodicHypercubicPlaquetteHolonomy A p) := by
      simpa [C] using continuous_compact_oriented_plaquetteHolonomy C p
    exact (continuous_specialUnitaryWilsonPlaquetteEnergy N).comp hHol
  · simp [propositionIndicator, hs]
    exact continuous_const

/-- The strict positive-open-half Wilson action is continuous. -/
theorem periodicHypercubicEvenPositiveWilsonAction_continuous
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    Continuous (periodicHypercubicEvenPositiveWilsonAction H N) := by
  simpa [periodicHypercubicEvenPositiveWilsonAction] using
    (periodicHypercubicEvenWilsonIndicatorAction_continuous
      H N hN periodicHypercubicEvenStrictPositivePlaquette)

/-- The positive-boundary-adjacent temporal Wilson action is continuous. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction_continuous
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    Continuous (periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N) := by
  simpa [periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction] using
    (periodicHypercubicEvenWilsonIndicatorAction_continuous
      H N hN periodicHypercubicEvenPositiveBoundaryTemporalPlaquette)

/-- The positive bulk Wilson Boltzmann amplitude is continuous. -/
theorem periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude_continuous
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) :
    Continuous (periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude H N beta) := by
  unfold periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude
  exact Real.continuous_exp.comp
    (continuous_const.mul
      (periodicHypercubicEvenPositiveWilsonAction_continuous H N hN))

/-- The positive-boundary temporal Wilson Boltzmann weight is continuous. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_continuous
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) :
    Continuous
      (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
        H N beta) := by
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
  exact Real.continuous_exp.comp
    (continuous_const.mul
      (periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction_continuous
        H N hN))

/-- The completed positive Wilson amplitude on the full finite configuration
space is continuous.  Both the bulk and boundary-adjacent temporal interactions
are retained. -/
theorem periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude_continuous
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) :
    Continuous
      (periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta) := by
  unfold periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude
  exact
    (periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude_continuous
      H N hN beta).mul
    (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_continuous
      H N hN beta)

/-- For fixed shared boundary data, the completed positive Wilson amplitude is
continuous in the actual positive open-half configuration. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude_continuous_openHalf
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    Continuous
      (periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
        H N beta b) := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  have hAssemble : Continuous
      (fun x : P.OpenHalfConfiguration (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        P.boundaryFiberedAssemble b x (fun _ => 1)) :=
    P.boundaryFiberedAssemble_continuous_positive b (fun _ => 1)
  unfold periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
  exact
    (periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude_continuous
      H N hN beta).comp hAssemble

/-- For fixed shared boundary data, the actual completed-positive scalar Gram
feature is continuous on the positive open-half configuration space. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_continuous_openHalf
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    Continuous
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b) := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
  exact continuous_const.mul
    (periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude_continuous_openHalf
      H N hN beta b)

end

end MathlibAnalytic
end MGAP4D
