import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryRawActualAnalysisPlaquetteAlgebraClosure
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2RawActualAnalysisContinuousPullbackClosure
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2FinitePositiveHalfObservableRangeBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology

noncomputable section

private theorem actualPlaquettePositiveTimeBridgeTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance actualPlaquettePositiveTimeBridgeNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance actualPlaquettePositiveTimeBridgeTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance actualPlaquettePositiveTimeBridgeCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance actualPlaquettePositiveTimeBridgeSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance actualPlaquettePositiveTimeBridgeMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance actualPlaquettePositiveTimeBridgeBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance actualPlaquettePositiveTimeBridgeSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The bounded-continuous carrier obtained from the concrete actual plaquette
algebra by Mathlib's canonical linear isometry from continuous maps on a
compact space.

This carrier is target-independent and carries no density assumption: its
members are exactly bounded representatives of actual finite plaquette-algebra
observables. -/
noncomputable def periodicHypercubicEvenBoundaryActualPlaquetteAlgebraBoundedCarrier
    (H : ℕ) :
    Set (BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2) ℝ) :=
  Set.range fun f :
      periodicHypercubicEvenBoundaryActualPlaquetteAlgebra
        H 2 actualPlaquettePositiveTimeBridgeTwoRankPositive =>
    ContinuousMap.linearIsometryBoundedOfCompact
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2) ℝ ℝ f.1

/-- The explicit raw actual-analysis mode lies in the sup-norm closure of the
bounded carrier of the actual plaquette algebra.

The hard input is the preceding concrete `C⁰` theorem, which was proved from
finite plaquette generators, polynomial approximation of the Gibbs
exponentials, and the boundary Bochner integral.  Here we only transport that
closure through Mathlib's canonical continuous linear isometry
`ContinuousMap.linearIsometryBoundedOfCompact`.

No abstract `Dense` hypothesis and no positive-time realizability hypothesis
is used in this theorem. -/
theorem
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction_mem_actualPlaquetteAlgebraBoundedCarrier_closure
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
        H beta hbeta k c ∈
      closure (periodicHypercubicEvenBoundaryActualPlaquetteAlgebraBoundedCarrier H) := by
  let X := PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2
  let A := periodicHypercubicEvenBoundaryActualPlaquetteAlgebra
    H 2 actualPlaquettePositiveTimeBridgeTwoRankPositive
  let L := ContinuousMap.linearIsometryBoundedOfCompact X ℝ ℝ
  let g :=
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMap
      H beta hbeta k c
  have hgTopologicalClosure : g ∈ A.topologicalClosure := by
    simpa [A, g] using
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMap_mem_actualPlaquetteAlgebra_topologicalClosure
        H beta hbeta k c)
  have hgClosure : g ∈ closure (A : Set C(X, ℝ)) := by
    simpa only [Subalgebra.topologicalClosure_coe] using hgTopologicalClosure
  rcases mem_closure_iff_seq_limit.mp hgClosure with ⟨u, huA, huTendsto⟩
  have hLAt : Tendsto L (𝓝 g) (𝓝 (L g)) :=
    L.continuous.continuousAt
  have huMappedTendsto : Tendsto (fun m => L (u m)) atTop (𝓝 (L g)) :=
    hLAt.comp huTendsto
  have huCarrier : ∀ m,
      L (u m) ∈ periodicHypercubicEvenBoundaryActualPlaquetteAlgebraBoundedCarrier H := by
    intro m
    refine ⟨⟨u m, huA m⟩, ?_⟩
    rfl
  have hMappedClosure :
      L g ∈ closure
        (periodicHypercubicEvenBoundaryActualPlaquetteAlgebraBoundedCarrier H) :=
    mem_closure_iff_seq_limit.mpr ⟨fun m => L (u m), huCarrier, huMappedTendsto⟩
  simpa [L, g,
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction]
    using hMappedClosure

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

private abbrev actualPlaquettePositiveTimeBridgePreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualPlaquettePositiveTimeBridgeTwoRankPositive beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 actualPlaquettePositiveTimeBridgeTwoRankPositive
      beta hbeta Q.toWeakStarBridge hInvariant n

/-- Approximate physical positive-time realization of the actual plaquette
carrier is already sufficient for the explicit raw actual-analysis mode.

Unlike an exact section into `range (Q.positiveHalfPullback n)`, the hypothesis
only asks each finite actual-plaquette observable to lie in the sup-norm closure
of that range.  Since the target raw mode is itself in the closure of the
actual plaquette carrier, Mathlib's `closure_minimal` closes the two
approximations without choosing or diagonalizing approximating sequences. -/
theorem
    normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_actualPlaquetteAlgebra_closure_lift
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualPlaquettePositiveTimeBridgeTwoRankPositive beta hbeta)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hLiftClosure :
      periodicHypercubicEvenBoundaryActualPlaquetteAlgebraBoundedCarrier
          (halfExtent n) ⊆
        closure (LinearMap.range (Q.positiveHalfPullback n))) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveHalfPullback n)) := by
  exact
    (closure_minimal hLiftClosure isClosed_closure)
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction_mem_actualPlaquetteAlgebraBoundedCarrier_closure
        (halfExtent n) (beta n) (hbeta n) k c)

/-- The approximate actual-plaquette realization hypothesis also reaches the
open-half Haar `L²` range closure through Mathlib's canonical
bounded-continuous-to-`L²` map.  Thus no exact positive-time preimage is needed
at either the `C⁰` or `L²` level. -/
theorem
    normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2RangeClosure_of_actualPlaquetteAlgebra_closure_lift
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualPlaquettePositiveTimeBridgeTwoRankPositive beta hbeta)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hLiftClosure :
      periodicHypercubicEvenBoundaryActualPlaquetteAlgebraBoundedCarrier
          (halfExtent n) ⊆
        closure (LinearMap.range (Q.positiveHalfPullback n))) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)) := by
  apply
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2RangeClosure_of_mem_positiveHalfPullbackRangeClosure
  exact
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_actualPlaquetteAlgebra_closure_lift
      n k c hLiftClosure

/-- The remaining approximation premise can now be stated entirely with the
already-constructed finite OS observables.  If every bounded actual-plaquette
observable is a sup-norm limit of finite positive-half OS observables, the raw
actual-analysis mode lies in the coherent positive-half pullback closure.

The proof uses the exact range equality proved for the OS carrier and then only
Mathlib closure transport.  No global density, section, or multiplicativity of
the coherent pullback is asserted. -/
theorem
    normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_actualPlaquetteAlgebra_finitePositiveHalfObservable_closure_lift
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualPlaquettePositiveTimeBridgeTwoRankPositive beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hFiniteLiftClosure :
      periodicHypercubicEvenBoundaryActualPlaquetteAlgebraBoundedCarrier
          (halfExtent n) ⊆
        closure
          (Set.range
            (fun F : (actualPlaquettePositiveTimeBridgePreHilbert
                Q hInvariant n).Carrier =>
              physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
                S D halfExtent 2 actualPlaquettePositiveTimeBridgeTwoRankPositive
                  beta hbeta Q.toWeakStarBridge hInvariant n F))) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveHalfPullback n)) := by
  apply
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_actualPlaquetteAlgebra_closure_lift
      n k c
  intro f hf
  rw [← Q.finitePositiveHalfObservable_rangeClosure_eq_positiveHalfPullback_rangeClosure
    hInvariant n]
  exact hFiniteLiftClosure hf

/-- The same finite-OS approximation premise reaches the actual open-half Haar
`L²` range closure.  This is the exact analytic input consumed by the
closure-derived reconstructed-excitation route. -/
theorem
    normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2RangeClosure_of_actualPlaquetteAlgebra_finitePositiveHalfObservable_closure_lift
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualPlaquettePositiveTimeBridgeTwoRankPositive beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hFiniteLiftClosure :
      periodicHypercubicEvenBoundaryActualPlaquetteAlgebraBoundedCarrier
          (halfExtent n) ⊆
        closure
          (Set.range
            (fun F : (actualPlaquettePositiveTimeBridgePreHilbert
                Q hInvariant n).Carrier =>
              physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
                S D halfExtent 2 actualPlaquettePositiveTimeBridgeTwoRankPositive
                  beta hbeta Q.toWeakStarBridge hInvariant n F))) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)) := by
  apply
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2RangeClosure_of_mem_positiveHalfPullbackRangeClosure
  exact
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_actualPlaquetteAlgebra_finitePositiveHalfObservable_closure_lift
      hInvariant n k c hFiniteLiftClosure

/-- Terminal reconstructed-Hamiltonian consequence of approximate realization
by genuine finite OS observables.  All actual plaquette/Gibbs/Bochner `C⁰`
approximation and the canonical `C⁰ → L²` transfer are theorem-generated;
nonemptiness of the physical excitation domain and nonnegativity of the
variational mass then follow from the existing OS Hamiltonian theory.

The only model-facing approximation input is the finite-OS closure statement
above.  No numerical mass value, decay rate, coercivity constant, determinant,
projective-surjectivity, global density, or multiplicativity premise is added. -/
theorem
    normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_actualPlaquetteAlgebra_finitePositiveHalfObservable_closure_lift
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualPlaquettePositiveTimeBridgeTwoRankPositive beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hH : 1 < halfExtent n)
    (hbetaPos : 0 < beta n)
    (hc : c ≠ 0)
    (hzero :
      inner ℝ
        (periodicHypercubicEvenBoundaryMarginalVacuumL2
          (halfExtent n) (beta n) (hbeta n))
        (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
          (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hFiniteLiftClosure :
      periodicHypercubicEvenBoundaryActualPlaquetteAlgebraBoundedCarrier
          (halfExtent n) ⊆
        closure
          (Set.range
            (fun F : (actualPlaquettePositiveTimeBridgePreHilbert
                Q hInvariant n).Carrier =>
              physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
                S D halfExtent 2 actualPlaquettePositiveTimeBridgeTwoRankPositive
                  beta hbeta Q.toWeakStarBridge hInvariant n F)))
    (T : (actualPlaquettePositiveTimeBridgePreHilbert
      Q hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    0 ≤ T.physicalYangMillsMass := by
  apply
    Q.normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure
      hInvariant U n k c hH hbetaPos hc hzero _ T hSelf
  exact
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_actualPlaquetteAlgebra_finitePositiveHalfObservable_closure_lift
      hInvariant n k c hFiniteLiftClosure

/-- Once every bounded actual-plaquette-algebra observable is realized by the
existing coherent positive-time pullback, the explicit raw actual-analysis
mode belongs to the required positive-half range closure.

This is the precise non-density frontier.  The approximation statement itself
is now theorem-generated from the actual finite plaquette/Wilson construction;
the only remaining input is the concrete realization of that algebraic carrier
inside the pre-existing physical positive-time pullback range. -/
theorem
    normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_actualPlaquetteAlgebra_lift
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualPlaquettePositiveTimeBridgeTwoRankPositive beta hbeta)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hLift :
      periodicHypercubicEvenBoundaryActualPlaquetteAlgebraBoundedCarrier
          (halfExtent n) ⊆
        LinearMap.range (Q.positiveHalfPullback n)) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveHalfPullback n)) := by
  apply closure_mono hLift
  exact
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction_mem_actualPlaquetteAlgebraBoundedCarrier_closure
      (halfExtent n) (beta n) (hbeta n) k c

/-- The same concrete actual-plaquette realization hypothesis reaches the
already-established open-half Haar `L²` range closure.  Thus all approximation,
Gibbs-exponential, boundary-integration, and `C⁰ → L²` work is discharged before
the remaining physical positive-time realization step. -/
theorem
    normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2RangeClosure_of_actualPlaquetteAlgebra_lift
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualPlaquettePositiveTimeBridgeTwoRankPositive beta hbeta)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hLift :
      periodicHypercubicEvenBoundaryActualPlaquetteAlgebraBoundedCarrier
          (halfExtent n) ⊆
        LinearMap.range (Q.positiveHalfPullback n)) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)) := by
  apply
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2RangeClosure_of_mem_positiveHalfPullbackRangeClosure
  exact
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_actualPlaquetteAlgebra_lift
      n k c hLift

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
