import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ActualPlaquetteGeneratorReadout
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ActualPlaquetteAlgebraPositiveTimeBridge
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2RawActualAnalysisReadableCylinderAlgebra
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem actualPlaquetteGeneratorAlgebraLiftTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance actualPlaquetteGeneratorAlgebraLiftNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance actualPlaquetteGeneratorAlgebraLiftTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance actualPlaquetteGeneratorAlgebraLiftCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance actualPlaquetteGeneratorAlgebraLiftSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance actualPlaquetteGeneratorAlgebraLiftMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance actualPlaquetteGeneratorAlgebraLiftBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance actualPlaquetteGeneratorAlgebraLiftSU2Nontrivial :
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

private abbrev actualPlaquetteGeneratorAlgebraLiftPreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualPlaquetteGeneratorAlgebraLiftTwoRankPositive beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 actualPlaquetteGeneratorAlgebraLiftTwoRankPositive
      beta hbeta Q.toWeakStarBridge hInvariant n

/-- Generator-by-generator physical readout is sufficient to realize the whole
bounded actual plaquette algebra inside the readable positive-half cylinder
algebra.

The proof is the canonical Mathlib algebra argument.  The actual continuous
plaquette algebra is `Algebra.adjoin` of the elementary plaquette energies; the
compact-domain conversion to bounded-continuous functions is an `AlgHom`; and
the readable physical cylinder targets are already a `Subalgebra`.  Therefore
`Algebra.adjoin_le` propagates generator readout to every finite polynomial
without ever asking the coherent positive-half pullback to be multiplicative. -/
theorem actualPlaquetteAlgebraBoundedCarrier_subset_positiveHalfCylinderReadableSubalgebra_of_generatorReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualPlaquetteGeneratorAlgebraLiftTwoRankPositive beta hbeta)
    (n : ℕ)
    (R : PhysicalYangMillsWilsonSU2ActualPlaquetteGeneratorReadout Q n) :
    periodicHypercubicEvenBoundaryActualPlaquetteAlgebraBoundedCarrier
        (halfExtent n) ⊆
      (↑(positiveHalfCylinderReadableSubalgebra Q n) :
        Set (BoundedContinuousFunction
          (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
            (halfExtent n) 2) ℝ)) := by
  let X := PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
    (halfExtent n) 2
  let L := continuousMapAlgHomBoundedOfCompact X
  let B := positiveHalfCylinderReadableSubalgebra Q n
  have hAdjoin :
      periodicHypercubicEvenBoundaryActualPlaquetteAlgebra
          (halfExtent n) 2 actualPlaquetteGeneratorAlgebraLiftTwoRankPositive ≤
        B.comap L := by
    unfold periodicHypercubicEvenBoundaryActualPlaquetteAlgebra
    apply Algebra.adjoin_le
    rintro f ⟨⟨b, p⟩, rfl⟩
    change
      L (periodicHypercubicEvenBoundaryPlaquetteEnergyContinuousMap
        (halfExtent n) 2 actualPlaquetteGeneratorAlgebraLiftTwoRankPositive b p) ∈ B
    simpa [L, B,
      periodicHypercubicEvenBoundaryPlaquetteEnergyBoundedContinuousFunction] using
      R.boundedGenerator_mem_positiveHalfCylinderReadableSubalgebra b p
  intro f hf
  rcases hf with ⟨g, rfl⟩
  have hg := hAdjoin g.2
  change L g.1 ∈ B at hg
  simpa [L, B, continuousMapAlgHomBoundedOfCompact] using hg

/-- Consequently the explicit raw actual-analysis mode is a uniform limit of
genuine readable physical positive-half cylinder targets whenever the elementary
actual plaquette generators admit the generator readout above.

All Gibbs-factor, polynomial, Gram-feature and Bochner approximation work is
reused from the existing actual `C⁰` closure theorem. -/
theorem normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfCylinderReadableSubalgebraClosure_of_actualPlaquetteGeneratorReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualPlaquetteGeneratorAlgebraLiftTwoRankPositive beta hbeta)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (R : PhysicalYangMillsWilsonSU2ActualPlaquetteGeneratorReadout Q n) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure
        (↑(positiveHalfCylinderReadableSubalgebra Q n) :
          Set (BoundedContinuousFunction
            (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
              (halfExtent n) 2) ℝ)) := by
  exact
    (closure_mono
      (Q.actualPlaquetteAlgebraBoundedCarrier_subset_positiveHalfCylinderReadableSubalgebra_of_generatorReadout
        n R))
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction_mem_actualPlaquetteAlgebraBoundedCarrier_closure
        (halfExtent n) (beta n) (hbeta n) k c)

/-- Generator-level actual plaquette realization therefore reaches the coherent
positive-half pullback range closure through the theorem-generated readable
cylinder algebra. -/
theorem normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_actualPlaquetteGeneratorReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualPlaquetteGeneratorAlgebraLiftTwoRankPositive beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (R : PhysicalYangMillsWilsonSU2ActualPlaquetteGeneratorReadout Q n) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveHalfPullback n)) := by
  apply
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_mem_positiveHalfCylinderReadableSubalgebraClosure
      C hInvariant U n k c
  exact
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfCylinderReadableSubalgebraClosure_of_actualPlaquetteGeneratorReadout
      n k c R

/-- Terminal reconstructed-Hamiltonian consequence of generator-level actual
plaquette realization.  This theorem adds no new Hamiltonian or spectral
hypothesis; it only discharges the `C⁰` readable-cylinder premise of the #1670
physical-mass route from elementary actual plaquette readouts. -/
theorem normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_actualPlaquetteGeneratorReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualPlaquetteGeneratorAlgebraLiftTwoRankPositive beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
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
    (R : PhysicalYangMillsWilsonSU2ActualPlaquetteGeneratorReadout Q n)
    (T : (actualPlaquetteGeneratorAlgebraLiftPreHilbert
      Q hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    0 ≤ T.physicalYangMillsMass := by
  apply
    Q.normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_mem_positiveHalfCylinderReadableSubalgebraClosure
      C hInvariant U n k c hH hbetaPos hc hzero _ T hSelf
  exact
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfCylinderReadableSubalgebraClosure_of_actualPlaquetteGeneratorReadout
      n k c R

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
