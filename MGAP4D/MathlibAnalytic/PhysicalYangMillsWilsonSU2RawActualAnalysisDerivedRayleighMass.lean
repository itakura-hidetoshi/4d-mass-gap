import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2RawActualAnalysisExcitationDomainWitness
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedRayleighMass
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

private theorem rawActualAnalysisDerivedRayleighMassTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance rawActualAnalysisDerivedRayleighMassTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance rawActualAnalysisDerivedRayleighMassCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance rawActualAnalysisDerivedRayleighMassSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance rawActualAnalysisDerivedRayleighMassMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance rawActualAnalysisDerivedRayleighMassBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance rawActualAnalysisDerivedRayleighMassSU2Nontrivial :
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

/-- The explicit raw actual-Wilson realization makes the variational mass of
the reconstructed closed OS Hamiltonian nonnegative.  No numerical mass scale
is inserted: the conclusion is inherited from the Hamiltonian Rayleigh set. -/
theorem normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_rawActualAnalysis_range
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 rawActualAnalysisDerivedRayleighMassTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility Q hInvariant)
    (n k : ℕ) (c : Fin (k + 1) → ℝ) (hH : 1 < halfExtent n) (hbetaPos : 0 < beta n) (hc : c ≠ 0)
    (hzero : inner ℝ (periodicHypercubicEvenBoundaryMarginalVacuumL2 (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2 (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hRawRange : periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
      (halfExtent n) (beta n) (hbeta n) k c ∈ (Q.positiveHalfL2LinearMap hInvariant n).range)
    (T : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
      rawActualAnalysisDerivedRayleighMassTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    0 ≤ T.physicalYangMillsMass := by
  let W := Q.normalizedTracePolynomial_excitationDomainWitness_of_rawActualAnalysis_range
    hInvariant U n k c hH hbetaPos hc hzero hRawRange T hSelf
  exact T.physicalYangMillsMass_nonneg W

/-- Every uniform lower Rayleigh estimate proved for the actual reconstructed
Yang--Mills Hamiltonian lies below its variational mass once the explicit raw
Wilson mode has supplied nonemptiness of the excitation domain. -/
theorem normalizedTracePolynomial_uniformRayleighLowerBound_le_physicalYangMillsMass_of_rawActualAnalysis_range
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 rawActualAnalysisDerivedRayleighMassTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility Q hInvariant)
    (n k : ℕ) (c : Fin (k + 1) → ℝ) (hH : 1 < halfExtent n) (hbetaPos : 0 < beta n) (hc : c ≠ 0)
    (hzero : inner ℝ (periodicHypercubicEvenBoundaryMarginalVacuumL2 (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2 (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hRawRange : periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
      (halfExtent n) (beta n) (hbeta n) k c ∈ (Q.positiveHalfL2LinearMap hInvariant n).range)
    (T : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
      rawActualAnalysisDerivedRayleighMassTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {m : ℝ}
    (hLower :
      ∀ psi : T.closedRightHamiltonian.domain,
        (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
          rawActualAnalysisDerivedRayleighMassTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert) ≠ 0 →
        inner ℝ
          (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
            rawActualAnalysisDerivedRayleighMassTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert)
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
            rawActualAnalysisDerivedRayleighMassTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n).vacuum = 0 →
        m * ‖(psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
          rawActualAnalysisDerivedRayleighMassTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert)‖ ^ 2 ≤
          inner ℝ (T.closedRightHamiltonian psi)
            (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
              rawActualAnalysisDerivedRayleighMassTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert)) :
    m ≤ T.physicalYangMillsMass := by
  let W := Q.normalizedTracePolynomial_excitationDomainWitness_of_rawActualAnalysis_range
    hInvariant U n k c hH hbetaPos hc hzero hRawRange T hSelf
  exact T.uniformRayleighLowerBound_le_physicalYangMillsMass W hLower

/-- For the actual Wilson-reconstructed excitation sector, positivity of the
variational Yang--Mills mass is equivalent to a strictly positive uniform
Rayleigh lower bound on the closed Hamiltonian domain. -/
theorem normalizedTracePolynomial_physicalYangMillsMass_pos_iff_exists_uniformRayleighLowerBound_of_rawActualAnalysis_range
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 rawActualAnalysisDerivedRayleighMassTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility Q hInvariant)
    (n k : ℕ) (c : Fin (k + 1) → ℝ) (hH : 1 < halfExtent n) (hbetaPos : 0 < beta n) (hc : c ≠ 0)
    (hzero : inner ℝ (periodicHypercubicEvenBoundaryMarginalVacuumL2 (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2 (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hRawRange : periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
      (halfExtent n) (beta n) (hbeta n) k c ∈ (Q.positiveHalfL2LinearMap hInvariant n).range)
    (T : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
      rawActualAnalysisDerivedRayleighMassTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    0 < T.physicalYangMillsMass ↔
      ∃ m : ℝ, 0 < m ∧
        ∀ psi : T.closedRightHamiltonian.domain,
          (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
            rawActualAnalysisDerivedRayleighMassTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert) ≠ 0 →
          inner ℝ
            (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
              rawActualAnalysisDerivedRayleighMassTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert)
            (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
              rawActualAnalysisDerivedRayleighMassTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n).vacuum = 0 →
          m * ‖(psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
            rawActualAnalysisDerivedRayleighMassTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert)‖ ^ 2 ≤
            inner ℝ (T.closedRightHamiltonian psi)
              (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
                rawActualAnalysisDerivedRayleighMassTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert) := by
  let W := Q.normalizedTracePolynomial_excitationDomainWitness_of_rawActualAnalysis_range
    hInvariant U n k c hH hbetaPos hc hzero hRawRange T hSelf
  exact T.physicalYangMillsMass_pos_iff_exists_uniformRayleighLowerBound W

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
