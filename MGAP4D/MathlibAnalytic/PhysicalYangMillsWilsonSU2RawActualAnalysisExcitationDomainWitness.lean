import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2RawActualAnalysisPhysicalExcitation
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedMassExcitationWitness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

private theorem rawActualAnalysisExcitationDomainTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance rawActualAnalysisExcitationDomainTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance rawActualAnalysisExcitationDomainCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance rawActualAnalysisExcitationDomainSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance rawActualAnalysisExcitationDomainMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance rawActualAnalysisExcitationDomainBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance rawActualAnalysisExcitationDomainSU2Nontrivial :
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

/-- The explicit raw actual-Wilson witness realization reaches the domain of
the already-constructed self-adjoint OS Hamiltonian.  The finite realization
condition is exactly the raw continuous analysis witness lying in the coherent
positive-half carrier range; no range condition on the full abstract `A f`
output and no new spectral or mass assumption is introduced. -/
noncomputable def normalizedTracePolynomial_excitationDomainWitness_of_rawActualAnalysis_range
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 rawActualAnalysisExcitationDomainTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility Q hInvariant)
    (n k : ℕ) (c : Fin (k + 1) → ℝ) (hH : 1 < halfExtent n) (hbetaPos : 0 < beta n) (hc : c ≠ 0)
    (hzero : inner ℝ (periodicHypercubicEvenBoundaryMarginalVacuumL2 (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2 (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hRawRange : periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
      (halfExtent n) (beta n) (hbeta n) k c ∈ (Q.positiveHalfL2LinearMap hInvariant n).range)
    (T : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
      rawActualAnalysisExcitationDomainTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    T.PhysicalYangMillsExcitationDomainWitness := by
  let Pn := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 rawActualAnalysisExcitationDomainTwoRankPositive beta hbeta
    Q.toWeakStarBridge hInvariant n
  have hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent 2 rawActualAnalysisExcitationDomainTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  have hNonempty : Nonempty T.PhysicalYangMillsExcitationDomainWitness := by
    rcases Q.normalizedTracePolynomial_exists_nonzero_vacuumOrthogonalPhysicalState_of_rawActualAnalysis_range
        hInvariant U n k c hH hbetaPos hc hzero hRawRange with ⟨psi, hpsi⟩
    exact ⟨T.physicalYangMillsExcitationDomainWitness_of_nonzeroExcitation
      hPn hSelf psi hpsi⟩
  exact Classical.choice hNonempty

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
