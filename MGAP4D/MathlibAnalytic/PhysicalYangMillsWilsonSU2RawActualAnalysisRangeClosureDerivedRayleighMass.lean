import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2RawActualAnalysisClosureDerivedRayleighMass
import Mathlib.Topology.Sequences
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set Topology
open scoped InnerProduct InnerProductSpace

noncomputable section

private theorem rawActualAnalysisRangeClosureTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance rawActualAnalysisRangeClosureTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance rawActualAnalysisRangeClosureCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance rawActualAnalysisRangeClosureSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance rawActualAnalysisRangeClosureMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance rawActualAnalysisRangeClosureBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance rawActualAnalysisRangeClosureSU2Nontrivial :
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

private abbrev rawActualAnalysisRangeClosurePreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 rawActualAnalysisRangeClosureTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 rawActualAnalysisRangeClosureTwoRankPositive beta hbeta
    Q.toWeakStarBridge hInvariant n

/-- The explicit raw actual-analysis Wilson vector need not have an exact
positive-half preimage, nor does an approximating sequence have to be supplied
as data.  Membership in the topological closure of the actual coherent
positive-half `L²` image is enough.

Mathlib's Fréchet--Urysohn closure theorem produces an image-valued sequence
converging to the target.  Choosing carrier preimages of that sequence reduces
this exact closure statement to the previously proved finite-stage strict
pairing argument.  Hence the remaining realizability frontier is precisely the
single target-specific closure membership below. -/
theorem normalizedTracePolynomial_exists_nonzero_vacuumOrthogonalPhysicalState_of_rawActualAnalysis_mem_rangeClosure
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 rawActualAnalysisRangeClosureTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility Q hInvariant)
    (n k : ℕ) (c : Fin (k + 1) → ℝ) (hH : 1 < halfExtent n) (hbetaPos : 0 < beta n) (hc : c ≠ 0)
    (hzero : inner ℝ (periodicHypercubicEvenBoundaryMarginalVacuumL2 (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2 (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hClosure : periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
      (halfExtent n) (beta n) (hbeta n) k c ∈ closure
        (LinearMap.range (Q.positiveHalfL2LinearMap hInvariant n))) :
    let Pn := rawActualAnalysisRangeClosurePreHilbert Q hInvariant n
    ∃ psi : Pn.VacuumOrthogonalHilbert, psi ≠ 0 := by
  dsimp only
  let Pn := rawActualAnalysisRangeClosurePreHilbert Q hInvariant n
  let g := periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
    (halfExtent n) (beta n) (hbeta n) k c
  have hClosureG : g ∈ closure (LinearMap.range (Q.positiveHalfL2LinearMap hInvariant n)) := by
    simpa [g] using hClosure
  rcases (mem_closure_iff_seq_limit.mp hClosureG) with ⟨u, huRange, huTendsto⟩
  choose Fseq hFseq using huRange
  have hSeqEq : (fun m => Q.positiveHalfL2LinearMap hInvariant n (Fseq m)) = u := by
    funext m
    exact hFseq m
  have hApprox : Tendsto
      (fun m => Q.positiveHalfL2LinearMap hInvariant n (Fseq m)) atTop (𝓝 g) := by
    rw [hSeqEq]
    exact huTendsto
  exact Q.normalizedTracePolynomial_exists_nonzero_vacuumOrthogonalPhysicalState_of_rawActualAnalysis_tendsto
    hInvariant U n k c hH hbetaPos hc hzero Fseq (by simpa [g] using hApprox)

/-- Closure realizability of the explicit raw Wilson mode therefore suffices for
nonnegativity of the variational mass of the reconstructed closed physical
Hamiltonian.  No exact range witness, chosen approximation sequence, numerical
mass value, decay rate, coercivity constant, determinant assumption, or
projective-surjectivity assumption is introduced. -/
theorem normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_rawActualAnalysis_mem_rangeClosure
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 rawActualAnalysisRangeClosureTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility Q hInvariant)
    (n k : ℕ) (c : Fin (k + 1) → ℝ) (hH : 1 < halfExtent n) (hbetaPos : 0 < beta n) (hc : c ≠ 0)
    (hzero : inner ℝ (periodicHypercubicEvenBoundaryMarginalVacuumL2 (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2 (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hClosure : periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
      (halfExtent n) (beta n) (hbeta n) k c ∈ closure
        (LinearMap.range (Q.positiveHalfL2LinearMap hInvariant n)))
    (T : (rawActualAnalysisRangeClosurePreHilbert Q hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) : 0 ≤ T.physicalYangMillsMass := by
  let Pn := rawActualAnalysisRangeClosurePreHilbert Q hInvariant n
  have hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent 2 rawActualAnalysisRangeClosureTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  rcases Q.normalizedTracePolynomial_exists_nonzero_vacuumOrthogonalPhysicalState_of_rawActualAnalysis_mem_rangeClosure
      hInvariant U n k c hH hbetaPos hc hzero hClosure with ⟨psi, hpsi⟩
  let W := T.physicalYangMillsExcitationDomainWitness_of_nonzeroExcitation hPn hSelf psi hpsi
  exact T.physicalYangMillsMass_nonneg W

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
