import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2RawActualAnalysisDerivedRayleighMass
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Topology
open scoped InnerProduct InnerProductSpace

noncomputable section

private theorem rawActualAnalysisClosureTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance rawActualAnalysisClosureTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance rawActualAnalysisClosureCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance rawActualAnalysisClosureSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance rawActualAnalysisClosureMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance rawActualAnalysisClosureBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance rawActualAnalysisClosureSU2Nontrivial :
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

private abbrev rawActualAnalysisClosurePreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 rawActualAnalysisClosureTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 rawActualAnalysisClosureTwoRankPositive beta hbeta
    Q.toWeakStarBridge hInvariant n

/-- Exact raw-Wilson range membership is unnecessary for producing a physical
excitation.  It suffices that images of genuine coherent positive-half carrier
vectors converge in open-half Haar `L²` to the explicit raw actual-analysis
vector.

The strict raw pairing `⟪A f,g⟫ = ‖g‖² > 0` survives at some finite stage by
continuity of the inner product.  Vacuum centering of that finite carrier then
removes only a constant-one component, which is orthogonal to the centered
actual output.  Thus a genuine reconstructed vacuum-orthogonal state is already
nonzero at one finite approximating stage. -/
theorem normalizedTracePolynomial_exists_nonzero_vacuumOrthogonalPhysicalState_of_rawActualAnalysis_tendsto
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 rawActualAnalysisClosureTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility Q hInvariant)
    (n k : ℕ) (c : Fin (k + 1) → ℝ) (hH : 1 < halfExtent n) (hbetaPos : 0 < beta n) (hc : c ≠ 0)
    (hzero : inner ℝ (periodicHypercubicEvenBoundaryMarginalVacuumL2 (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2 (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (Fseq : ℕ → (rawActualAnalysisClosurePreHilbert Q hInvariant n).Carrier)
    (hApprox : Tendsto (fun m => Q.positiveHalfL2LinearMap hInvariant n (Fseq m)) atTop
      (𝓝 (periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c))) :
    let Pn := rawActualAnalysisClosurePreHilbert Q hInvariant n
    ∃ psi : Pn.VacuumOrthogonalHilbert, psi ≠ 0 := by
  dsimp only
  let Pn := rawActualAnalysisClosurePreHilbert Q hInvariant n
  let f := periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
    (halfExtent n) (beta n) (hbeta n) k c
  let Aout := periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
    (halfExtent n) 2 rawActualAnalysisClosureTwoRankPositive (beta n) (hbeta n) f
  let g := periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
    (halfExtent n) (beta n) (hbeta n) k c
  let one := periodicHypercubicEvenOpenHalfConstantOneL2 (halfExtent n) 2
  have hgNe : g ≠ 0 := by
    rcases periodicHypercubicEvenNormalizedTracePolynomial_exists_positiveDegree_rawActualAnalysisHaarL2_ne_zero
        (halfExtent n) hH (beta n) hbetaPos k c hc with ⟨_i, _hi, hg⟩
    simpa [g] using hg
  have hAoutCentered : inner ℝ one Aout = 0 := by
    simpa [one, Aout, f] using
      periodicHypercubicEvenBoundaryNormalizedTracePolynomial_actualAnalysisOutput_centered
        (halfExtent n) (beta n) (hbeta n) k c hzero
  have hpair : inner ℝ Aout g = ‖g‖ ^ 2 := by
    simpa [Aout, f, g] using
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_inner_rawActualAnalysisHaarL2_eq_norm_sq
        (halfExtent n) (beta n) (hbeta n) k c
  have hLimitPos : 0 < inner ℝ g Aout := by
    rw [real_inner_comm, hpair]
    exact sq_pos_of_pos (norm_pos_iff.mpr hgNe)
  have hApproxG : Tendsto
      (fun m => Q.positiveHalfL2LinearMap hInvariant n (Fseq m)) atTop (𝓝 g) := by
    simpa [g] using hApprox
  have hPairTendsto : Tendsto
      (fun m => inner ℝ (Q.positiveHalfL2LinearMap hInvariant n (Fseq m)) Aout)
      atTop (𝓝 (inner ℝ g Aout)) := by
    exact hApproxG.inner tendsto_const_nhds
  have hEventuallyPos : ∀ᶠ m in atTop,
      0 < inner ℝ (Q.positiveHalfL2LinearMap hInvariant n (Fseq m)) Aout := by
    exact hPairTendsto.eventually (Ioi_mem_nhds hLimitPos)
  rcases hEventuallyPos.exists with ⟨m, hm⟩
  let F := Fseq m
  have hFpair : 0 < inner ℝ (Q.positiveHalfL2LinearMap hInvariant n F) Aout := by
    simpa [F] using hm
  have hVacImage : Q.positiveHalfL2LinearMap hInvariant n Pn.vacuumObservable = one := by
    simpa [Pn, one] using
      Q.positiveHalfL2LinearMap_vacuum_eq_openHalfConstantOneL2 hInvariant U n
  let Fc := Pn.vacuumCenteredCarrier F
  have hFcImage : Q.positiveHalfL2LinearMap hInvariant n Fc =
      Q.positiveHalfL2LinearMap hInvariant n F - Pn.omega F.toGaugeInvariant • one := by
    change Q.positiveHalfL2LinearMap hInvariant n
      (F - Pn.omega F.toGaugeInvariant • Pn.vacuumObservable) = _
    rw [map_sub, map_smul, hVacImage]
  have hFcSynthesisPos : 0 < inner ℝ
      (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent 2 rawActualAnalysisClosureTwoRankPositive beta hbeta n
        (Q.positiveHalfL2LinearMap hInvariant n Fc)) f := by
    change 0 < inner ℝ
      (periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
        (halfExtent n) 2 rawActualAnalysisClosureTwoRankPositive
        (beta n) (hbeta n) (Q.positiveHalfL2LinearMap hInvariant n Fc)) f
    rw [periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator_inner]
    change 0 < inner ℝ (Q.positiveHalfL2LinearMap hInvariant n Fc) Aout
    rw [hFcImage, inner_sub_left, inner_smul_left, hAoutCentered]
    simpa using hFpair
  have hBoundaryNe : physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
      S D halfExtent 2 rawActualAnalysisClosureTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n Fc ≠ 0 := by
    rw [physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis]
    change physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
      halfExtent 2 rawActualAnalysisClosureTwoRankPositive beta hbeta n
      (Q.positiveHalfL2LinearMap hInvariant n Fc) ≠ 0
    intro hzeroBoundary
    rw [hzeroBoundary] at hFcSynthesisPos
    simpa using hFcSynthesisPos
  have hBoundaryNormPos : 0 < ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
      S D halfExtent 2 rawActualAnalysisClosureTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n Fc‖ := norm_pos_iff.mpr hBoundaryNe
  have hFcNormPos : 0 < ‖Fc‖ := by
    rw [physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_norm
      S D halfExtent 2 rawActualAnalysisClosureTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n Fc] at hBoundaryNormPos
    exact hBoundaryNormPos
  have hFcQuadraticPos : 0 < Pn.osQuadraticValue Fc := by
    rw [Pn.osQuadraticValue_eq_norm_sq]
    nlinarith
  have hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent 2 rawActualAnalysisClosureTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  refine ⟨Pn.centeredPhysicalExcitation hPn F, ?_⟩
  apply Pn.centeredPhysicalExcitation_ne_zero_of_osQuadraticValue_pos hPn F
  simpa [Fc] using hFcQuadraticPos

/-- A raw Wilson `L²`-closure realization already makes the closed Hamiltonian
excitation domain nonempty; no exact positive-half preimage is selected. -/
noncomputable def normalizedTracePolynomial_excitationDomainWitness_of_rawActualAnalysis_tendsto
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 rawActualAnalysisClosureTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility Q hInvariant)
    (n k : ℕ) (c : Fin (k + 1) → ℝ) (hH : 1 < halfExtent n) (hbetaPos : 0 < beta n) (hc : c ≠ 0)
    (hzero : inner ℝ (periodicHypercubicEvenBoundaryMarginalVacuumL2 (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2 (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (Fseq : ℕ → (rawActualAnalysisClosurePreHilbert Q hInvariant n).Carrier)
    (hApprox : Tendsto (fun m => Q.positiveHalfL2LinearMap hInvariant n (Fseq m)) atTop
      (𝓝 (periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c)))
    (T : (rawActualAnalysisClosurePreHilbert Q hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    T.PhysicalYangMillsExcitationDomainWitness := by
  let Pn := rawActualAnalysisClosurePreHilbert Q hInvariant n
  have hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent 2 rawActualAnalysisClosureTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  have hNonempty : Nonempty T.PhysicalYangMillsExcitationDomainWitness := by
    rcases Q.normalizedTracePolynomial_exists_nonzero_vacuumOrthogonalPhysicalState_of_rawActualAnalysis_tendsto
        hInvariant U n k c hH hbetaPos hc hzero Fseq hApprox with ⟨psi, hpsi⟩
    exact ⟨T.physicalYangMillsExcitationDomainWitness_of_nonzeroExcitation
      hPn hSelf psi hpsi⟩
  exact Classical.choice hNonempty

/-- The actual reconstructed variational Yang--Mills mass is nonnegative under
raw Wilson `L²`-closure realization.  No numerical mass value is inserted. -/
theorem normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_rawActualAnalysis_tendsto
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 rawActualAnalysisClosureTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility Q hInvariant)
    (n k : ℕ) (c : Fin (k + 1) → ℝ) (hH : 1 < halfExtent n) (hbetaPos : 0 < beta n) (hc : c ≠ 0)
    (hzero : inner ℝ (periodicHypercubicEvenBoundaryMarginalVacuumL2 (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2 (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (Fseq : ℕ → (rawActualAnalysisClosurePreHilbert Q hInvariant n).Carrier)
    (hApprox : Tendsto (fun m => Q.positiveHalfL2LinearMap hInvariant n (Fseq m)) atTop
      (𝓝 (periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c)))
    (T : (rawActualAnalysisClosurePreHilbert Q hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    0 ≤ T.physicalYangMillsMass := by
  let W := Q.normalizedTracePolynomial_excitationDomainWitness_of_rawActualAnalysis_tendsto
    hInvariant U n k c hH hbetaPos hc hzero Fseq hApprox T hSelf
  exact T.physicalYangMillsMass_nonneg W

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
