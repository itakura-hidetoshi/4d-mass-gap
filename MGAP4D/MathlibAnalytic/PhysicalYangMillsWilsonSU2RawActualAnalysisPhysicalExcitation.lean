import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ActualAnalysisStrictPhysicalExcitation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryRawActualAnalysisOperatorNonzero
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

private theorem rawActualAnalysisPhysicalExcitationTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance rawActualAnalysisPhysicalExcitationTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance rawActualAnalysisPhysicalExcitationCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance rawActualAnalysisPhysicalExcitationSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance rawActualAnalysisPhysicalExcitationMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance rawActualAnalysisPhysicalExcitationBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance rawActualAnalysisPhysicalExcitationSU2Nontrivial :
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

/-- It is enough to realize the explicit raw continuous Wilson witness in the
coherent positive-half physical range; the full abstract analysis output need
not itself be assumed to lie in that range.

For the raw witness `g`, #1669 proves `⟪A f,g⟫ = ‖g‖²` and `g ≠ 0`.  After
vacuum centering a physical preimage of `g`, the extra scalar multiple of the
constant-one vector drops out against the centered actual output `A f`.  The
actual adjoint synthesis therefore has a strictly positive matrix coefficient,
which forces positive OS quadratic norm and hence a nonzero reconstructed
vacuum-orthogonal state. -/
theorem normalizedTracePolynomial_exists_nonzero_vacuumOrthogonalPhysicalState_of_rawActualAnalysis_range
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 rawActualAnalysisPhysicalExcitationTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility Q hInvariant)
    (n k : ℕ) (c : Fin (k + 1) → ℝ) (hH : 1 < halfExtent n) (hbetaPos : 0 < beta n) (hc : c ≠ 0)
    (hzero : inner ℝ (periodicHypercubicEvenBoundaryMarginalVacuumL2 (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2 (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hRawRange : periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
      (halfExtent n) (beta n) (hbeta n) k c ∈ (Q.positiveHalfL2LinearMap hInvariant n).range) :
    let Pn := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
      rawActualAnalysisPhysicalExcitationTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n
    ∃ psi : Pn.VacuumOrthogonalHilbert, psi ≠ 0 := by
  dsimp only
  let Pn := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 rawActualAnalysisPhysicalExcitationTwoRankPositive beta hbeta
    Q.toWeakStarBridge hInvariant n
  let f := periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
    (halfExtent n) (beta n) (hbeta n) k c
  let Aout := periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
    (halfExtent n) 2 rawActualAnalysisPhysicalExcitationTwoRankPositive (beta n) (hbeta n) f
  let g := periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
    (halfExtent n) (beta n) (hbeta n) k c
  let one := periodicHypercubicEvenOpenHalfConstantOneL2 (halfExtent n) 2
  change g ∈ (Q.positiveHalfL2LinearMap hInvariant n).range at hRawRange
  rcases hRawRange with ⟨F, hF⟩
  have hFimage : Q.positiveHalfL2LinearMap hInvariant n F = g := by
    simpa [g] using hF
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
  have hVacImage : Q.positiveHalfL2LinearMap hInvariant n Pn.vacuumObservable = one := by
    simpa [Pn, one] using
      Q.positiveHalfL2LinearMap_vacuum_eq_openHalfConstantOneL2 hInvariant U n
  let Fc := Pn.vacuumCenteredCarrier F
  have hFcImage : Q.positiveHalfL2LinearMap hInvariant n Fc =
      g - Pn.omega F.toGaugeInvariant • one := by
    change Q.positiveHalfL2LinearMap hInvariant n
      (F - Pn.omega F.toGaugeInvariant • Pn.vacuumObservable) = _
    rw [map_sub, map_smul, hFimage, hVacImage]
  have hFcSynthesisPos : 0 < inner ℝ
      (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent 2 rawActualAnalysisPhysicalExcitationTwoRankPositive beta hbeta n
        (Q.positiveHalfL2LinearMap hInvariant n Fc)) f := by
    change 0 < inner ℝ
      (periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
        (halfExtent n) 2 rawActualAnalysisPhysicalExcitationTwoRankPositive
        (beta n) (hbeta n) (Q.positiveHalfL2LinearMap hInvariant n Fc)) f
    rw [periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator_inner]
    change 0 < inner ℝ (Q.positiveHalfL2LinearMap hInvariant n Fc) Aout
    rw [hFcImage, inner_sub_left, inner_smul_left, hAoutCentered]
    simp only [mul_zero, sub_zero]
    rw [real_inner_comm, hpair]
    exact sq_pos_of_pos (norm_pos_iff.mpr hgNe)
  have hBoundaryNe : physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
      S D halfExtent 2 rawActualAnalysisPhysicalExcitationTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n Fc ≠ 0 := by
    rw [physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis]
    change physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
      halfExtent 2 rawActualAnalysisPhysicalExcitationTwoRankPositive beta hbeta n
      (Q.positiveHalfL2LinearMap hInvariant n Fc) ≠ 0
    intro hzeroBoundary
    rw [hzeroBoundary] at hFcSynthesisPos
    simpa using hFcSynthesisPos
  have hBoundaryNormPos : 0 < ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
      S D halfExtent 2 rawActualAnalysisPhysicalExcitationTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n Fc‖ := norm_pos_iff.mpr hBoundaryNe
  have hFcNormPos : 0 < ‖Fc‖ := by
    rw [physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_norm
      S D halfExtent 2 rawActualAnalysisPhysicalExcitationTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n Fc] at hBoundaryNormPos
    exact hBoundaryNormPos
  have hFcQuadraticPos : 0 < Pn.osQuadraticValue Fc := by
    rw [Pn.osQuadraticValue_eq_norm_sq]
    nlinarith
  have hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent 2 rawActualAnalysisPhysicalExcitationTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  refine ⟨Pn.centeredPhysicalExcitation hPn F, ?_⟩
  apply Pn.centeredPhysicalExcitation_ne_zero_of_osQuadraticValue_pos hPn F
  simpa [Fc] using hFcQuadraticPos

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
