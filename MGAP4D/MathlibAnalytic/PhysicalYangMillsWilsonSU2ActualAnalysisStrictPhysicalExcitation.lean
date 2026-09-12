import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonActualAnalysisNonzeroCriterion
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryMarginalVacuumNormalization
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCenteredQuadraticExcitation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

private theorem actualAnalysisStrictPhysicalExcitationTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance actualAnalysisStrictPhysicalExcitationTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance actualAnalysisStrictPhysicalExcitationCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance actualAnalysisStrictPhysicalExcitationSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance actualAnalysisStrictPhysicalExcitationMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance actualAnalysisStrictPhysicalExcitationBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance actualAnalysisStrictPhysicalExcitationSU2Nontrivial :
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

/-- Vacuum-unit compatibility identifies the coherent positive-half `L²` image
of the finite OS vacuum with the concrete constant-one vector used by the
actual Wilson vacuum-orthogonality theorem. -/
theorem positiveHalfL2LinearMap_vacuum_eq_openHalfConstantOneL2
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n : ℕ) :
    let Pn := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
    Q.positiveHalfL2LinearMap hInvariant n Pn.vacuumObservable =
      periodicHypercubicEvenOpenHalfConstantOneL2 (halfExtent n) 2 := by
  dsimp only
  change physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
      S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
      ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n).vacuumObservable) = _
  unfold physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
  rw [U.finitePositiveHalfObservable_vacuum_eq_one n]
  rfl

/-- The centered/nonzero actual-analysis output from #1669 yields a genuine
nonzero vector in the already-constructed OS vacuum-orthogonal Hilbert sector
whenever that *analysis output* is realized by the existing coherent
positive-half carrier map.

After vacuum centering, the positive-half image has the form `A f - a • 1`.
Pairing its actual adjoint synthesis with `f` gives
`⟪A† (A f - a • 1), f⟫ = ‖A f‖² > 0`, because #1669 supplies both
`A f ≠ 0` and `A f ⟂ 1`.  Hence the centered boundary moment is nonzero, its
OS quadratic value is strictly positive, and the existing OS completion yields
a nonzero vacuum-orthogonal physical state.  No static `A† A` operator is
identified with Euclidean time evolution. -/
theorem normalizedTracePolynomial_exists_nonzero_vacuumOrthogonalPhysicalState_of_analysisImage_range_of_factorized_inner_self_pos
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility Q hInvariant)
    (n k : ℕ) (c : Fin (k + 1) → ℝ)
    (hzero : inner ℝ (periodicHypercubicEvenBoundaryMarginalVacuumL2 (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2 (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hpos : 0 < inner ℝ
      (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator (halfExtent n) 2
        actualAnalysisStrictPhysicalExcitationTwoRankPositive (beta n) (hbeta n)
        (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2 (halfExtent n) (beta n) (hbeta n) k c))
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2 (halfExtent n) (beta n) (hbeta n) k c))
    (hAnalysisRange : periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator (halfExtent n) 2
      actualAnalysisStrictPhysicalExcitationTwoRankPositive (beta n) (hbeta n)
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2 (halfExtent n) (beta n) (hbeta n) k c) ∈
      (Q.positiveHalfL2LinearMap hInvariant n).range) :
    let Pn := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
    ∃ psi : Pn.VacuumOrthogonalHilbert, psi ≠ 0 := by
  dsimp only
  let Pn := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
    Q.toWeakStarBridge hInvariant n
  let Aout := periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
    (halfExtent n) 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive (beta n) (hbeta n)
    (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
      (halfExtent n) (beta n) (hbeta n) k c)
  let one := periodicHypercubicEvenOpenHalfConstantOneL2 (halfExtent n) 2
  change Aout ∈ (Q.positiveHalfL2LinearMap hInvariant n).range at hAnalysisRange
  rcases hAnalysisRange with ⟨F, hF⟩
  have hFimage : Q.positiveHalfL2LinearMap hInvariant n F = Aout := by
    simpa [Aout] using hF
  have hAoutNe : Aout ≠ 0 := by
    simpa [Aout] using
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_apply_ne_zero_of_factorized_inner_self_pos
        (beta n) (hbeta n)
        (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
          (halfExtent n) (beta n) (hbeta n) k c) hpos
  have hAoutCentered : inner ℝ one Aout = 0 := by
    simpa [one, Aout] using
      periodicHypercubicEvenBoundaryNormalizedTracePolynomial_actualAnalysisOutput_centered
        (halfExtent n) (beta n) (hbeta n) k c hzero
  have hVacImage : Q.positiveHalfL2LinearMap hInvariant n Pn.vacuumObservable = one := by
    simpa [Pn, one] using
      Q.positiveHalfL2LinearMap_vacuum_eq_openHalfConstantOneL2 hInvariant U n
  let Fc := Pn.vacuumCenteredCarrier F
  have hFcImage : Q.positiveHalfL2LinearMap hInvariant n Fc =
      Aout - Pn.omega F.toGaugeInvariant • one := by
    change Q.positiveHalfL2LinearMap hInvariant n
      (F - Pn.omega F.toGaugeInvariant • Pn.vacuumObservable) = _
    rw [map_sub, map_smul, hFimage, hVacImage]
  have hFcSynthesisPos : 0 < inner ℝ
      (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta n
        (Q.positiveHalfL2LinearMap hInvariant n Fc))
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
        (halfExtent n) (beta n) (hbeta n) k c) := by
    change 0 < inner ℝ
      (periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
        (halfExtent n) 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive
        (beta n) (hbeta n) (Q.positiveHalfL2LinearMap hInvariant n Fc))
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
        (halfExtent n) (beta n) (hbeta n) k c)
    rw [periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator_inner]
    change 0 < inner ℝ (Q.positiveHalfL2LinearMap hInvariant n Fc) Aout
    rw [hFcImage, inner_sub_left, inner_smul_left, hAoutCentered]
    simp only [mul_zero, sub_zero]
    rw [real_inner_self_eq_norm_sq]
    have hnorm : 0 < ‖Aout‖ := norm_pos_iff.mpr hAoutNe
    nlinarith
  have hBoundaryNe :
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n Fc ≠ 0 := by
    rw [physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis]
    change physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
      halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta n
      (Q.positiveHalfL2LinearMap hInvariant n Fc) ≠ 0
    intro hzeroBoundary
    rw [hzeroBoundary] at hFcSynthesisPos
    simpa using hFcSynthesisPos
  have hBoundaryNormPos : 0 < ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
      S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n Fc‖ :=
    norm_pos_iff.mpr hBoundaryNe
  have hFcNormPos : 0 < ‖Fc‖ := by
    rw [physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_norm
      S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n Fc] at hBoundaryNormPos
    exact hBoundaryNormPos
  have hFcQuadraticPos : 0 < Pn.osQuadraticValue Fc := by
    rw [Pn.osQuadraticValue_eq_norm_sq]
    nlinarith
  have hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  refine ⟨Pn.centeredPhysicalExcitation hPn F, ?_⟩
  apply Pn.centeredPhysicalExcitation_ne_zero_of_osQuadraticValue_pos hPn F
  simpa [Fc] using hFcQuadraticPos

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
