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

The carrier preimage is vacuum-centered before completion.  Its positive-half
image has the form `A f - a • 1`.  Since #1669 gives both `A f ≠ 0` and
`A f ⟂ 1`, this vector is nonzero for every scalar `a`; hence the centered
carrier and its isometric physical completion are nonzero.  No static `A† A`
operator is identified with Euclidean time evolution. -/
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
  have hFcImageNe : Q.positiveHalfL2LinearMap hInvariant n Fc ≠ 0 := by
    intro hzeroImage
    have hdiff : Aout - Pn.omega F.toGaugeInvariant • one = 0 := by
      rw [← hFcImage, hzeroImage]
    have hscalar : Aout = Pn.omega F.toGaugeInvariant • one := sub_eq_zero.mp hdiff
    have hself : inner ℝ Aout Aout = 0 := by
      calc
        inner ℝ Aout Aout =
            inner ℝ (Pn.omega F.toGaugeInvariant • one) Aout :=
          congrArg (fun x => inner ℝ x Aout) hscalar
        _ = Pn.omega F.toGaugeInvariant * inner ℝ one Aout := by
          rw [inner_smul_left]
        _ = 0 := by rw [hAoutCentered, mul_zero]
    exact hAoutNe (inner_self_eq_zero.mp hself)
  have hFcNe : Fc ≠ 0 := by
    intro hzeroFc
    apply hFcImageNe
    rw [hzeroFc, map_zero]
  have hPhysicalNe : Pn.physicalState Fc ≠ 0 := by
    intro hzeroPhysical
    have hnorm : ‖Fc‖ = 0 := by
      calc
        ‖Fc‖ = ‖Pn.physicalState Fc‖ := (Pn.norm_physicalState Fc).symm
        _ = 0 := by rw [hzeroPhysical, norm_zero]
    have hFcZero : Fc = 0 :=
      (norm_eq_zero : ‖Fc‖ = 0 ↔ Fc = 0).mp hnorm
    exact hFcNe hFcZero
  have hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  let psi : Pn.VacuumOrthogonalHilbert :=
    ⟨Pn.physicalState Fc,
      Pn.physicalState_vacuumCenteredCarrier_mem_vacuumOrthogonal hPn F⟩
  refine ⟨psi, ?_⟩
  intro hzeroPsi
  apply hPhysicalNe
  exact congrArg Subtype.val hzeroPsi

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
