import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonActualAnalysisNonzeroCriterion
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryMarginalVacuumNormalization
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentSeparationCompletion
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalCore
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

/-- Under the already-isolated vacuum-unit compatibility, the completed OS
boundary realization sends the normalized finite Wilson vacuum to the concrete
boundary-Haar square-root-density vacuum used by the actual rectangular Wilson
analysis.

This is a kinematic identification only.  It adds no mass, decay, coercivity,
projective, determinant, or spectral assumption. -/
theorem physicalHilbertBoundaryMomentLinearIsometry_vacuum_eq_boundaryVacuumHaarL2
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n
    Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n Pn.vacuum =
      periodicHypercubicEvenBoundaryVacuumHaarL2
        (halfExtent n) (beta n) (hbeta n) := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  change Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
      (Pn.physicalState Pn.vacuumObservable) = _
  rw [Q.physicalHilbertBoundaryMomentLinearIsometry_physicalState]
  apply Lp.ext
  filter_upwards [
    U.canonicalBoundaryMomentL2_vacuum_coeFn n,
    periodicHypercubicEvenBoundaryVacuumHaarL2_coeFn
      (halfExtent n) (beta n) (hbeta n)] with b hcanonical hvacuum
  exact hcanonical.trans hvacuum.symm

/-- The coherent positive-half `L²` realization carries the OS vacuum observable
to the same constant-one vector which appears in the concrete actual-analysis
vacuum-orthogonality theorem. -/
theorem positiveHalfL2LinearMap_vacuum_eq_openHalfConstantOneL2
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n
    Q.positiveHalfL2LinearMap hInvariant n Pn.vacuumObservable =
      periodicHypercubicEvenOpenHalfConstantOneL2 (halfExtent n) 2 := by
  dsimp only
  change
    physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
        S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
          Q.toWeakStarBridge hInvariant n).vacuumObservable) = _
  unfold physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
  rw [U.finitePositiveHalfObservable_vacuum_eq_one n]
  rfl

/-- The #1669 centered/nonzero actual-analysis output itself produces a genuine
nonzero reconstructed OS excitation as soon as that *output* lies in the range
of the already-existing coherent positive-half realization.

This is the natural realization condition used by the preceding normal-output
physical-range layer.  It is strictly upstream of asking the weighted boundary
input itself to be in the completed boundary-moment range.

The proof vacuum-centers an actual carrier preimage `F`.  Its positive-half image
is `A f - a • 1` for the scalar vacuum expectation `a`.  Since #1669 proves
`A f ≠ 0` and `A f ⟂ 1`, this difference cannot vanish for any `a`.  Thus the
centered carrier is nonzero; the canonical OS completion is isometric, and the
existing centered-carrier theorem places the resulting nonzero state in
`VacuumOrthogonalHilbert`.

No static `A† A` operator is identified with Euclidean time translation. -/
theorem normalizedTracePolynomial_exists_nonzero_vacuumOrthogonalPhysicalState_of_analysisImage_range_of_factorized_inner_self_pos
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hzero :
      inner ℝ
        (periodicHypercubicEvenBoundaryMarginalVacuumL2
          (halfExtent n) (beta n) (hbeta n))
        (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
          (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hpos :
      0 < inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          (halfExtent n) 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive
          (beta n) (hbeta n)
          (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
            (halfExtent n) (beta n) (hbeta n) k c))
        (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
          (halfExtent n) (beta n) (hbeta n) k c))
    (hAnalysisRange :
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          (halfExtent n) 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive
          (beta n) (hbeta n)
          (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
            (halfExtent n) (beta n) (hbeta n) k c) ∈
        (Q.positiveHalfL2LinearMap hInvariant n).range) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n
    ∃ psi : Pn.VacuumOrthogonalHilbert, psi ≠ 0 := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  let Aout :=
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
      (halfExtent n) 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive
      (beta n) (hbeta n)
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
  have hVacImage :
      Q.positiveHalfL2LinearMap hInvariant n Pn.vacuumObservable = one := by
    simpa [Pn, one] using
      Q.positiveHalfL2LinearMap_vacuum_eq_openHalfConstantOneL2 hInvariant U n
  let Fc := Pn.vacuumCenteredCarrier F
  have hFcImage :
      Q.positiveHalfL2LinearMap hInvariant n Fc =
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
      rw [hscalar, inner_smul_left, hAoutCentered]
      simp
    exact hAoutNe (inner_self_eq_zero.mp hself)
  have hFcNe : Fc ≠ 0 := by
    intro hzeroFc
    apply hFcImageNe
    rw [hzeroFc, map_zero]
  have hPhysicalNe : Pn.physicalState Fc ≠ 0 := by
    intro hzeroPhysical
    apply hFcNe
    apply norm_eq_zero.mp
    calc
      ‖Fc‖ = ‖Pn.physicalState Fc‖ := (Pn.norm_physicalState Fc).symm
      _ = 0 := by rw [hzeroPhysical, norm_zero]
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

/-- The finite actual-Wilson strict polynomial witness lifts to a genuine
nonzero vacuum-orthogonal vector in the already-constructed completed OS
physical Hilbert space as soon as that same boundary-Haar mode lies in the
range of the canonical completed boundary realization.

The static factorized operator `A† A` is used only to prove nonvanishing of the
actual Wilson mode.  It is not identified with Euclidean time evolution.  The
only realization input is range membership in the pre-existing completed OS
boundary isometry; no duplicate Hilbert carrier is introduced. -/
theorem normalizedTracePolynomial_exists_nonzero_vacuumOrthogonalPhysicalState_of_boundaryMoment_range_of_factorized_inner_self_pos
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hzero :
      inner ℝ
        (periodicHypercubicEvenBoundaryMarginalVacuumL2
          (halfExtent n) (beta n) (hbeta n))
        (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
          (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hpos :
      0 < inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          (halfExtent n) 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive
          (beta n) (hbeta n)
          (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
            (halfExtent n) (beta n) (hbeta n) k c))
        (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
          (halfExtent n) (beta n) (hbeta n) k c))
    (hRange :
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
          (halfExtent n) (beta n) (hbeta n) k c ∈
        (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n).toLinearMap.range) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n
    ∃ psi : Pn.VacuumOrthogonalHilbert,
      psi ≠ 0 ∧
        Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
            (psi : Pn.PhysicalHilbert) =
          periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
            (halfExtent n) (beta n) (hbeta n) k c := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  let J := Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
  let f := periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
    (halfExtent n) (beta n) (hbeta n) k c
  change f ∈ J.toLinearMap.range at hRange
  rcases hRange with ⟨psi, hpsi⟩
  have hpsiJ : J psi = f := by
    simpa [J] using hpsi
  have hAnalysisNe :
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          (halfExtent n) 2 actualAnalysisStrictPhysicalExcitationTwoRankPositive
          (beta n) (hbeta n) f ≠ 0 := by
    simpa [f] using
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_apply_ne_zero_of_factorized_inner_self_pos
        (beta n) (hbeta n) f (by simpa [f] using hpos)
  have hf : f ≠ 0 := by
    intro hf
    apply hAnalysisNe
    simp [hf]
  have hboundaryCentered :
      inner ℝ
        (periodicHypercubicEvenBoundaryVacuumHaarL2
          (halfExtent n) (beta n) (hbeta n)) f = 0 := by
    simpa [f] using
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2_centered
        (halfExtent n) (beta n) (hbeta n) k c hzero
  have hJvacuum :
      J Pn.vacuum =
        periodicHypercubicEvenBoundaryVacuumHaarL2
          (halfExtent n) (beta n) (hbeta n) := by
    simpa [J, Pn] using
      Q.physicalHilbertBoundaryMomentLinearIsometry_vacuum_eq_boundaryVacuumHaarL2
        hInvariant U n
  have horth : inner ℝ Pn.vacuum psi = 0 := by
    calc
      inner ℝ Pn.vacuum psi = inner ℝ (J Pn.vacuum) (J psi) :=
        (J.inner_map_map Pn.vacuum psi).symm
      _ = inner ℝ
          (periodicHypercubicEvenBoundaryVacuumHaarL2
            (halfExtent n) (beta n) (hbeta n)) f := by
        rw [hJvacuum, hpsiJ]
      _ = 0 := hboundaryCentered
  have hpsiNe : psi ≠ 0 := by
    intro hzeroPsi
    apply hf
    calc
      f = J psi := hpsiJ.symm
      _ = J 0 := by rw [hzeroPsi]
      _ = 0 := by simp
  let psiOrth : Pn.VacuumOrthogonalHilbert :=
    ⟨psi, (Pn.mem_vacuumOrthogonal_iff psi).2 horth⟩
  refine ⟨psiOrth, ?_, ?_⟩
  · intro hzeroPsiOrth
    apply hpsiNe
    exact congrArg Subtype.val hzeroPsiOrth
  · change J psi = f
    exact hpsiJ

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
