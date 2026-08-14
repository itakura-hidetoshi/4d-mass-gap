import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonActualAnalysisNonzeroCriterion
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryMarginalVacuumNormalization
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentSeparationCompletion
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalCore
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
