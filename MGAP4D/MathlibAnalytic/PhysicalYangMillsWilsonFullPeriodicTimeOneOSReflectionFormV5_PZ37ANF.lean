import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicPositiveClosureCommonL2ZeroClassesV5_PZ37ANE
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveBoundedMeasurableWilsonGibbsReflectionPositivity
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANF — real original Wilson OS reflection form of the exact time-one cylinder

ANE supplies actual nonzero real L2 classes for the unaltered original
time-one two-mode Wilson observable, under both the genuine normalized
full-periodic Gibbs positive-closure marginal and the original product Haar.
Nonzero ordinary L2 does NOT imply positive OS reflection seminorm.

This leaf admits THAT SAME literal time-one cylinder in the existing
boundary-positive reflection-form domain, without dropping its shared
reflection-fixed boundary.  It proves the real original full-periodic Wilson
Gibbs OS quadratic form is nonnegative and identifies it, via the exact
boundary-conditioned finite Wilson Gram kernel, with the boundary integral of
the squared finite Wilson Gram moment.

Strict positivity requires a NONZERO boundary Gram moment and is NOT inferred
from ordinary L2 nonzero.  No new Hamiltonian, mass gap, Hilbert quotient
identification, one-slab intertwining or conditional transfer axiom is added.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANF_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37ANF_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANF_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANF_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANF_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANF_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

/-- Same literal ANC/AND/ANE two-mode Wilson time-one observable, now typed as
an element of the REAL finite Wilson OS boundary-positive test domain. -/
noncomputable def p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable
    (H : ℕ) (c0 c1 : ℝ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H 2 → ℝ :=
  p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable H c0 c1

theorem p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable_measurable
    (H : ℕ) (c0 c1 : ℝ) :
    Measurable (p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable H c0 c1) := by
  simpa [p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable] using
    p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable_measurable H c0 c1

/-- Exactly the original SU(2) two-mode sup bound; no interaction-dependent
or volume-uniform operator norm is asserted. -/
theorem p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable_norm_le
    (H : ℕ) (c0 c1 : ℝ)
    (z : PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H 2) :
    ‖p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable H c0 c1 z‖ ≤
      |c0| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0‖ +
      |c1| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1‖ := by
  simpa [p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable] using
    p4Q2PZ37AND_timeOnePositiveClosureObservable_norm_le H c0 c1 z

/-- The original Gibbs OS quadratic form of this exact positive-time
cylinder, including the actual full-configuration Euclidean reflection. -/
noncomputable def p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) : ℝ :=
  ∫ A,
    periodicHypercubicEvenBoundaryPositiveFullReflectedObservable H
      (p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable H c0 c1) A
    ∂(periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) 2 (by norm_num) beta hbeta).gibbsMeasure

/-- Direct unconditional nonnegativity for the exact original time-one
Wilson cylinder in the TRUE full-periodic interacting Gibbs OS form. -/
theorem p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic_nonneg
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) :
    0 ≤ p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic
      H beta hbeta c0 c1 := by
  let f := p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable H c0 c1
  let M := |c0| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0‖ +
    |c1| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1‖
  have hf : Measurable f :=
    p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable_measurable H c0 c1
  have hM : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg
      (mul_nonneg (abs_nonneg _) (norm_nonneg _))
      (mul_nonneg (abs_nonneg _) (norm_nonneg _))
  have hBound : ∀ z, ‖f z‖ ≤ M := by
    intro z
    exact p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable_norm_le
      H c0 c1 z
  unfold p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic
  exact periodicHypercubicEvenBoundaryPositiveWilsonGibbs_reflectionPositive_boundedMeasurable
    H 2 (by norm_num) beta hbeta f hf M hM hBound

/-- The exact original boundary-conditioned Wilson Gram moment of THIS
specific positive-time two-mode cylinder, retaining the boundary dependence. -/
noncomputable def p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) : ℝ :=
  ∫ x,
    periodicHypercubicEvenBoundaryObservableGramFeature
      H 2 (by norm_num) beta hbeta
        (fun x => p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable H c0 c1 (b, x))
      b x ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)

/-- Exact ORIGINAL Gibbs reflection form = boundary Haar integral of squares
of the explicit boundary-conditioned Wilson Gram moments.

This identifies the remaining kernel obstruction *without* falsely
asserting that ordinary a.e.-nonzero implies OS-nonzero. -/
theorem p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic_eq_boundaryGramMoment_sq
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) :
    p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic H beta hbeta c0 c1 =
      ∫ b, ‖p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
        H beta hbeta c0 c1 b‖ ^ 2
      ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  let f := p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable H c0 c1
  let M := |c0| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0‖ +
    |c1| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1‖
  have hf : Measurable f :=
    p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable_measurable H c0 c1
  have hM : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg
      (mul_nonneg (abs_nonneg _) (norm_nonneg _))
      (mul_nonneg (abs_nonneg _) (norm_nonneg _))
  have hBound : ∀ z, ‖f z‖ ≤ M := by
    intro z
    exact p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable_norm_le
      H c0 c1 z
  have hTransport :=
    periodicHypercubicEvenBoundaryPositiveWilsonGibbs_reflectedObservable_integral_eq_boundaryIntegral_of_measurable_of_bound
      H 2 (by norm_num) beta hbeta f hf M hM hBound
  change
    (∫ A,
      periodicHypercubicEvenBoundaryPositiveFullReflectedObservable H f A
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) 2 (by norm_num) beta hbeta).gibbsMeasure) =
      ∫ b, ‖p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
        H beta hbeta c0 c1 b‖ ^ 2
      ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2)
  rw [hTransport]
  apply integral_congr_ae
  filter_upwards [] with b
  let fb : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 → ℝ :=
    fun x => f (b, x)
  have hGram : Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        H 2 (by norm_num) beta hbeta fb b)
      (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
    simpa [fb] using
      periodicHypercubicEvenBoundaryPositiveObservableGramFeature_integrable_of_measurable_of_bound
        H 2 (by norm_num) beta hbeta f hf M hM hBound b
  calc
    (∫ x, ∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H 2 (by norm_num) beta hbeta (b, (x, y))).toReal *
        (f (b, x) *
          f (b, periodicHypercubicEvenOpenHalfOrientationCorrection H y))
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)) =
        ∫ x, ∫ y,
          (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
            H 2 (by norm_num) beta hbeta
              (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal *
            (fb x * fb y)
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simpa [fb] using
          (periodicHypercubicEvenBoundaryObservable_corrected_innerIntegral_eq_original
            H 2 (by norm_num) beta hbeta fb b x).symm
    _ = ‖∫ x,
        periodicHypercubicEvenBoundaryObservableGramFeature
          H 2 (by norm_num) beta hbeta fb b x
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)‖ ^ 2 := by
      exact periodicHypercubicEvenBoundaryObservable_corrected_iteratedIntegral_eq_norm_sq
        H 2 (by norm_num) beta hbeta fb b hGram
    _ = ‖p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
      H beta hbeta c0 c1 b‖ ^ 2 := by
      rfl

/-- Concrete sufficient condition for a NONZERO OS class.  ANF does not
prove the premise: the required strict boundary-Gram-moment integral is the
explicit analytic obstruction that remains after ANE. -/
theorem p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic_pos_of_boundaryMoment
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ)
    (hMoment :
      0 < ∫ b, ‖p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
        H beta hbeta c0 c1 b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2)) :
    0 < p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic
      H beta hbeta c0 c1 := by
  rw [p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic_eq_boundaryGramMoment_sq]
  exact hMoment

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable_measurable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable_norm_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic_nonneg
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic_eq_boundaryGramMoment_sq
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic_pos_of_boundaryMoment
