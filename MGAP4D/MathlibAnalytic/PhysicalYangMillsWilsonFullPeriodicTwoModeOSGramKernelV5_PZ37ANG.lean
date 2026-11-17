import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicTimeOneOSReflectionFormV5_PZ37ANF
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANG — exact two-mode boundary Gram-moment cancellation criterion

ANF identifies the ORIGINAL full-periodic SU(2) Wilson OS quadratic form
with a boundary Haar integral of Gram-moment squares.  This leaf resolves
the algebraic two-mode part of that obstruction, with the EXACT unchanged
ANC time-one observable and Wilson kernel.

Its two coefficient modes are not silently identified with vectors in
the completed OS Hilbert quotient.  This file does not assert that any
nonzero top-orthogonal coefficient pair has a nonzero boundary moment.
Strict positivity is a separate analytic obligation.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANG_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37ANG_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANG_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANG_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANG_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANG_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

/-- The same literal time-one observable is linear in the TWO original
SU(2) Gram--Schmidt mode coefficients, pointwise on the actual closure. -/
theorem p4Q2PZ37ANG_originalTimeOneObservable_twoMode_linear
    (H : ℕ) (c0 c1 : ℝ)
    (z : PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H 2) :
    p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable H c0 c1 z =
      c0 * p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable H 1 0 z +
      c1 * p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable H 0 1 z := by
  simp [p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable,
    p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable,
    p4Q2PZ37ANA_timeOneTwoModeWilsonObservable]

/-- Integrability of each boundary-fibered Gram feature for arbitrary
real coefficients, using only ANF's unchanged measurable bound. -/
theorem p4Q2PZ37ANG_originalTimeOneBoundaryGramFeature_integrable
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        H 2 (by norm_num) beta hbeta
          (fun x => p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable
            H c0 c1 (b, x)) b)
      (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
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
    exact p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable_norm_le H c0 c1 z
  simpa [f] using
    periodicHypercubicEvenBoundaryPositiveObservableGramFeature_integrable_of_measurable_of_bound
      H 2 (by norm_num) beta hbeta f hf M hM hBound b

/-- EXACT linearity of the original time-one Wilson boundary Gram moment
for the two specific, unmodified continuous Wilson modes. -/
theorem p4Q2PZ37ANG_originalTimeOneBoundaryGramMoment_twoMode_linear
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment H beta hbeta c0 c1 b =
      c0 * p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
        H beta hbeta 1 0 b +
      c1 * p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
        H beta hbeta 0 1 b := by
  let W := periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
    H 2 (by norm_num) beta hbeta b
  let f := p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable H
  let mu := periodicHypercubicEvenOpenHalfHaarMeasure H 2
  have h0 : Integrable (fun x => W x * f 1 0 (b, x)) mu := by
    simpa [W, f, mu, periodicHypercubicEvenBoundaryObservableGramFeature] using
      p4Q2PZ37ANG_originalTimeOneBoundaryGramFeature_integrable
        H beta hbeta 1 0 b
  have h1 : Integrable (fun x => W x * f 0 1 (b, x)) mu := by
    simpa [W, f, mu, periodicHypercubicEvenBoundaryObservableGramFeature] using
      p4Q2PZ37ANG_originalTimeOneBoundaryGramFeature_integrable
        H beta hbeta 0 1 b
  change (∫ x, W x * f c0 c1 (b, x) ∂mu) =
    c0 * (∫ x, W x * f 1 0 (b, x) ∂mu) +
    c1 * (∫ x, W x * f 0 1 (b, x) ∂mu)
  have hFun :
      (fun x => W x * f c0 c1 (b, x)) =
        (fun x => c0 * (W x * f 1 0 (b, x)) +
          c1 * (W x * f 0 1 (b, x))) := by
    funext x
    rw [show f c0 c1 (b, x) =
      c0 * f 1 0 (b, x) + c1 * f 0 1 (b, x) from
        p4Q2PZ37ANG_originalTimeOneObservable_twoMode_linear H c0 c1 (b, x)]
    ring
  rw [hFun]
  rw [integral_add (h0.const_mul c0) (h1.const_mul c1)]
  simp only [integral_const_mul]

/-- The true full-periodic Wilson OS form equals the squared boundary norm
of the exact TWO fixed Wilson mode moments and their original coefficients.
No positivity stronger than ANF is claimed. -/
theorem p4Q2PZ37ANG_originalTimeOneWilsonOSQuadratic_eq_twoModeMoment_sq
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) :
    p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic H beta hbeta c0 c1 =
      ∫ b, ‖c0 * p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
          H beta hbeta 1 0 b +
        c1 * p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
          H beta hbeta 0 1 b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  rw [p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic_eq_boundaryGramMoment_sq]
  apply integral_congr_ae
  filter_upwards [] with b
  rw [p4Q2PZ37ANG_originalTimeOneBoundaryGramMoment_twoMode_linear]

/-- A concrete boundary-moment cancellation is an obstruction to OS
strict positivity for this *actual* two-mode cylinder.  The premise is
NOT supplied by ordinary nonzero Gibbs or Haar L2. -/
theorem p4Q2PZ37ANG_originalTimeOneWilsonOSQuadratic_zero_of_modeCancellation
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ)
    (hCancel : ∀ᵐ b ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2),
      c0 * p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
        H beta hbeta 1 0 b +
      c1 * p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
        H beta hbeta 0 1 b = 0) :
    p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic H beta hbeta c0 c1 = 0 := by
  rw [p4Q2PZ37ANG_originalTimeOneWilsonOSQuadratic_eq_twoModeMoment_sq]
  have hZero :
      (fun b => ‖c0 * p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
        H beta hbeta 1 0 b +
      c1 * p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
        H beta hbeta 0 1 b‖ ^ 2) =ᵐ[
        periodicHypercubicEvenBoundaryHaarMeasure H 2]
        (fun _ => (0 : ℝ)) := by
    filter_upwards [hCancel] with b hb
    simp [hb]
  exact (integral_congr_ae hZero).trans (by simp)

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANG_originalTimeOneObservable_twoMode_linear
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANG_originalTimeOneBoundaryGramFeature_integrable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANG_originalTimeOneBoundaryGramMoment_twoMode_linear
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANG_originalTimeOneWilsonOSQuadratic_eq_twoModeMoment_sq
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANG_originalTimeOneWilsonOSQuadratic_zero_of_modeCancellation
