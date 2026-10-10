import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarTopSpectralGeometricRayleigh
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# P4-Q2-AA2: actual original Wilson Gram all-one geometric Rayleigh bound

The previously verified TRUE frozen Wilson original-link signed posterior
Gram is EXACTLY the squared ℓ² norm of the all-link innovations summed
along the genuine positive-fine Wilson Krylov family. Combine this with
P4-Q2-AA depth-UNIFORM geometric error and a nonnegative margin to prove
  ((r+1)‖I_frozen(P_fine u_H)‖ - C/(1-q))²
     <= onesᵀ G_original(r) ones.
This uses neither a surrogate posterior nor an unproved frame/continuum
mass-gap statement. The next step is a depth-linear lower bound on the
normalized original all-one Rayleigh when the true projected innovation
is nonzero (the latter was established on a positive fine window in Z2).
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 850000

local instance p4AA2Group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4AA2Compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4AA2SecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4AA2Measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4AA2Borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4AA2LinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4AA2RealHilbertComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- Exact all-one original Wilson frozen posterior right-Gram Rayleigh:
its genuine signed full-link Hilbert receiver has precisely the same
squared norm as the original posterior Gram quadratic form. -/
theorem fineRightKrylovPairHaarResidualGram_ones_eq_fullLinkInnovationSum_sq
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) :
    let H := halfExtent (n + 1)
    let I := physicalOriginalReceiverPosteriorInnovation H 2
      specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let V (j : Fin (r + 1)) :=
      WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
        I e (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ)))
    star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
      (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)
        (fun _ : Fin (r + 1) => (1 : ℝ))) =
      ‖∑ j : Fin (r + 1), V j‖ ^ 2 := by
  classical
  let H := halfExtent (n + 1)
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let R : Fin (r + 1) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    fun j => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ)
  let V (j : Fin (r + 1)) :=
    WithLp.toLp 2 (fun e : Link => I e (R j))
  have hCoordSumFinset (s : Finset (Fin (r + 1))) (e : Link) :
      (∑ j ∈ s, V j) e = ∑ j ∈ s, I e (R j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
        simp only [Finset.sum_insert hj, PiLp.add_apply]
        rw [ih]
  have hCoordSum (e : Link) :
      (∑ j : Fin (r + 1), V j) e =
        ∑ j : Fin (r + 1), I e (R j) := by
    exact hCoordSumFinset Finset.univ e
  have hDirectSumIdentity :
      ‖∑ j : Fin (r + 1), V j‖ ^ 2 =
        ∑ e : Link, ‖∑ j : Fin (r + 1), I e (R j)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [hCoordSum]
  change star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
      (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)
        (fun _ : Fin (r + 1) => (1 : ℝ))) =
      ‖∑ j : Fin (r + 1), V j‖ ^ 2
  rw [hDirectSumIdentity]
  simpa only [one_smul, I, R, physicalOriginalReceiverPosteriorInnovation] using
    (fineRightKrylovPairHaarResidualGram_rayleigh
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r (fun _ : Fin (r + 1) => (1 : ℝ)))

/-- The actual ORIGINAL full-link Wilson Gram lower bound is quadratic
in the depth-linear top-component signal, minus a DEPTH-INDEPENDENT
genuine geometric error C/(1-q). A nonnegative margin is required
before squaring the reverse-triangle inequality. -/
theorem fineRightKrylovPairHaarResidualGram_ones_rayleigh_ge_topGeometricMargin
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ)
    (hMargin :
      let H := halfExtent (n+1)
      let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
      let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
      let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
      let I := physicalOriginalReceiverPosteriorInnovation
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
      let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
      let B := physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n+1))
      let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
      let C := (Real.sqrt gamma * B) * Real.sqrt L + Real.sqrt gamma * Real.sqrt L
      let U := WithLp.toLp 2
        (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e (P u))
      0 ≤ (((r+1:ℕ):ℝ) * ‖U‖) - C/(1-‖S-P‖)) :
    let H := halfExtent (n+1)
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
    let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
    let I := physicalOriginalReceiverPosteriorInnovation
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let B := physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n+1))
    let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
    let C := (Real.sqrt gamma * B) * Real.sqrt L + Real.sqrt gamma * Real.sqrt L
    let U := WithLp.toLp 2
      (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e (P u))
    ((((r+1:ℕ):ℝ) * ‖U‖) - C/(1-‖S-P‖)) ^ 2 ≤
      star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)
          (fun _ : Fin (r + 1) => (1 : ℝ))) := by
  classical
  let H := halfExtent (n+1)
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let B := physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n+1))
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  let C := (Real.sqrt gamma * B) * Real.sqrt L + Real.sqrt gamma * Real.sqrt L
  let U := WithLp.toLp 2
    (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e (P u))
  let V (j : Fin (r+1)) := WithLp.toLp 2
    (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
      I e (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (j:ℕ)))
  let N : ℝ := ((r+1:ℕ):ℝ)
  let E : ℝ := C / (1 - ‖S-P‖)
  let m : ℝ := N * ‖U‖ - E
  change 0 ≤ m at hMargin
  have hLower : m ≤ ‖∑ j : Fin (r+1), V j‖ := by
    exact fineRightKrylov_originalPosteriorFullLink_sum_norm_lower_geometric
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have hProduct :
      0 ≤ (‖∑ j : Fin (r+1), V j‖ - m) *
        (‖∑ j : Fin (r+1), V j‖ + m) :=
    mul_nonneg (sub_nonneg.mpr hLower)
      (add_nonneg (norm_nonneg _) hMargin)
  have hSquare : m ^ 2 ≤ ‖∑ j : Fin (r+1), V j‖ ^ 2 := by
    nlinarith [hProduct]
  have hGram :=
    fineRightKrylovPairHaarResidualGram_ones_eq_fullLinkInnovationSum_sq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  change m ^ 2 ≤ star (fun _ : Fin (r+1) => (1:ℝ)) ⬝ᵥ
    (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)
      (fun _ : Fin (r+1) => (1:ℝ)))
  rw [hGram]
  exact hSquare

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
