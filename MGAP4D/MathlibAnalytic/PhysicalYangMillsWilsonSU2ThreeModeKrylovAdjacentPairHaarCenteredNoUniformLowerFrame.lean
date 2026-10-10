import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarCenteredGeometricUpperFrame
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# P4-Q2-AC: authentic Wilson centered Krylov lower-frame obstruction

For the genuine physical normalized fine Wilson transfer and ORIGINAL
frozen posterior innovation, P4-Q2-AA established, for every depth j:
  ‖V_j-U‖ ≤ C q^j,   0 ≤ q < 1.

Choose the centered coefficient vector supported at deep adjacent
Krylov indices r and r+1, with coefficients +1 and -1.
Its coefficient sum is zero and its squared Euclidean norm is 2.
Its genuine original posterior Gram Rayleigh is exactly
  ‖V_r-V_(r+1)‖² ≤ C² (1+q)² q^(2r) → 0.

Therefore there is NO strictly positive lower coefficient-l2
coercivity constant independent of Krylov depth even on the centered
coefficient hyperplane. This is a specific *representation-level*
obstruction, not a claim against the physical Yang--Mills mass gap
or centered semigroup coercivity on a different Hilbert carrier.

All physical operators/laws are unchanged; no Dobrushin, surrogate,
new axiom, sorry, admit, or unproved volume-uniform coefficient.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 850000

/-- The two actual last adjacent positions of the finite Krylov family. -/
def p4Q2AC_adjacentLow (r : ℕ) : Fin (r+2) := ⟨r, by omega⟩
def p4Q2AC_adjacentHigh (r : ℕ) : Fin (r+2) := ⟨r+1, by omega⟩

theorem p4Q2AC_adjacentLow_ne_high (r : ℕ) :
    p4Q2AC_adjacentLow r ≠ p4Q2AC_adjacentHigh r := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [p4Q2AC_adjacentLow, p4Q2AC_adjacentHigh] at hv
  omega

/-- The centered two-spike coefficient (+1 at r, -1 at r+1). -/
def p4Q2AC_adjacentCoeff (r : ℕ) (j : Fin (r+2)) : ℝ :=
  (if j = p4Q2AC_adjacentLow r then 1 else 0) -
    (if j = p4Q2AC_adjacentHigh r then 1 else 0)

/-- Exactly centered, with no asymptotic approximation. -/
theorem p4Q2AC_adjacentCoeff_sum_zero (r : ℕ) :
    (∑ j : Fin (r+2), p4Q2AC_adjacentCoeff r j) = 0 := by
  classical
  simp [p4Q2AC_adjacentCoeff, Finset.sum_sub_distrib]

/-- The coefficient ℓ² norm is exactly sqrt(2), independent of depth. -/
theorem p4Q2AC_adjacentCoeff_sum_sq_two (r : ℕ) :
    (∑ j : Fin (r+2), (p4Q2AC_adjacentCoeff r j)^2) = 2 := by
  classical
  let lo := p4Q2AC_adjacentLow r
  let hi := p4Q2AC_adjacentHigh r
  have hne : lo ≠ hi := p4Q2AC_adjacentLow_ne_high r
  have hs (j : Fin (r+2)) :
      (p4Q2AC_adjacentCoeff r j)^2 =
        (if j = lo then (1 : ℝ) else 0) +
          (if j = hi then (1 : ℝ) else 0) := by
    by_cases hlo : j = lo
    · subst j
      simp [p4Q2AC_adjacentCoeff, lo, hi, hne]
    · by_cases hhi : j = hi
      · subst j
        simp [p4Q2AC_adjacentCoeff, lo, hi, hlo]
      · simp [p4Q2AC_adjacentCoeff, lo, hi, hlo, hhi]
  calc
    (∑ j : Fin (r+2), (p4Q2AC_adjacentCoeff r j)^2) =
        ∑ j : Fin (r+2),
          ((if j = lo then (1 : ℝ) else 0) +
            (if j = hi then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact hs j
    _ = 2 := by
      rw [Finset.sum_add_distrib]
      simp
      norm_num

/-- The TRUE signed linear combination with these coefficients is just
the difference of the two adjacent physical innovations. -/
theorem p4Q2AC_adjacentCoeff_weighted_sum
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : ℕ) (v : ℕ → E) :
    (∑ j : Fin (r+2), p4Q2AC_adjacentCoeff r j • v (j : ℕ)) =
      v r - v (r+1) := by
  classical
  simp only [p4Q2AC_adjacentCoeff, sub_smul, Finset.sum_sub_distrib]
  simp [p4Q2AC_adjacentLow, p4Q2AC_adjacentHigh]

/-- The authentic geometric error gives an exponentially vanishing
norm for any adjacent mode difference, with no sign assumption on
the frozen innovation or any Gram cross entry. -/
theorem p4Q2AC_adjacent_difference_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℕ → E) (u : E) (q C : ℝ)
    (hNear : ∀ j : ℕ, ‖v j-u‖ ≤ C*q^j)
    (r : ℕ) :
    ‖v r-v (r+1)‖ ≤ C*(q^r+q^(r+1)) := by
  calc
    ‖v r-v (r+1)‖ =
        ‖(v r-u)-(v (r+1)-u)‖ := by
      congr 1
      abel
    _ ≤ ‖v r-u‖+‖v (r+1)-u‖ := norm_sub_le _ _
    _ ≤ C*q^r+C*q^(r+1) := add_le_add (hNear r) (hNear (r+1))
    _ = C*(q^r+q^(r+1)) := by ring

/-- The physical adjacent geometric upper budget (and its square)
converges to zero. Exact finite-H q is fixed while depth varies. -/
theorem p4Q2AC_adjacent_geometric_square_tendsto_zero
    (q C : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun r : ℕ => (C*(q^r+q^(r+1)))^2) atTop (nhds 0) := by
  have hpow : Tendsto (fun r : ℕ => q^r) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hmul : Tendsto (fun r : ℕ => (C*(1+q))*q^r) atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hpow :
      Tendsto (fun r : ℕ => (C*(1+q))*q^r) atTop (nhds ((C*(1+q))*0)))
  have hsq := hmul.pow 2
  convert hsq using 1
  · funext r
    rw [pow_succ]
    ring
  · norm_num

/-- Any real normed family with fixed top signal and exponentially
decaying excited remainder cannot have a positive coefficient lower
frame uniformly over all depths, even after imposing sum a_j=0. -/
theorem p4Q2AC_generic_centered_no_depth_uniform_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℕ → E) (u : E) (q C : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hC : 0 ≤ C)
    (hNear : ∀ j : ℕ, ‖v j-u‖ ≤ C*q^j) :
    ¬ ∃ κ : ℝ, 0 < κ ∧
      ∀ (m : ℕ) (a : Fin (m+1) → ℝ),
        (∑ j : Fin (m+1), a j) = 0 →
        κ*(∑ j : Fin (m+1), (a j)^2) ≤
          ‖∑ j : Fin (m+1), a j • v (j:ℕ)‖^2 := by
  rintro ⟨κ, hκ, hLower⟩
  have hlim := p4Q2AC_adjacent_geometric_square_tendsto_zero q C hq0 hq1
  have hsmall :
      ∀ᶠ r : ℕ in atTop, (C*(q^r+q^(r+1)))^2 < 2*κ :=
    hlim.eventually_lt_const (by linarith)
  obtain ⟨r, hr⟩ := hsmall.exists
  let a := p4Q2AC_adjacentCoeff r
  have hCsum : (∑ j : Fin (r+2), a j) = 0 :=
    p4Q2AC_adjacentCoeff_sum_zero r
  have hCsq : (∑ j : Fin (r+2), (a j)^2) = 2 :=
    p4Q2AC_adjacentCoeff_sum_sq_two r
  have hLow :=
    hLower (r+1) a hCsum
  rw [hCsq] at hLow
  have hCombination :
      (∑ j : Fin (r+2), a j • v (j:ℕ)) = v r-v (r+1) :=
    p4Q2AC_adjacentCoeff_weighted_sum r v
  rw [hCombination] at hLow
  have hNearPair := p4Q2AC_adjacent_difference_norm_le v u q C hNear r
  have hRate : 0 ≤ C*(q^r+q^(r+1)) := by
    positivity
  have hSquare :
      ‖v r-v (r+1)‖^2 ≤ (C*(q^r+q^(r+1)))^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hNearPair)
      (add_nonneg hRate (norm_nonneg (v r-v (r+1))))]
  have hContr : 2*κ ≤ (C*(q^r+q^(r+1)))^2 := by
    calc
      2*κ = κ*2 := by ring
      _ ≤ ‖v r-v (r+1)‖^2 := hLow
      _ ≤ (C*(q^r+q^(r+1)))^2 := hSquare
  exact (not_lt_of_ge hContr) hr

local instance p4ACGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4ACCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4ACSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4ACMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4ACBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4ACLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4ACComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- The original SU(2) frozen Wilson posterior Gram has no positive
depth-independent coefficient-l2 lower bound on the centered subspace
sum a_j=0, at ANY finite H and ANY nonnegative frozen/fine couplings.
A direct consequence of authentic top-projection geometric convergence,
not an artificial rank-one posterior. -/
theorem fineRightKrylovPairHaarResidualGram_centered_no_uniform_lower
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n : ℕ) :
    ¬ ∃ κ : ℝ, 0 < κ ∧
      ∀ (r : ℕ) (a : Fin (r+1) → ℝ),
        (∑ j : Fin (r+1), a j) = 0 →
        κ*(∑ j : Fin (r+1), (a j)^2) ≤
          star a ⬝ᵥ (Matrix.mulVec
            (fineRightKrylovPairHaarResidualGram
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r) a) := by
  let H := halfExtent (n+1)
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let B := physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n+1))
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  let C : ℝ := (Real.sqrt gamma*B)*Real.sqrt L+Real.sqrt gamma*Real.sqrt L
  let U := WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e (P u))
  let V (j : ℕ) := WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
    I e (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n j))
  have hq : ‖S-P‖ < 1 :=
    physicalOriginalNormalizedFineTransfer_sub_topSpectralProjection_norm_lt_one
      H (beta (n+1)) (hbeta (n+1))
  have hB : 0 ≤ B :=
    physicalOriginalNormalizedTransferConstantStepBetaBudget_nonneg
      H (beta (n+1)) (hbeta (n+1))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hNear (j : ℕ) : ‖V j-U‖ ≤ C*‖S-P‖^j :=
    fineRightKrylov_originalPosteriorFullLink_sub_topProjection_norm_le_geometric_allDepth
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n j
  have hGeneric :=
    p4Q2AC_generic_centered_no_depth_uniform_lower
      V U ‖S-P‖ C (norm_nonneg (S-P)) hq hC hNear
  intro hFrame
  apply hGeneric
  obtain ⟨κ, hκ, hLower⟩ := hFrame
  refine ⟨κ, hκ, ?_⟩
  intro r a hCenter
  have hL := hLower r a hCenter
  have hIdentity :=
    fineRightKrylovPairHaarResidualGram_rayleigh_eq_fullLinkWeightedSum_sq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  change star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r) a) =
      ‖∑ j : Fin (r+1), a j • V (j:ℕ)‖^2 at hIdentity
  rw [hIdentity] at hL
  exact hL

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
