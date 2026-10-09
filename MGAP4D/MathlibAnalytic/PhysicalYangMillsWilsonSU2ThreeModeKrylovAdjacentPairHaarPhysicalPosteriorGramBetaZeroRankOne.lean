import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalSourceGramBetaZeroObstruction
import Mathlib.Tactic

/-!
# P4-Q2-F: fine-beta-zero EXACT original-Wilson posterior Gram rank one

The source-frame obstruction of PR #5342 needs a careful distinction:
the ORIGINAL posterior residual Gram is NOT the physical source Gram.

When only the FINE beta(n+1) vanishes, all actual physical right-Krylov
inputs R_{n,j} are the same physical constant unit u_H. The frozen
posterior coupling beta(n) remains arbitrary and nonnegative.

Consequently the genuine uncentered original Wilson posterior
residual Gram has every entry equal to the EXACT physical-unit
receiver energy
   E_unit(beta(n),H) = sum_e ||(I-Q_{beta(n),e}) V_{beta(n)}u_H||^2.

Its true Rayleigh form is E_unit * (sum_j a_j)^2, not the rank-one
source Gram Rayleigh without E_unit.

If E_unit > 0 is proved for a particular frozen coupling, then this
Gram cannot have a depth-independent coefficient-l2 Rayleigh upper
bound: its unit-direction eigenvalue grows as (r+1) * E_unit.
This is conditional on strict physical E_unit positivity and does
NOT claim that positivity without proof; at frozen beta=0 it may vanish.

No fake posterior, new axiom, sorry/admit, Dobrushin or continuum claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4FrozenRankTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4FrozenRankCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4FrozenRankSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4FrozenRankMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4FrozenRankBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4FrozenRankLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Actual original Wilson posterior Gram has constant physical-unit
receiver energy in EVERY entry when beta(n+1)=0. The distinct frozen
beta(n) remains free; unlike the source Gram, the entry need not be 1. -/
theorem fineRightKrylovPairHaarResidualGram_entry_eq_unitEnergy_of_fine_beta_zero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (hzero : beta (n + 1) = 0)
    (i j : Fin (r + 1)) :
    (fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r) i j =
    physicalOriginalUnitReceiverFullLinkEnergy
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n) := by
  classical
  let H := halfExtent (n + 1)
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let R : Fin (r + 1) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    fun k => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (k : ℕ)
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  have hi : R i = u :=
    fineRightFactor_eq_constantUnit_of_fine_beta_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (i : ℕ) hzero
  have hj : R j = u :=
    fineRightFactor_eq_constantUnit_of_fine_beta_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ) hzero
  rw [fineRightKrylovPairHaarResidualGram_entry_eq_originalPosteriorCovariance]
  change (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      inner ℝ (I e (R i)) (I e (R j))) =
    ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖I e u‖ ^ 2
  apply Finset.sum_congr rfl
  intro e _he
  rw [hi, hj]
  exact real_inner_self_eq_norm_sq _

/-- The ACTUAL UN-CENTERED fine-right posterior Gram Rayleigh at fine
beta zero has the rank-one coefficient E_unit(frozen beta,H), and
therefore differs from the source Gram unless E_unit=1. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_eq_unitEnergy_sum_sq_of_fine_beta_zero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (hzero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) =
      physicalOriginalUnitReceiverFullLinkEnergy
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) *
      (∑ j : Fin (r + 1), a j) ^ 2 := by
  classical
  let G := fineRightKrylovPairHaarResidualGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  let E := physicalOriginalUnitReceiverFullLinkEnergy
    (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
    (beta n) (hbeta n)
  have hEntry (i j : Fin (r + 1)) : G i j = E :=
    fineRightKrylovPairHaarResidualGram_entry_eq_unitEnergy_of_fine_beta_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hzero i j
  change star a ⬝ᵥ (Matrix.mulVec G a) =
    E * (∑ j : Fin (r + 1), a j) ^ 2
  calc
    star a ⬝ᵥ (Matrix.mulVec G a) =
        ∑ i : Fin (r + 1), a i *
          (∑ j : Fin (r + 1), E * a j) := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
      apply Finset.sum_congr rfl
      intro i _hi
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hEntry i j]
    _ = E * (∑ j : Fin (r + 1), a j) ^ 2 := by
      rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- Exact ALL-ONE coefficient Rayleigh value of the original posterior
Gram. This is (r+1)^2 times the genuine unit posterior energy. -/
theorem fineRightKrylovPairHaarResidualGram_ones_rayleigh_eq_unitEnergy_of_fine_beta_zero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (hzero : beta (n + 1) = 0) :
    star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
      (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r)
        (fun _ : Fin (r + 1) => (1 : ℝ))) =
      physicalOriginalUnitReceiverFullLinkEnergy
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) *
      ((r + 1 : ℕ) : ℝ) ^ 2 := by
  simpa using
    (fineRightKrylovPairHaarResidualGram_rayleigh_eq_unitEnergy_sum_sq_of_fine_beta_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hzero (fun _ : Fin (r + 1) => (1 : ℝ)))

/-- Conditional NO-GO for a depth-uniform original posterior Gram:
strictly positive actual frozen unit-receiver energy is explicitly
REQUIRED, not postulated as a fact for every positive coupling. -/
theorem fineRightKrylovPairHaarResidualGram_noUniformFrame_of_fine_beta_zero_unitEnergy_pos
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n : ℕ) (hzero : beta (n + 1) = 0)
    (hE : 0 < physicalOriginalUnitReceiverFullLinkEnergy
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)) :
    ¬ ∃ C : ℝ, ∀ r : ℕ,
      star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r)
          (fun _ : Fin (r + 1) => (1 : ℝ))) ≤
        C * (∑ _j : Fin (r + 1), (1 : ℝ) ^ 2) := by
  let E : ℝ := physicalOriginalUnitReceiverFullLinkEnergy
    (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
    (beta n) (hbeta n)
  rintro ⟨C, hFrame⟩
  obtain ⟨r, hr⟩ := exists_nat_gt (C / E)
  have hRay :=
    fineRightKrylovPairHaarResidualGram_ones_rayleigh_eq_unitEnergy_of_fine_beta_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hzero
  have hCount :
      (∑ _j : Fin (r + 1), (1 : ℝ) ^ 2) =
        ((r + 1 : ℕ) : ℝ) := by simp
  have hBound := hFrame r
  rw [hRay, hCount] at hBound
  have hCr : C < (r : ℝ) * E :=
    (div_lt_iff₀ hE).mp hr
  have hrSucc : (r : ℝ) < ((r + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_succ_self r
  have hC : C < E * ((r + 1 : ℕ) : ℝ) := by
    have hh := mul_lt_mul_of_pos_right hrSucc hE
    nlinarith
  have hPos : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  have hContr := mul_lt_mul_of_pos_right hC hPos
  change E * ((r + 1 : ℕ) : ℝ) ^ 2 ≤
    C * ((r + 1 : ℕ) : ℝ) at hBound
  nlinarith [hContr, hBound]

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
