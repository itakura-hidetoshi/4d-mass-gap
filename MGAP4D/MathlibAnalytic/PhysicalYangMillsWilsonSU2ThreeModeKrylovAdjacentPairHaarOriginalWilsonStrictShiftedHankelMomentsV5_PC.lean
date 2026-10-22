import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonPhysicalKrylovHankelMomentsV5_PB
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonAllShiftTwoModePhysicalGramV5_PA
import Mathlib.Tactic

/-!
# P4-Q2-PC — strict original shifted physical Wilson Hankel moments

PA's true original Wilson all-shift two-mode positivity and PB's
exact normalized physical Wilson Hankel identity combine to give a
strict scalar moment inequality at EVERY transfer shift k, in the SAME
positive-fine interval fixed by the real interacting-posterior minor ON.

For the genuine Gauss-law constant source U and normalized physical
one-slab Wilson transfer T, put m_j = <U,T^j U>_physical. Then

  m_(2k) * m_(2k+2) - m_(2k+1)^2 > 0

for all k at fixed finite volume, frozen beta>0, and the authentic
small-positive fine window. This is the genuine order-two strict
Hankel condition, NOT the still-unproved order-three determinant.
All Perron halfweights and two original Wilson couplings are unchanged.
No artificial spectral law, third-rank assumption, new axiom, sorry,
admit, Dobrushin or independent-Haar surrogate.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory Matrix
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PC_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PC_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PC_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PC_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PC_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Actual normalized physical Wilson scalar Hankel at even shift 2k.
It is built from PB's original Gauss-law Hilbert moments, not an
independent or hypothetical spectral measure. -/
noncomputable def p4Q2PC_originalWilsonEvenShiftedHankel
    (H : ℕ) (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
    Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℝ :=
  Matrix.of (fun i j : Fin (1 + 1) =>
    p4Q2PB_originalWilsonPhysicalMoment H t ht
      (k + k + (i : ℕ) + (j : ℕ)))

section ActualWilsonShiftedHankel
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive
    (beta (n + 1)) (hbeta (n + 1))

/-- Exact same-Wilson identification of PA's shifted two-mode Gauss-law
Gram with PB's genuine scalar moment Hankel matrix at shift 2k. -/
theorem p4Q2PC_actualShiftedGram_eq_originalWilsonEvenShiftedHankel
    (k : ℕ) :
    Matrix.gram ℝ (p4Q2PA_actualShiftedDepthOneModes
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n k) =
    p4Q2PC_originalWilsonEvenShiftedHankel
      Hn (beta (n + 1)) (hbeta (n + 1)) k := by
  ext i j
  change inner ℝ ((Fine ^ k) ((Fine ^ (i : ℕ)) U))
      ((Fine ^ k) ((Fine ^ (j : ℕ)) U)) =
    p4Q2PB_originalWilsonPhysicalMoment
      Hn (beta (n + 1)) (hbeta (n + 1))
      (k + k + (i : ℕ) + (j : ℕ))
  have hPow (r : ℕ) :
      (Fine ^ k) ((Fine ^ r) U) = (Fine ^ (k + r)) U := by
    rw [pow_add]
    rfl
  rw [hPow (i : ℕ), hPow (j : ℕ)]
  have hMoment :=
    p4Q2PB_originalWilsonPhysicalKrylov_inner_eq_moment
      Hn (beta (n + 1)) (hbeta (n + 1))
      (k + (i : ℕ)) (k + (j : ℕ))
  convert hMoment using 1
  congr 1
  omega

/-- All genuinely shifted scalar two-moment Hankel matrices are
positive definite and have STRICTLY positive determinant, for every
k in the common true small-positive fine window of ON/PA.
No depth-two three-mode positive determinant is claimed. -/
theorem p4Q2PC_actualSmallFine_allShifts_originalHankel_posDef_det_pos
    (hFrozen : 0 < beta n) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        ∀ k : ℕ,
          (p4Q2PC_originalWilsonEvenShiftedHankel
            Hn (beta (n + 1)) (hbeta (n + 1)) k).PosDef ∧
          0 < (p4Q2PC_originalWilsonEvenShiftedHankel
            Hn (beta (n + 1)) (hbeta (n + 1)) k).det) := by
  obtain ⟨delta, hdelta, hGram⟩ :=
    p4Q2PA_actualSmallFine_allShifts_twoModeGram_posDef_det_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall k
  simpa only [p4Q2PC_actualShiftedGram_eq_originalWilsonEvenShiftedHankel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n k]
    using (hGram ht hsmall k)

/-- Strict shifted Cauchy--Schwarz *in scalar Wilson physical
moments*, not a generic moment-model assumption:
m_(2k) m_(2k+2) > m_(2k+1)^2 at every actual shift k.
This is compatible with, but does not itself exclude, exact
two-eigenvalue quadratic Krylov closure. -/
theorem p4Q2PC_actualSmallFine_allShifts_strictWilsonMomentLogConvex
    (hFrozen : 0 < beta n) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        ∀ k : ℕ,
          0 <
            p4Q2PB_originalWilsonPhysicalMoment Hn
              (beta (n + 1)) (hbeta (n + 1)) (k + k) *
            p4Q2PB_originalWilsonPhysicalMoment Hn
              (beta (n + 1)) (hbeta (n + 1)) (k + k + 2) -
            (p4Q2PB_originalWilsonPhysicalMoment Hn
              (beta (n + 1)) (hbeta (n + 1)) (k + k + 1)) ^ 2) := by
  obtain ⟨delta, hdelta, hHankel⟩ :=
    p4Q2PC_actualSmallFine_allShifts_originalHankel_posDef_det_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall k
  have hdet := (hHankel ht hsmall k).2
  simpa [p4Q2PC_originalWilsonEvenShiftedHankel,
    Matrix.det_fin_two, pow_two, Nat.add_assoc] using hdet

end ActualWilsonShiftedHankel
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PC_actualShiftedGram_eq_originalWilsonEvenShiftedHankel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PC_actualSmallFine_allShifts_originalHankel_posDef_det_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PC_actualSmallFine_allShifts_strictWilsonMomentLogConvex
