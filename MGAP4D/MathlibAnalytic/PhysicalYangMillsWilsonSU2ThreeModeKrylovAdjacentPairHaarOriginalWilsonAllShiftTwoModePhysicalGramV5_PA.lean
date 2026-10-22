import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonAllIteratedFineKrylovNonzeroV5_OZ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSmallFinePhysicalNormCoercivityV5_OS
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# P4-Q2-PA — actual original Wilson shifted two-mode physical Gram positivity

OZ proves that, on the genuine positive-fine Wilson small-coupling
window already certified by ON's two authentic interacting-posterior
GI contexts, every nonzero REAL coefficient vector of the original
first two Gauss-law Krylov sources survives EVERY normalized-fine
Wilson transfer iterate.

This file transports that existing ANALYTIC nonannihilation result
through the exact genuine Hilbert synthesis identity to the PHYSICAL
shifted two-mode Gram matrix of the same Wilson operator:

  G_{k,ij} = <T_fine^k T_fine^i U, T_fine^k T_fine^j U>_physical,

where i,j in Fin 2, k is arbitrary, and no synthetic independent-Haar
posterior or artificially assumed rank is introduced.

For each fixed finite spatial volume, positive frozen beta and the
authentic small-positive-fine window, prove simultaneously for ALL k:
  * real-linear independence of the actual shifted two-mode vectors;
  * strict positive definiteness of G_k;
  * strictly positive determinant det G_k > 0;
  * positive inverse-Lipschitz norm stability of their true synthesis.

The norm constants MAY depend on the volume, fine/frozen couplings
and shift k. Positivity at every k does NOT imply a lower bound
uniform in k nor independence of THREE adjacent Krylov modes.
In particular the genuine depth-two physical Schur source and the
3x3 Gram determinant remain OPEN, as do U0/endpoint/continuum gap.

Mathlib's genuine finite-dimensional Gram and inverse-Lipschitz
theorems are used; no sorry, admit, new unproved axiom, Dobrushin
or replacement posterior.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Matrix
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PA_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PA_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PA_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PA_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PA_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section ActualShiftedPhysicalWilsonGram
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Unit" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
local notation "Right" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "S" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n

/-- The ACTUAL original physical two-mode Gauss-law Hilbert family
after k transfers of the SAME norm-normalized fine Wilson operator.
For j = 0,1 these are exactly T^k U and T^(k+1) U. -/
noncomputable def p4Q2PA_actualShiftedDepthOneModes (k : ℕ) :
    Fin (1 + 1) → Phys :=
  fun j => (Fine ^ k) (Right n (j : ℕ))

/-- Actual real coefficient synthesis of the shifted first two modes.
No artificial rank or Gram hypothesis is introduced. -/
noncomputable def p4Q2PA_actualShiftedDepthOneSource (k : ℕ) :
    (Fin (1 + 1) → ℝ) →ₗ[ℝ] Phys :=
  (Fine ^ k).toLinearMap.comp (S 1)

/-- Exact original Wilson Hilbert identity:
T^k (S_1 a) = sum_j a_j T^k T^j U, with the same Gauss-law source
and the same norm-normalized fine physical Wilson operator. -/
theorem p4Q2PA_actualShiftedDepthOneSource_eq_sum
    (k : ℕ) (a : Fin (1 + 1) → ℝ) :
    p4Q2PA_actualShiftedDepthOneSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n k a =
      ∑ j : Fin (1 + 1), a j •
        p4Q2PA_actualShiftedDepthOneModes
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n k j := by
  change (Fine ^ k) (∑ j : Fin (1 + 1), a j • Right n (j : ℕ)) =
    ∑ j : Fin (1 + 1), a j • (Fine ^ k) (Right n (j : ℕ))
  rw [map_sum]
  simp only [map_smul]

/-- The entire actual two-mode shifted source map is injective at
EVERY shift k in the ONE authentic ON small-fine interval chosen
before k, by OZ's real Wilson all-iterate nonannihilation. -/
theorem p4Q2PA_actualSmallFine_allShifts_depthOneSource_injective
    (hFrozen : 0 < beta n) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        ∀ k : ℕ, Function.Injective
          (p4Q2PA_actualShiftedDepthOneSource
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n k)) := by
  obtain ⟨delta, hdelta, hNonzero⟩ :=
    p4Q2OZ_actualSmallFine_allIteratedDepthOne_twoMode_physicalNonzero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall k a b hab
  have hDiff :
      p4Q2PA_actualShiftedDepthOneSource
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n k
          (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  by_cases hZero : a - b = 0
  · exact sub_eq_zero.mp hZero
  · have hPhysical : (Fine ^ k) (S 1 (a - b)) ≠ 0 :=
      hNonzero ht hsmall k (a - b) hZero
    exact (hPhysical hDiff).elim

/-- The EXACT physical Gram quadratic is the genuine Gauss-law
Hilbert norm squared of the corresponding shifted Wilson synthesis.
This is not a proxy Gram on a separately chosen source plane. -/
theorem p4Q2PA_actualShiftedGram_quadratic_eq_physicalNormSq
    (k : ℕ) (a : Fin (1 + 1) → ℝ) :
    star a ⬝ᵥ
        ((Matrix.gram ℝ (p4Q2PA_actualShiftedDepthOneModes
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n k)) *ᵥ a) =
      ‖p4Q2PA_actualShiftedDepthOneSource
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n k a‖ ^ 2 := by
  rw [Matrix.star_dotProduct_gram_mulVec]
  rw [p4Q2PA_actualShiftedDepthOneSource_eq_sum]
  exact real_inner_self_eq_norm_sq _

/-- Genuine physical shifted 2x2 Wilson Gram is strictly positive
definite AND has strictly positive determinant for every finite
shift k in the original small-positive-fine interval.
No third-mode positivity claim is hidden in the result. -/
theorem p4Q2PA_actualSmallFine_allShifts_twoModeGram_posDef_det_pos
    (hFrozen : 0 < beta n) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        ∀ k : ℕ,
          (Matrix.gram ℝ (p4Q2PA_actualShiftedDepthOneModes
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n k)).PosDef ∧
          0 < (Matrix.gram ℝ (p4Q2PA_actualShiftedDepthOneModes
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n k)).det) := by
  obtain ⟨delta, hdelta, hInj⟩ :=
    p4Q2PA_actualSmallFine_allShifts_depthOneSource_injective
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall k
  let v := p4Q2PA_actualShiftedDepthOneModes
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n k
  have hLI : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro a hSum j
    have hEq :
        p4Q2PA_actualShiftedDepthOneSource
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n k a = 0 := by
      calc
        _ = ∑ i : Fin (1 + 1), a i • v i :=
          p4Q2PA_actualShiftedDepthOneSource_eq_sum
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n k a
        _ = 0 := hSum
    have ha : a = 0 := (hInj ht hsmall k) (by
      simpa only [map_zero] using hEq)
    simpa using congrArg (fun f : Fin (1 + 1) → ℝ => f j) ha
  have hGram : (Matrix.gram ℝ v).PosDef :=
    Matrix.posDef_gram_of_linearIndependent hLI
  exact ⟨hGram, hGram.det_pos⟩

/-- The same real physically genuine shifted two-mode Wilson
synthesis has a positive inverse-Lipschitz norm constant at EVERY
shift; its value may depend on k and the actual finite volume/
couplings. No uniform lower bound is claimed. -/
theorem p4Q2PA_actualSmallFine_allShifts_physicalNormControl
    (hFrozen : 0 < beta n) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        ∀ k : ℕ, ∃ K : NNReal, 0 < K ∧
          ∀ a : Fin (1 + 1) → ℝ,
            ‖a‖ ≤ (K : ℝ) *
              ‖p4Q2PA_actualShiftedDepthOneSource
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n k a‖) := by
  obtain ⟨delta, hdelta, hInj⟩ :=
    p4Q2PA_actualSmallFine_allShifts_depthOneSource_injective
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall k
  exact p4Q2OS_finiteDimensional_injective_normControl
    (p4Q2PA_actualShiftedDepthOneSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n k)
    (hInj ht hsmall k)

end ActualShiftedPhysicalWilsonGram
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PA_actualShiftedDepthOneSource_eq_sum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PA_actualSmallFine_allShifts_depthOneSource_injective
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PA_actualShiftedGram_quadratic_eq_physicalNormSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PA_actualSmallFine_allShifts_twoModeGram_posDef_det_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PA_actualSmallFine_allShifts_physicalNormControl
