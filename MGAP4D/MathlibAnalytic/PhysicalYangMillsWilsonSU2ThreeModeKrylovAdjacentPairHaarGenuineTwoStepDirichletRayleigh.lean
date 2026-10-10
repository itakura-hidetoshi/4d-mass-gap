import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUniformLogRateCharacterization
import MGAP4D.MathlibAnalytic.PositiveOperatorRayleighLogRate
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

/-!
# P4-Q2-AK: genuine physical Wilson two-step Dirichlet/Rayleigh gap

AK does not supply the unproved uniform Wilson mass input. Instead, it
reduces the frontier to an **actual physical energy inequality**.

For the TRUE normalized finite Wilson transfer S and its entire eigenvalue-1
top projection P, let T = S-P on the same physical gauge-invariant Haar L2.
The positive operator T†T is the authentic two-step centered transfer
energy operator, not a proxy Gram, posterior, or surrogate dynamics.

1. At every finite volume, for EVERY physical unit vector psi,
     1 - <T†T psi,psi> >= 1 - ||T||² > 0.
2. For ||T||>0 this bound is optimal, in the precise sense that
   an arbitrary lower bound on ALL unit-vector energies is equivalent
   to the same lower bound on 1-||T||². No eigenvector attainment assumed.
3. A physical unit-state energy coercivity estimate
     2*m*a_n <= 1 - <T_n†T_n psi,psi>
   for all n and all physical unit states implies the common Wilson
   one-step bound ||T_n|| <= exp(-m*a_n) and genuine centered source
   all-time decay.

(3) is a CONDITIONAL reduction; actual uniform-in-spacing coercivity
is NOT assumed to have been proved. The q=0 case is included in the
sufficient estimate, without applying log 0. No Dobrushin,
replacement physical carrier, sorry/admit/new axioms or continuum gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 850000

/-- Actual bounded real Hilbert operator T, with no compactness,
spectrum or nonzero assumption: every unit vector has positive-adjoint
energy bounded below by the exact norm deficit 1-||T||². -/
theorem p4Q2AK_realHilbert_adjointTwoStep_unitEnergy_lower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E) (x : E) (hx : ‖x‖ = 1) :
    1 - ‖T‖ ^ 2 ≤
      1 - inner ℝ ((T.adjoint ∘L T) x) x := by
  have hCS :
      inner ℝ ((T.adjoint ∘L T) x) x ≤
        ‖(T.adjoint ∘L T) x‖ * ‖x‖ :=
    real_inner_le_norm ((T.adjoint ∘L T) x) x
  have hOp :
      ‖(T.adjoint ∘L T) x‖ ≤ ‖T.adjoint ∘L T‖ * ‖x‖ :=
    ContinuousLinearMap.le_opNorm (T.adjoint ∘L T) x
  rw [hx, mul_one] at hCS hOp
  have hNorm : ‖T.adjoint ∘L T‖ = ‖T‖ ^ 2 := by
    rw [ContinuousLinearMap.norm_adjoint_comp_self]
    ring
  rw [hNorm] at hOp
  linarith

/-- The previous Dirichlet deficit is the EXACT optimal unit-state
constant as soon as ||T||>0. The converse exploits the genuine positive
adjoint square T†T and its norm-approximating Rayleigh vectors; no
finite-dimensional eigenvector or norm attainment is needed. -/
theorem p4Q2AK_realHilbert_adjointTwoStep_unitEnergy_lower_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hT : 0 < ‖T‖)
    (delta : ℝ) :
    (∀ x : E, ‖x‖ = 1 →
      delta ≤ 1 - inner ℝ ((T.adjoint ∘L T) x) x) ↔
      delta ≤ 1 - ‖T‖ ^ 2 := by
  constructor
  · intro hEnergy
    by_contra h
    have hStrict : 1 - ‖T‖ ^ 2 < delta := lt_of_not_ge h
    have hNorm : ‖T.adjoint ∘L T‖ = ‖T‖ ^ 2 := by
      rw [ContinuousLinearMap.norm_adjoint_comp_self]
      ring
    have hNormPos : 0 < ‖T.adjoint ∘L T‖ := by
      rw [hNorm]
      positivity
    have hThreshold : max 0 (1-delta) < ‖T.adjoint ∘L T‖ := by
      apply max_lt hNormPos
      rw [hNorm]
      linarith
    obtain ⟨x, hx, hxRay⟩ :=
      (ContinuousLinearMap.isPositive_adjoint_comp_self T).exists_unit_inner_gt_of_lt_norm
        (le_max_left 0 (1-delta)) hThreshold
    have hxEnergy := hEnergy x hx
    have hBelow : 1 - delta ≤ max 0 (1-delta) :=
      le_max_right 0 (1-delta)
    linarith
  · intro hDeficit x hx
    exact hDeficit.trans
      (p4Q2AK_realHilbert_adjointTwoStep_unitEnergy_lower T x hx)

/-- A TRUE physical two-step adjoint-energy inequality at all unit
states implies a one-step physical-time exponential bound. This does
not presume q>0; q=0 is handled directly and never logarithmized. -/
theorem p4Q2AK_realHilbert_adjointTwoStep_energy_implies_exp
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E) (spacing mass : ℝ)
    (hEnergy : ∀ x : E, ‖x‖ = 1 →
      2 * mass * spacing ≤
        1 - inner ℝ ((T.adjoint ∘L T) x) x) :
    ‖T‖ ≤ Real.exp (-mass * spacing) := by
  by_cases hPos : 0 < ‖T‖
  · have hDeficit : 2 * mass * spacing ≤ 1 - ‖T‖ ^ 2 :=
      (p4Q2AK_realHilbert_adjointTwoStep_unitEnergy_lower_iff
        T hPos (2 * mass * spacing)).mp hEnergy
    have hLinear : mass * spacing ≤ 1 - ‖T‖ := by
      nlinarith [sq_nonneg (1 - ‖T‖)]
    exact p4Q2AJ_deficit_lower_implies_exp_upper ‖T‖ spacing mass hLinear
  · have hZero : ‖T‖ = 0 :=
      le_antisymm (le_of_not_gt hPos) (norm_nonneg T)
    rw [hZero]
    exact (Real.exp_pos _).le

local instance p4AKGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4AKCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4AKSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4AKMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4AKBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4AKComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- Actual finite SU(2) Wilson centered transfer: every physical unit
vector has strictly positive two-step (adjoint) Dirichlet energy. The
strict constant is exactly the ACTUAL finite-volume norm deficit,
not a postulated volume-uniform number. -/
theorem physicalOriginalNormalizedFineTransfer_twoStep_unitEnergy_pos
    (H : ℕ) (fine : ℝ) (hFine : 0 ≤ fine)
    (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (hx : ‖x‖ = 1) :
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive fine hFine
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive fine hFine
    let T := S - P
    0 < 1 - ‖T‖ ^ 2 ∧
      1 - ‖T‖ ^ 2 ≤
        1 - inner ℝ ((T.adjoint ∘L T) x) x := by
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive fine hFine
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive fine hFine
  let T := S - P
  have hq : ‖T‖ < 1 :=
    physicalOriginalNormalizedFineTransfer_sub_topSpectralProjection_norm_lt_one
      H fine hFine
  have hqNonneg : 0 ≤ ‖T‖ := norm_nonneg T
  have hDeficitPos : 0 < 1 - ‖T‖ ^ 2 := by
    nlinarith
  exact ⟨hDeficitPos,
    p4Q2AK_realHilbert_adjointTwoStep_unitEnergy_lower T x hx⟩

/-- At finite Wilson volume with nonzero actual excitation norm,
the SAME true physical two-step Dirichlet bound is equivalent to the
exact norm-squared spectral deficit. -/
theorem physicalOriginalNormalizedFineTransfer_twoStep_energy_iff_deficit
    (H : ℕ) (fine : ℝ) (hFine : 0 ≤ fine)
    (hFactor :
      0 < ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive fine hFine -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H 2 specialUnitaryTwoWilsonRankPositive fine hFine‖)
    (delta : ℝ) :
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive fine hFine
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive fine hFine
    let T := S - P
    (∀ x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2,
      ‖x‖ = 1 →
        delta ≤ 1 - inner ℝ ((T.adjoint ∘L T) x) x) ↔
      delta ≤ 1 - ‖T‖ ^ 2 := by
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive fine hFine
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive fine hFine
  let T := S - P
  exact p4Q2AK_realHilbert_adjointTwoStep_unitEnergy_lower_iff T hFactor delta

/-- P4-Q2-AK main bridge: a COMMON all-scales unit-state Dirichlet bound
for the ACTUAL Wilson T_n†T_n yields a COMMON exponential bound on
EVERY true centered Krylov source orbit in physical Haar L2.
The missing all-scales Dirichlet hypothesis is explicit and NOT proved. -/
theorem fineRightKrylov_originalWilson_uniformTwoStepEnergy_implies_allTimeMass
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (spacing : ℕ → ℝ) (mass : ℝ)
    (hEnergy : ∀ n : ℕ,
      let H := halfExtent (n + 1)
      let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
      let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
      let T := S - P
      ∀ x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2,
        ‖x‖ = 1 →
          2 * mass * spacing n ≤ 1 - inner ℝ ((T.adjoint ∘L T) x) x)
    (n r : ℕ) (a : Fin (r+1) → ℝ)
    (hCenter : (∑ j : Fin (r+1), a j) = 0)
    (k : ℕ) :
    let H := halfExtent (n+1)
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
    let F := fineRightKrylovOriginalSignedPhysicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
    ‖(S ^ k) F‖ ≤
      Real.exp ((k : ℝ)*(-mass*spacing n))*‖F‖ := by
  let H := halfExtent (n+1)
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  let T := S - P
  have hThis : ∀ x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2,
      ‖x‖ = 1 →
        2 * mass * spacing n ≤ 1 - inner ℝ ((T.adjoint ∘L T) x) x :=
    hEnergy n
  have hStep : ‖S-P‖ ≤ Real.exp (-mass*spacing n) :=
    p4Q2AK_realHilbert_adjointTwoStep_energy_implies_exp T (spacing n) mass hThis
  exact fineRightKrylov_originalWilson_centeredSource_spacingRate_of_certifiedStep
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a hCenter (spacing n) mass hStep k

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
