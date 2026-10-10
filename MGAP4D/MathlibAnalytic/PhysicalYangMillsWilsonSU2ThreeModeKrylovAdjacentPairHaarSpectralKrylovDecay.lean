import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalVolumeHorizonUpper
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalCenteredTransferConvergence
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# P4-Q2-Y: genuine Wilson spectral Krylov orbit decay instead of O(r) telescoping

The ACTUAL normalized finite-volume Wilson transfer S has a canonical
orthogonal projection P onto its entire eigenvalue-one eigenspace.
The exact centered real operator S-P has norm q<1 (strict excited
sector contraction, certified by the existing Wilson spectral theorems).

For every positive Krylov depth j the ORIGINAL fine-right orbit satisfies
  ‖S^j u_H - P u_H‖ ≤ q^j ‖u_H‖.

Passing through the frozen original Wilson posterior signed innovation
at any link and then through the finite full-link PiLp 2 direct sum
preserves this geometric decay with the physical coefficient
sqrt(L_H)*sqrt(gamma_frozen), rather than a depth-growing O(j) budget.

This is a true real-physical S and original posterior I, not a proxy.
The remaining obstruction for a depth-uniform positive Rayleigh is
nonvanishing of the genuine frozen innovation at P u_H and quantitative
control of its projection/overlap. This file makes NO claim that
I(P u_H) is nonzero. It introduces no new physical axioms, no
Dobrushin condition, and no continuum mass-gap assertion.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 750000

/-- Algebraic separation of positive powers of orthogonal idempotent
and excited summands. -/
theorem p4Q2Y_idempotent_add_orthogonal_pow_succ
    {A : Type*} [Ring A] (p z : A)
    (hpp : p * p = p) (hpz : p * z = 0) (hzp : z * p = 0)
    (n : ℕ) :
    (p + z) ^ (n + 1) = p + z ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hzpowp : z ^ (n + 1) * p = 0 := by
        rw [pow_succ, mul_assoc, hzp, mul_zero]
      calc
        (p + z) ^ (Nat.succ n + 1) =
            (p + z) ^ (n + 1) * (p + z) := by
          rw [show Nat.succ n + 1 = (n + 1) + 1 by omega, pow_succ]
        _ = (p + z ^ (n + 1)) * (p + z) := by rw [ih]
        _ = p + z ^ (Nat.succ n + 1) := by
          rw [add_mul, mul_add, mul_add, hpp, hpz, hzpowp]
          simp [pow_succ]

/-- Quantitative spectral orbit control for a symmetric operator on a
complete real Hilbert space using its genuine full fixed-space projection.
No requirement that the top eigenspace be one-dimensional. -/
theorem p4Q2Y_realHilbert_symmetric_pow_succ_sub_topProjection_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    (hSym : (S : E →ₗ[ℝ] E).IsSymmetric)
    (n : ℕ) (u : E) :
    ‖(S ^ (n + 1)) u - realHilbertTopEigenspaceProjection S u‖ ≤
      ‖S - realHilbertTopEigenspaceProjection S‖ ^ (n + 1) * ‖u‖ := by
  let P : E →L[ℝ] E := realHilbertTopEigenspaceProjection S
  let Z : E →L[ℝ] E := S - P
  have hSP : S * P = P := by
    change S.comp (realHilbertTopEigenspaceProjection S) =
      realHilbertTopEigenspaceProjection S
    exact realHilbertTopEigenspace_comp_projection S
  have hPS : P * S = P := by
    change (realHilbertTopEigenspaceProjection S).comp S =
      realHilbertTopEigenspaceProjection S
    exact realHilbertTopEigenspace_projection_comp S hSym
  have hPP : P * P = P := by
    apply ContinuousLinearMap.ext
    intro x
    change P (P x) = P x
    have hx := congrArg (fun T : E →L[ℝ] E => T x) hSP
    have hFix : S (P x) = P x := by simpa only [mul_apply] using hx
    exact (realHilbertTopEigenspaceProjection_apply_eq_self_iff S (P x)).mpr hFix
  have hPZ : P * Z = 0 := by
    dsimp [Z]
    rw [mul_sub, hPS, hPP, sub_self]
  have hZP : Z * P = 0 := by
    dsimp [Z]
    rw [sub_mul, hSP, hPP, sub_self]
  have hDecomp : S = P + Z := by
    dsimp [Z]
    abel
  have hPower : S ^ (n + 1) = P + Z ^ (n + 1) := by
    calc
      S ^ (n + 1) = (P + Z) ^ (n + 1) :=
        congrArg (fun T : E →L[ℝ] E => T ^ (n + 1)) hDecomp
      _ = P + Z ^ (n + 1) :=
        p4Q2Y_idempotent_add_orthogonal_pow_succ P Z hPP hPZ hZP n
  have hApply :
      (S ^ (n + 1)) u - P u = (Z ^ (n + 1)) u := by
    rw [hPower]
    simp
  change ‖(S ^ (n + 1)) u - P u‖ ≤ ‖Z‖ ^ (n + 1) * ‖u‖
  calc
    ‖(S ^ (n + 1)) u - P u‖ = ‖(Z ^ (n + 1)) u‖ :=
      congrArg norm hApply
    _ ≤ ‖Z ^ (n + 1)‖ * ‖u‖ :=
      ContinuousLinearMap.le_opNorm (Z ^ (n + 1)) u
    _ ≤ ‖Z‖ ^ (n + 1) * ‖u‖ :=
      mul_le_mul_of_nonneg_right (norm_pow_le Z (n + 1)) (norm_nonneg u)

local instance p4YSpectralGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4YSpectralCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4YSpectralSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4YSpectralMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4YSpectralBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4YSpectralLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4YSpectralRealHilbertComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- The ACTUAL normalized SU(2) physical Wilson transfer has
strictly contracting real centered part. The center is the exact
top spectral projection, not the beta-zero rank-one surrogate. -/
theorem physicalOriginalNormalizedFineTransfer_sub_topSpectralProjection_norm_lt_one
    (H : ℕ) (fine : ℝ) (hFine : 0 ≤ fine) :
    ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive fine hFine -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H 2 specialUnitaryTwoWilsonRankPositive fine hFine‖ < 1 := by
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive fine hFine
  have hSym :
      (S : _ →ₗ[ℝ] _).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 specialUnitaryTwoWilsonRankPositive fine hFine
  have hEq :
      ‖S - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H 2 specialUnitaryTwoWilsonRankPositive fine hFine‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive fine hFine‖ := by
    simpa [S,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator]
      using (realHilbertCenteredOperator_norm_eq_orthogonalRestriction S hSym)
  change ‖S - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive fine hFine‖ < 1
  rw [hEq]
  exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
    H 2 specialUnitaryTwoWilsonRankPositive fine hFine

/-- A positive-depth actual Wilson right-Krylov mode converges
GEOMETRICALLY to the genuine full-top physical component at the
fine coupling. All extents and coupling parameters stay independent. -/
theorem fineRightKrylov_originalPhysicalOrbit_sub_topProjection_norm_le_geometric
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n j : ℕ) :
    let H := halfExtent (n + 1)
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
    ‖physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j + 1) - P u‖ ≤ ‖S - P‖ ^ (j + 1) * ‖u‖ := by
  let H := halfExtent (n + 1)
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  have hSym :
      (S : _ →ₗ[ℝ] _).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 specialUnitaryTwoWilsonRankPositive
      (beta (n + 1)) (hbeta (n + 1))
  change ‖(S ^ (j + 1)) u - P u‖ ≤ ‖S - P‖ ^ (j + 1) * ‖u‖
  simpa only [S, P] using
    (p4Q2Y_realHilbert_symmetric_pow_succ_sub_topProjection_norm_le S hSym j u)

/-- Signed innovation at each genuine frozen Wilson link also decays
geometrically along the actual fine-right Krylov orbit relative to the
fine-transfer top eigenspace component. -/
theorem fineRightKrylov_originalPosteriorLink_sub_topProjection_norm_le_geometric
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n j : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) :
    let H := halfExtent (n + 1)
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
    let I := physicalOriginalReceiverPosteriorInnovation
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    ‖I e (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j + 1)) - I e (P u)‖ ≤
      Real.sqrt gamma * (‖S - P‖ ^ (j + 1) * ‖u‖) := by
  let H := halfExtent (n + 1)
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let R := physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (j + 1)
  have hOrbit :
      ‖R - P u‖ ≤ ‖S - P‖ ^ (j + 1) * ‖u‖ :=
    fineRightKrylov_originalPhysicalOrbit_sub_topProjection_norm_le_geometric
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n j
  have hBound :=
    physicalOriginalReceiverPosteriorInnovation_norm_le_sqrt_signedHilbert
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
      e (R - P u)
  change ‖I e R - I e (P u)‖ ≤ Real.sqrt gamma *
    (‖S - P‖ ^ (j + 1) * ‖u‖)
  calc
    ‖I e R - I e (P u)‖ = ‖I e (R - P u)‖ := by
      exact (congrArg norm
        (physicalOriginalReceiverPosteriorInnovation_sub
          H 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) e R (P u))).symm
    _ ≤ Real.sqrt gamma * ‖R - P u‖ := hBound
    _ ≤ Real.sqrt gamma * (‖S - P‖ ^ (j + 1) * ‖u‖) :=
      mul_le_mul_of_nonneg_left hOrbit (Real.sqrt_nonneg _)

/-- The exact original signed receiver, assembled over ALL Wilson
spatial links in the genuine PiLp 2 Hilbert direct sum, inherits the
spectral geometric contraction. No volume-uniform q is claimed. -/
theorem fineRightKrylov_originalPosteriorFullLink_sub_topProjection_norm_le_geometric
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n j : ℕ) :
    let H := halfExtent (n + 1)
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
    let I := physicalOriginalReceiverPosteriorInnovation
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    ‖WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
        I e (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j + 1))) -
      WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
        I e (P u))‖ ≤
      (Real.sqrt gamma * (‖S - P‖ ^ (j + 1) * ‖u‖)) *
        Real.sqrt (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) := by
  let H := halfExtent (n + 1)
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let R := physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (j + 1)
  let U := WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e (P u))
  let V := WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e R)
  let C : ℝ := Real.sqrt gamma * (‖S - P‖ ^ (j + 1) * ‖u‖)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hCoordinate :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖V e - U e‖ ≤ ((1 : ℕ) : ℝ) * C := by
    intro e
    have he :=
      fineRightKrylov_originalPosteriorLink_sub_topProjection_norm_le_geometric
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n j e
    simpa only [Nat.cast_one, one_mul] using he
  have hDirect :=
    p4Q2_finite_piLp2_error_le_sqrt_card
      1 U V C hC hCoordinate
  simpa only [Nat.cast_one, one_mul] using hDirect

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
