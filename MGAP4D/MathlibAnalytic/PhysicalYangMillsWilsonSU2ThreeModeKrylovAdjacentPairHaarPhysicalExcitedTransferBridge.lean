import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalCoordinateSingularValues
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalSourceGramComparison
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSpectralKrylovDecay
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# P4-Q2-AF4: genuine physical excited Wilson transfer / realized Gram coordinates

The actual normalized finite-volume physical Wilson transfer S_fine acts
on the physical gauge-invariant Haar-L2 SOURCE Hilbert space. The original
frozen-beta signed all-link posterior innovation synthesis A_r acts FROM
its finite Krylov coefficient space INTO a DIFFERENT pair-Haar Hilbert
carrier. We do not pretend the transfer acts on the latter carrier.

For a centered real polynomial of the actual fine Wilson transfer,
F_a = ∑_j a_j S_fine^j u, ∑_j a_j = 0, the genuine full-top projection
P_fine annihilates F_a exactly, irrespective of the rank of the finite
posterior Gram. The authentic one-step transfer preserves this excited
source sector and obeys
    ||S_fine F_a|| <= ||S_fine - P_fine|| ||F_a||,  q_fine < 1.

The physical orthonormal coordinates of the ORIGINAL frozen posterior
Gram (AF1-AF3) measure exactly the receiver energy A_r a; this energy
remains bounded by the actual frozen signed-posterior Hilbert coefficient
times the REAL source norm ||F_a||². We retain the genuine spatial-link
count and finite-volume beta dependence.

No proxy transfer, proxy posterior/Gram, Dobrushin, fictitious
coefficient frame, volume-uniform rate or continuum mass gap is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 850000

/-- The genuine full fixed-space spectral projection is invariant under
every nonnegative power of a real symmetric Hilbert transfer. -/
theorem p4Q2AH_realHilbert_topProjection_transferPower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    (hSym : (S : E →ₗ[ℝ] E).IsSymmetric)
    (j : ℕ) (u : E) :
    realHilbertTopEigenspaceProjection S ((S ^ j) u) =
      realHilbertTopEigenspaceProjection S u := by
  let P : E →L[ℝ] E := realHilbertTopEigenspaceProjection S
  have hPS : P * S = P := by
    change P.comp S = P
    exact realHilbertTopEigenspace_projection_comp S hSym
  have hPow (m : ℕ) : P * S ^ m = P := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, ← mul_assoc, ih, hPS]
  have h := congrArg (fun T : E →L[ℝ] E => T u) (hPow j)
  change P ((S ^ j) u) = P u at h
  exact h

/-- A centered finite REAL Krylov polynomial of the genuine transfer
belongs to the orthogonal complement of its FULL eigenspace at 1. -/
theorem p4Q2AH_realHilbert_centeredTransferPolynomial_top_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    (hSym : (S : E →ₗ[ℝ] E).IsSymmetric)
    (r : ℕ) (u : E) (a : Fin (r+1) → ℝ)
    (hCenter : (∑ j : Fin (r+1), a j) = 0) :
    realHilbertTopEigenspaceProjection S
      (∑ j : Fin (r+1), a j • (S ^ (j : ℕ)) u) = 0 := by
  classical
  let P : E →L[ℝ] E := realHilbertTopEigenspaceProjection S
  change P (∑ j : Fin (r+1), a j • (S ^ (j : ℕ)) u) = 0
  calc
    P (∑ j : Fin (r+1), a j • (S ^ (j : ℕ)) u) =
        ∑ j : Fin (r+1), a j • P ((S ^ (j : ℕ)) u) := by
      simp only [map_sum, map_smul]
    _ = ∑ j : Fin (r+1), a j • P u := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [p4Q2AH_realHilbert_topProjection_transferPower S hSym (j : ℕ) u]
    _ = 0 := by rw [← Finset.sum_smul, hCenter, zero_smul]

/-- A physical vector with zero top spectral projection contracts under
the ORIGINAL transfer in its OWN source Hilbert norm. -/
theorem p4Q2AH_realHilbert_excited_transfer_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) (x : E)
    (hTopZero : realHilbertTopEigenspaceProjection S x = 0) :
    ‖S x‖ ≤ ‖S - realHilbertTopEigenspaceProjection S‖ * ‖x‖ := by
  let P : E →L[ℝ] E := realHilbertTopEigenspaceProjection S
  have hPx : P x = 0 := hTopZero
  have hEq : (S - P) x = S x := by
    simp only [ContinuousLinearMap.sub_apply, hPx, sub_zero]
  calc
    ‖S x‖ = ‖(S - P) x‖ := (congrArg norm hEq).symm
    _ ≤ ‖S - P‖ * ‖x‖ := ContinuousLinearMap.le_opNorm (S - P) x

/-- Top-zero physical sources stay in the excited sector under the
authentic symmetric Wilson transfer, without a new reducing projection. -/
theorem p4Q2AH_realHilbert_excited_transfer_top_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    (hSym : (S : E →ₗ[ℝ] E).IsSymmetric)
    (x : E)
    (hTopZero : realHilbertTopEigenspaceProjection S x = 0) :
    realHilbertTopEigenspaceProjection S (S x) = 0 := by
  have h := realHilbertTopEigenspace_projection_comp S hSym
  have hApply := congrArg (fun T : E →L[ℝ] E => T x) h
  change realHilbertTopEigenspaceProjection S (S x) =
    realHilbertTopEigenspaceProjection S x at hApply
  exact hApply.trans hTopZero

local instance p4AHGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4AHCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4AHSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4AHMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4AHBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4AHLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4AHComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- The existing ACTUAL signed fine-right physical source is literally a
polynomial of the genuine normalized fine Wilson transfer, evaluated at
the physical Haar constant unit. Frozen beta remains separate. -/
theorem fineRightKrylov_originalSignedPhysicalSource_eq_fineTransferPolynomial
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) (a : Fin (r+1) → ℝ) :
    let H := halfExtent (n+1)
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
    let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
    fineRightKrylovOriginalSignedPhysicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a =
      ∑ j : Fin (r+1), a j • (S ^ (j : ℕ)) u := by
  rfl

/-- For every centered coefficient vector, its ACTUAL Wilson physical
source lies in the true excited sector. The original Wilson transfer
contracts it in the SOURCE carrier, never on the pair-Haar receiver
carrier; the inequality is strict at finite H through q<1. -/
theorem fineRightKrylov_originalWilson_centeredPhysicalSource_excitedTransfer
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) (a : Fin (r+1) → ℝ)
    (hCenter : (∑ j : Fin (r+1), a j) = 0) :
    let H := halfExtent (n+1)
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
    let F := fineRightKrylovOriginalSignedPhysicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
    P F = 0 ∧ ‖S F‖ ≤ ‖S-P‖ * ‖F‖ ∧ ‖S-P‖ < 1 := by
  let H := halfExtent (n+1)
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  let F := fineRightKrylovOriginalSignedPhysicalSource
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  have hSym := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  have hF : F = ∑ j : Fin (r+1), a j • (S ^ (j : ℕ)) u :=
    fineRightKrylov_originalSignedPhysicalSource_eq_fineTransferPolynomial
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hTop : P F = 0 := by
    rw [hF]
    change realHilbertTopEigenspaceProjection S
      (∑ j : Fin (r+1), a j • (S ^ (j : ℕ)) u) = 0
    exact p4Q2AH_realHilbert_centeredTransferPolynomial_top_zero S hSym r u a hCenter
  have hNorm : ‖S F‖ ≤ ‖S-P‖ * ‖F‖ := by
    exact p4Q2AH_realHilbert_excited_transfer_norm_le S F hTop
  have hq : ‖S-P‖ < 1 :=
    physicalOriginalNormalizedFineTransfer_sub_topSpectralProjection_norm_lt_one
      H (beta (n+1)) (hbeta (n+1))
  exact ⟨hTop,hNorm,hq⟩

/-- One exact bridge: the orthonormal receiver coordinates of the
ORIGINAL Wilson Gram retain their original signed posterior energy,
while its centered ACTUAL source is annihilated by the genuine fine
transfer top spectral projection and contracts under that transfer.
The receiver energy remains bounded by original frozen posterior
coefficient gamma times the true finite spatial-link count. -/
theorem fineRightKrylov_originalGram_coordinates_excitedTransfer_certificate
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) (a : Fin (r+1) → ℝ)
    (hCenter : (∑ j : Fin (r+1), a j) = 0) :
    let H := halfExtent (n+1)
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
    let F := fineRightKrylovOriginalSignedPhysicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
    let T := fineRightKrylov_originalPhysicalFullLinkSynthesis
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
    ∃ k : ℕ, ∃ Φ : T.range ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k),
      (star a ⬝ᵥ Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a =
        ‖Φ (T.quotKerEquivRange (Submodule.Quotient.mk a))‖^2) ∧
      (‖Φ (T.quotKerEquivRange (Submodule.Quotient.mk a))‖^2 ≤
        ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          originalWilsonPhysicalSignedInnovationHilbertCoefficient
            H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)) *
          ‖F‖^2) ∧
      P F = 0 ∧ ‖S F‖ ≤ ‖S-P‖ * ‖F‖ ∧ ‖S-P‖ < 1 := by
  classical
  let H := halfExtent (n+1)
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  let F := fineRightKrylovOriginalSignedPhysicalSource
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  let T := fineRightKrylov_originalPhysicalFullLinkSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  obtain ⟨k, Φ, hPhi⟩ :=
    fineRightKrylov_originalGram_exists_orthonormalPhysicalCoordinates
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have hEnergy :
      ‖Φ (T.quotKerEquivRange (Submodule.Quotient.mk a))‖^2 ≤
        ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          originalWilsonPhysicalSignedInnovationHilbertCoefficient
            H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)) *
          ‖F‖^2 := by
    calc
      ‖Φ (T.quotKerEquivRange (Submodule.Quotient.mk a))‖^2 =
        star a ⬝ᵥ Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r) a := (hPhi a).symm
      _ ≤ _ := fineRightKrylovPairHaarResidualGram_rayleigh_le_physicalSourceNorm
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a
  have hExc : P F = 0 ∧ ‖S F‖ ≤ ‖S-P‖ * ‖F‖ ∧ ‖S-P‖ < 1 :=
    fineRightKrylov_originalWilson_centeredPhysicalSource_excitedTransfer
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a hCenter
  exact ⟨k,Φ,hPhi a,hEnergy,hExc.1,hExc.2.1,hExc.2.2⟩

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
