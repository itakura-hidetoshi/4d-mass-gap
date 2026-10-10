import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalDirichletTelescoping
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroExactTransferGap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# P4-Q2-AM: ORIGINAL raw Wilson kernel Dirichlet energy of true physical sources

AL made the positive adjoint-square energy of the TRUE centered normalized
finite SU(2) Wilson transfer into physical-time orbit norm loss.
Here we descend one level further to the ACTUAL UNNORMALIZED Wilson one-slab
Haar-L² transfer R_beta, which is the Gauss-law restriction of the literal
Wilson Hilbert-Schmidt kernel. Write S_beta = ‖R_beta‖⁻¹ • R_beta,
P_beta its entire eigenvalue-one spectral projection, and F the ORIGINAL
centered signed Wilson physical source (not a frozen posterior receiver).

We prove the EXACT identity:
  ‖R_beta‖² * (‖F‖² - <(S_beta-P_beta)†(S_beta-P_beta) F,F>)
     = ‖R_beta‖²*‖F‖² - ‖R_beta F‖².
The right side contains only the original raw physical Wilson kernel and
its real Hilbert norm. Furthermore its finite-volume Rayleigh lower bound
has the exact factor (1-‖S_beta-P_beta‖²) ‖R_beta‖² ‖F‖².

At beta=0, the raw normalized Wilson physical transfer is rank-one and
the canonical full-top centered operator is EXACTLY zero; this proves the
endpoint rate but does NOT prove any beta>0/spacing-uniform mass bound.
No new proxy, no receiver-space transfer, no new axioms/sorry/admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 850000

/-- Exact raw/normalized squared norm relation. The numerator is the
actual operator R rather than a surrogate quadratic form. -/
theorem p4Q2AM_realHilbert_raw_normalized_sq_norm_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (R : E →L[ℝ] E) (hR : 0 < ‖R‖) (x : E) :
    ‖R‖ ^ 2 * ‖(‖R‖⁻¹ • R) x‖ ^ 2 = ‖R x‖ ^ 2 := by
  have hScale : ‖R‖ * ‖(‖R‖⁻¹ • R) x‖ = ‖R x‖ := by
    change ‖R‖ * ‖‖R‖⁻¹ • R x‖ = ‖R x‖
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    rw [mul_inv_cancel_left₀ hR.ne']
  calc
    ‖R‖ ^ 2 * ‖(‖R‖⁻¹ • R) x‖ ^ 2 =
      (‖R‖ * ‖(‖R‖⁻¹ • R) x‖) ^ 2 := by ring
    _ = ‖R x‖ ^ 2 := by rw [hScale]

local instance p4AMGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4AMCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4AMSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4AMMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4AMBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4AMComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- Original centered Wilson physical source F: its AK/AL adjoint-square
energy is EXACTLY the normalized original RAW Wilson one-slab kernel
squared-norm defect. No fictional receiver transfer and no substitute
posterior Gram are used. -/
theorem fineRightKrylov_originalWilson_rawKernel_dirichlet_energy_identity
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (hCenter : (∑ j : Fin (r + 1), a j) = 0) :
    let H := halfExtent (n + 1)
    let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let F := fineRightKrylovOriginalSignedPhysicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
    ‖R‖ ^ 2 *
        (‖F‖ ^ 2 - inner ℝ (((S - P).adjoint ∘L (S - P)) F) F) =
      ‖R‖ ^ 2 * ‖F‖ ^ 2 - ‖R F‖ ^ 2 := by
  let H := halfExtent (n + 1)
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let F := fineRightKrylovOriginalSignedPhysicalSource
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hTop :=
    (fineRightKrylov_originalWilson_centeredPhysicalSource_excitedTransfer
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a hCenter).1
  have hEnergy :
      inner ℝ (((S - P).adjoint ∘L (S - P)) F) F = ‖S F‖ ^ 2 :=
    p4Q2AL_realHilbert_excited_dirichlet_inner_eq_transfer_norm_sq S F hTop
  have hRPos : 0 < ‖R‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  have hNorm :
      ‖R‖ ^ 2 * ‖S F‖ ^ 2 = ‖R F‖ ^ 2 := by
    change ‖R‖ ^ 2 * ‖(‖R‖⁻¹ • R) F‖ ^ 2 = ‖R F‖ ^ 2
    exact p4Q2AM_realHilbert_raw_normalized_sq_norm_identity R hRPos F
  calc
    ‖R‖ ^ 2 * (‖F‖ ^ 2 -
      inner ℝ (((S - P).adjoint ∘L (S - P)) F) F) =
        ‖R‖ ^ 2 * (‖F‖ ^ 2 - ‖S F‖ ^ 2) := by rw [hEnergy]
    _ = ‖R‖ ^ 2 * ‖F‖ ^ 2 - ‖R F‖ ^ 2 := by rw [← hNorm]; ring

/-- Strictly positive finite-H raw Wilson Dirichlet control on the
ORIGINAL centered physical source. The raw scale ‖R‖² is retained
explicitly, so no uniform-in-volume/spacing normalization is hidden. -/
theorem fineRightKrylov_originalWilson_rawKernel_dirichlet_finiteLower
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (hCenter : (∑ j : Fin (r + 1), a j) = 0) :
    let H := halfExtent (n + 1)
    let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let F := fineRightKrylovOriginalSignedPhysicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
    (1 - ‖S - P‖ ^ 2) * ‖R‖ ^ 2 * ‖F‖ ^ 2 ≤
      ‖R‖ ^ 2 * ‖F‖ ^ 2 - ‖R F‖ ^ 2 := by
  let H := halfExtent (n + 1)
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let F := fineRightKrylovOriginalSignedPhysicalSource
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hTop :=
    (fineRightKrylov_originalWilson_centeredPhysicalSource_excitedTransfer
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a hCenter).1
  have hSym :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  have hOne : ‖S F‖ ≤ ‖S - P‖ * ‖F‖ :=
    p4Q2AH_realHilbert_excited_transfer_norm_le S F hTop
  have hSq : ‖S F‖ ^ 2 ≤ (‖S - P‖ * ‖F‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg (S F)) (mul_nonneg
      (norm_nonneg (S - P)) (norm_nonneg F))).mpr hOne
  have hRPos : 0 < ‖R‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  have hNorm : ‖R‖ ^ 2 * ‖S F‖ ^ 2 = ‖R F‖ ^ 2 := by
    change ‖R‖ ^ 2 * ‖(‖R‖⁻¹ • R) F‖ ^ 2 = ‖R F‖ ^ 2
    exact p4Q2AM_realHilbert_raw_normalized_sq_norm_identity R hRPos F
  calc
    (1 - ‖S - P‖ ^ 2) * ‖R‖ ^ 2 * ‖F‖ ^ 2 =
      ‖R‖ ^ 2 * (‖F‖ ^ 2 - (‖S - P‖ * ‖F‖) ^ 2) := by ring
    _ ≤ ‖R‖ ^ 2 * (‖F‖ ^ 2 - ‖S F‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hSq _) (sq_nonneg ‖R‖)
    _ = ‖R‖ ^ 2 * ‖F‖ ^ 2 - ‖R F‖ ^ 2 := by rw [← hNorm]; ring

end GroundStatePosteriorJoint

/-- At the exact beta-zero endpoint, the ACTUAL SU(2) normalized Wilson
transfer agrees with its full eigenvalue-one orthogonal projection.
In particular, the genuine centered physical operator is ZERO at
every finite spatial volume. No continuity/positive-beta claim. -/
theorem p4Q2AM_originalWilson_betaZero_centeredOperator_eq_zero
    (H : ℕ) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive 0 (by norm_num) -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H 2 specialUnitaryTwoWilsonRankPositive 0 (by norm_num) = 0 := by
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive 0 (by norm_num)
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive 0 (by norm_num)
  have hSym :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 specialUnitaryTwoWilsonRankPositive 0 (by norm_num)
  have hNorm : ‖S - P‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive 0 (by norm_num)‖ := by
    simpa [S, P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator]
      using (realHilbertCenteredOperator_norm_eq_orthogonalRestriction S hSym)
  have hZero : ‖S - P‖ = 0 :=
    hNorm.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_zero_norm
        H 2 specialUnitaryTwoWilsonRankPositive)
  change S - P = 0
  exact (ContinuousLinearMap.opNorm_zero_iff (S - P)).mp hZero

end
end MathlibAnalytic
end MGAP4D
