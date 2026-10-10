import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarGenuineTwoStepDirichletRayleigh
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# P4-Q2-AL: physical Wilson energy loss, exact discrete telescoping

AK proved the exact optimal two-step adjoint Rayleigh lower bound for
the TRUE Wilson centered operator T=S-P (not a proxy action or Gram).
This file supplies the missing physical-dynamics interpretation:

* For every top-orthogonal real physical state x, the ACTUAL
  Wilson transfer S and centered T have identical action on x.
  Thus ⟪(T†T)x,x⟫ = ‖Sx‖² on actual excited states.
* Every later orbit state S^j x remains top-orthogonal.
* The cumulative two-step Dirichlet energy of the actual Wilson
  orbit telescopes EXACTLY to ‖x‖² - ‖S^k x‖².
* The same energy is bounded below by
     (1 - (‖S-P‖^k)^2) * ‖x‖²
  at every finite Wilson volume, with the genuine finite contraction.
* Specialize all equalities to original centered signed Wilson
  physical Krylov sources, without ever applying S on the frozen
  pair-Haar posterior receiver.

This is an unconditional finite-volume identity and a genuine finite-H
bound. It is NOT a uniform-in-lattice-spacing lower gap, does not prove
a continuum Yang-Mills gap, and introduces no new axioms/sorry/admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 850000

/-- Adjoint squared energy is the actual squared norm of the same
bounded real Hilbert-space operator. -/
theorem p4Q2AL_realHilbert_adjointSquare_inner_eq_map_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E) (x : E) :
    inner ℝ ((T.adjoint ∘L T) x) x = ‖T x‖ ^ 2 := by
  simpa using
    (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left T x).symm

/-- On the canonical full-top-orthogonal sector, the TRUE S and
centered S-P have literally identical physical action. -/
theorem p4Q2AL_realHilbert_centeredOperator_apply_excited
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) (x : E)
    (hTopZero : realHilbertTopEigenspaceProjection S x = 0) :
    (S - realHilbertTopEigenspaceProjection S) x = S x := by
  change S x - realHilbertTopEigenspaceProjection S x = S x
  rw [hTopZero, sub_zero]

/-- For an excited actual physical state the AK positive two-step
form is precisely the loss of squared S-transfer norm. -/
theorem p4Q2AL_realHilbert_excited_dirichlet_inner_eq_transfer_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) (x : E)
    (hTopZero : realHilbertTopEigenspaceProjection S x = 0) :
    inner ℝ
        (((S - realHilbertTopEigenspaceProjection S).adjoint ∘L
          (S - realHilbertTopEigenspaceProjection S)) x) x =
      ‖S x‖ ^ 2 := by
  rw [p4Q2AL_realHilbert_adjointSquare_inner_eq_map_norm_sq]
  rw [p4Q2AL_realHilbert_centeredOperator_apply_excited S x hTopZero]

/-- A purely real additive identity: telescoping the *actual* Wilson
orbit's squared-norm drops introduces no proxy transfer. -/
theorem p4Q2AL_realHilbert_physicalEnergy_telescopes
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) (x : E) (k : ℕ) :
    (∑ j ∈ Finset.range k,
        (‖(S ^ j) x‖ ^ 2 - ‖(S ^ (j + 1)) x‖ ^ 2)) =
      ‖x‖ ^ 2 - ‖(S ^ k) x‖ ^ 2 := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- The entire S-orbit of a centered input remains centered, and every
two-step Dirichlet form is the squared norm of the subsequent genuine
S-orbit state. -/
theorem p4Q2AL_realHilbert_excitedOrbits_adjointEnergy_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    (hSym : (S : E →ₗ[ℝ] E).IsSymmetric)
    (x : E) (hTopZero : realHilbertTopEigenspaceProjection S x = 0)
    (j : ℕ) :
    inner ℝ
        (((S - realHilbertTopEigenspaceProjection S).adjoint ∘L
          (S - realHilbertTopEigenspaceProjection S)) ((S ^ j) x))
        ((S ^ j) x) =
      ‖(S ^ (j + 1)) x‖ ^ 2 := by
  have hj : realHilbertTopEigenspaceProjection S ((S ^ j) x) = 0 :=
    (p4Q2AH_realHilbert_topProjection_transferPower S hSym j x).trans hTopZero
  have hstep : (S ^ (j + 1)) x = S ((S ^ j) x) := by
    rw [pow_succ']
    rfl
  calc
    inner ℝ
        (((S - realHilbertTopEigenspaceProjection S).adjoint ∘L
          (S - realHilbertTopEigenspaceProjection S)) ((S ^ j) x))
        ((S ^ j) x) =
      ‖S ((S ^ j) x)‖ ^ 2 :=
      p4Q2AL_realHilbert_excited_dirichlet_inner_eq_transfer_norm_sq
        S ((S ^ j) x) hj
    _ = ‖(S ^ (j + 1)) x‖ ^ 2 :=
      congrArg (fun y : E => ‖y‖ ^ 2) hstep.symm

/-- Finite-H Wilson excited energy budget: the actual accumulated
transfer loss is bounded below by the exact finite transfer q^k
deficit. No volume-uniform constant is inserted. -/
theorem p4Q2AL_realHilbert_excited_physicalEnergy_lower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    (hSym : (S : E →ₗ[ℝ] E).IsSymmetric)
    (x : E) (hTopZero : realHilbertTopEigenspaceProjection S x = 0)
    (k : ℕ) :
    (1 - (‖S - realHilbertTopEigenspaceProjection S‖ ^ k) ^ 2) *
        ‖x‖ ^ 2 ≤
      ∑ j ∈ Finset.range k,
        (‖(S ^ j) x‖ ^ 2 - ‖(S ^ (j + 1)) x‖ ^ 2) := by
  let q := ‖S - realHilbertTopEigenspaceProjection S‖
  have hPower : ‖(S ^ k) x‖ ≤ q ^ k * ‖x‖ :=
    p4Q2AI_realHilbert_excited_transferPow_norm_le S hSym x hTopZero k
  have hLeft : 0 ≤ ‖(S ^ k) x‖ := norm_nonneg _
  have hRight : 0 ≤ q ^ k * ‖x‖ :=
    mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)
  have hPowerSq : ‖(S ^ k) x‖ ^ 2 ≤ (q ^ k * ‖x‖) ^ 2 :=
    (sq_le_sq₀ hLeft hRight).mpr hPower
  calc
    (1 - q ^ k ^ 2) * ‖x‖ ^ 2 =
        ‖x‖ ^ 2 - (q ^ k * ‖x‖) ^ 2 := by ring
    _ ≤ ‖x‖ ^ 2 - ‖(S ^ k) x‖ ^ 2 :=
      sub_le_sub_left hPowerSq _
    _ = ∑ j ∈ Finset.range k,
        (‖(S ^ j) x‖ ^ 2 - ‖(S ^ (j + 1)) x‖ ^ 2) :=
      (p4Q2AL_realHilbert_physicalEnergy_telescopes S x k).symm

local instance p4ALGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4ALCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4ALSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4ALMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4ALBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4ALComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- ORIGINAL signed Wilson physical Krylov source: all discrete-time
adjoint-square energies equal the squared norms of the TRUE next
physical Wilson orbit states, not those of a posterior-space proxy. -/
theorem fineRightKrylov_originalWilson_physicalDirichlet_orbit_identity
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (hCenter : (∑ j : Fin (r + 1), a j) = 0)
    (j : ℕ) :
    let H := halfExtent (n + 1)
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let F := fineRightKrylovOriginalSignedPhysicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
    inner ℝ
      (((S-P).adjoint ∘L (S-P)) ((S ^ j) F))
        ((S ^ j) F) = ‖(S ^ (j + 1)) F‖ ^ 2 := by
  let H := halfExtent (n + 1)
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
  exact p4Q2AL_realHilbert_excitedOrbits_adjointEnergy_eq
    S hSym F hTop j

/-- Original centered Wilson physical source: ALL k-step energy losses
telescope to the exact physical norm defect, and the genuine finite
q gives its explicit lower bound. No claimed q-uniformity. -/
theorem fineRightKrylov_originalWilson_physicalDirichlet_telescoping_lower
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (hCenter : (∑ j : Fin (r + 1), a j) = 0)
    (k : ℕ) :
    let H := halfExtent (n + 1)
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let F := fineRightKrylovOriginalSignedPhysicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
    (∑ j ∈ Finset.range k,
        (‖(S ^ j) F‖ ^ 2 - ‖(S ^ (j + 1)) F‖ ^ 2)) =
      ‖F‖ ^ 2 - ‖(S ^ k) F‖ ^ 2 ∧
    (1 - (‖S - P‖ ^ k) ^ 2) * ‖F‖ ^ 2 ≤
      (∑ j ∈ Finset.range k,
        (‖(S ^ j) F‖ ^ 2 - ‖(S ^ (j + 1)) F‖ ^ 2)) := by
  let H := halfExtent (n + 1)
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
  exact ⟨p4Q2AL_realHilbert_physicalEnergy_telescopes S F k,
    p4Q2AL_realHilbert_excited_physicalEnergy_lower S hSym F hTop k⟩

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
