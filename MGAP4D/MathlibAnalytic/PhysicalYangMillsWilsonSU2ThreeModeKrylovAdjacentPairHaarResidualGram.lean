import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPosteriorProjectionNormLoss
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# Finite Krylov Gram matrices of the genuine pair-Haar posterior residuals

PR #5267 expresses the original frozen six-color initial energy and its
mode-dependent left link losses in terms of
  ||v - Q_e v||^2 = ||v||^2 - ||Q_e v||^2,
where Q_e is the TRUE transported weighted posterior projection, not an
independent Haar conditional expectation.

This file compresses the exact full-link residual quadratic form to
finite matrices on the ACTUAL Krylov orbit:

* Right: modes S_fine^j 1 for j = 0,...,r, giving an (r+1)x(r+1)
  positive semidefinite Gram matrix at the frozen coupling beta(n).
* Left: the three true primary Gram--Schmidt modes S_fine^r phi_k,
  giving a 3x3 positive semidefinite Gram matrix.

Every Gram entry sums actual pair-Haar residual inner products over ALL
spatial links.  Its diagonal is exactly the residual square sum, so the
original six-color energy and the summed left one-link errors are bounded
by the corresponding diagonal elements with no link-cardinality
substitution or arbitrary covariance/L2 identification.

Matrix SIZE is independent of spatial volume at fixed r; matrix ENTRIES
are not yet proved uniformly bounded.  No Dobrushin estimate, hard
support at positive depth, volume-uniform full-link bound, or continuum
mass-gap assertion is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4KrylovGramTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p4KrylovGramCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p4KrylovGramSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p4KrylovGramMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p4KrylovGramBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p4KrylovGramSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The genuinely transported pair-Haar posterior residual Gram matrix
on an arbitrary finite family of physical pair-Haar vectors.
No independence, locality, or covariance bound is required. -/
noncomputable def pairHaarSpatialLinkResidualGram
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (v : ι → PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    Matrix ι ι ℝ :=
  ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
    Matrix.gram ℝ (fun i : ι =>
      v i - pairHaarTransportedGroundStateSpatialLinkProjection
        H N hN beta hbeta e (v i))

/-- Every finite genuine posterior-residual Gram matrix is positive
semidefinite.  This is an exact Hilbert-space fact, independent of
Dobrushin or volume-uniform estimates. -/
theorem pairHaarSpatialLinkResidualGram_posSemidef
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (v : ι → PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    (pairHaarSpatialLinkResidualGram H N hN beta hbeta v).PosSemidef := by
  unfold pairHaarSpatialLinkResidualGram
  exact Matrix.posSemidef_sum
    (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) (by
      intro e _he
      exact Matrix.posSemidef_gram ℝ
        (fun i : ι =>
          v i - pairHaarTransportedGroundStateSpatialLinkProjection
            H N hN beta hbeta e (v i)))

/-- The Gram diagonal is EXACTLY the full spatial-link squared-residual
sum, not a cardinality times a worst-case one-link bound. -/
theorem pairHaarSpatialLinkResidualGram_diag
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (v : ι → PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (i : ι) :
    pairHaarSpatialLinkResidualGram H N hN beta hbeta v i i =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖v i - pairHaarTransportedGroundStateSpatialLinkProjection
          H N hN beta hbeta e (v i)‖ ^ 2 := by
  simp only [pairHaarSpatialLinkResidualGram, Finset.sum_apply,
    Matrix.gram_apply, real_inner_self_eq_norm_sq]

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "Frozen" =>
  physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "Q" =>
  pairHaarTransportedGroundStateSpatialLinkProjection
    Hn 2 Pos (beta n) (hbeta n)
local notation "PLeft" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
    Hn 2 Pos (beta n) (hbeta n)
local notation "VR" =>
  (fun j : ℕ =>
    normalizedPhysicalOneSlabPairHaarReceiver
      Hn 2 Pos (beta n) (hbeta n) (RightFactor n j))
local notation "VL" =>
  (fun k : Fin 3 =>
    normalizedPhysicalOneSlabPairHaarReceiver
      Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k))

/-- Exact (r+1)-mode Krylov compression for the actual common-right
physical orbit, with S_fine^j applied to the ORIGINAL constant vector.
The posterior projection always uses beta(n), not beta(n+1). -/
noncomputable def fineRightKrylovPairHaarResidualGram :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  pairHaarSpatialLinkResidualGram Hn 2 Pos (beta n) (hbeta n)
    (fun j : Fin (r + 1) => VR (j : ℕ))

theorem fineRightKrylovPairHaarResidualGram_posSemidef :
    (fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r).PosSemidef :=
  pairHaarSpatialLinkResidualGram_posSemidef
    Hn 2 Pos (beta n) (hbeta n)
    (fun j : Fin (r + 1) => VR (j : ℕ))

theorem fineRightKrylovPairHaarResidualGram_diag
    (j : Fin (r + 1)) :
    fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r j j =
      ∑ e : Link, ‖VR (j : ℕ) - Q e (VR (j : ℕ))‖ ^ 2 :=
  pairHaarSpatialLinkResidualGram_diag
    Hn 2 Pos (beta n) (hbeta n)
    (fun j : Fin (r + 1) => VR (j : ℕ)) j

/-- The original six-color frozen energy is bounded by the final diagonal
of the finite TRUE right-Krylov residual Gram matrix.  Its size is r+1;
no number-of-spatial-links factor is inserted. -/
theorem fineFrozenInitialEnergy_le_rightKrylovResidualGram_last
    (k : Fin 3) :
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n)
        (Frozen n r k) ≤
      (1 / 6 : ℝ) *
        fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r ⟨r, Nat.lt_succ_self r⟩ ⟨r, Nat.lt_succ_self r⟩ := by
  have hOriginal :=
    fineFrozenInitialEnergy_le_pairHaarRightProjectionResiduals
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  calc
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n)
        (Frozen n r k) ≤
      (1 / 12 : ℝ) * ∑ e : Link, 2 * ‖VR r - Q e (VR r)‖ ^ 2 :=
        hOriginal
    _ = (1 / 6 : ℝ) * ∑ e : Link,
          ‖VR r - Q e (VR r)‖ ^ 2 := by
      rw [← Finset.mul_sum]
      ring
    _ = (1 / 6 : ℝ) *
        fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r ⟨r, Nat.lt_succ_self r⟩ ⟨r, Nat.lt_succ_self r⟩ := by
      congr 1
      exact (fineRightKrylovPairHaarResidualGram_diag
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r ⟨r, Nat.lt_succ_self r⟩).symm

/-- True three-mode Gram matrix of the left physical Krylov factors,
all transported through the EXACT frozen joint half-density. -/
noncomputable def fineLeftThreeModePairHaarResidualGram :
    Matrix (Fin 3) (Fin 3) ℝ :=
  pairHaarSpatialLinkResidualGram Hn 2 Pos (beta n) (hbeta n)
    (fun k : Fin 3 => VL k)

theorem fineLeftThreeModePairHaarResidualGram_posSemidef :
    (fineLeftThreeModePairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r).PosSemidef :=
  pairHaarSpatialLinkResidualGram_posSemidef
    Hn 2 Pos (beta n) (hbeta n) (fun k : Fin 3 => VL k)

theorem fineLeftThreeModePairHaarResidualGram_diag
    (k : Fin 3) :
    fineLeftThreeModePairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k k =
      ∑ e : Link, ‖VL k - Q e (VL k)‖ ^ 2 :=
  pairHaarSpatialLinkResidualGram_diag
    Hn 2 Pos (beta n) (hbeta n) (fun k : Fin 3 => VL k) k

/-- Even after summing EVERY original left spatial-link residual, its
exact total remains bounded by ONE diagonal entry of the true three-mode
residual Gram matrix.  No Dobrushin or false positive-depth support. -/
theorem fineFrozenLeftResidualSum_le_threeModePairHaarGram_diag
    (k : Fin 3) :
    (∑ e : Link,
      ‖Frozen n r k - PLeft e (Frozen n r k)‖ ^ 2) ≤
      fineLeftThreeModePairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k k := by
  calc
    (∑ e : Link,
      ‖Frozen n r k - PLeft e (Frozen n r k)‖ ^ 2) ≤
        ∑ e : Link, ‖VL k - Q e (VL k)‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro e _he
          exact fineFrozenLeftSpatialLinkResidual_sq_le_pairHaarLeftProjectionResidual
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k e
    _ = fineLeftThreeModePairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k k :=
      (fineLeftThreeModePairHaarResidualGram_diag
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k).symm

end ActualAdjacentOrbit
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
