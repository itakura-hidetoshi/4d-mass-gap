import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarBetaZeroRightKrylovCollapse
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarBetaZeroReceiverRankOne
import Mathlib.Tactic

/-!
# Exact fine-beta-zero collapse of the original right Krylov Gram matrix

The right Krylov orbit evolves at beta(n+1), while its ORIGINAL
frozen posterior conditional expectations use beta(n).

PR #5275 proves that beta(n+1)=0 makes every physical right Krylov
input exactly the original constant Gauss-law physical vector. This
file pushes that equality through the true pair-Haar receiver and
the full spatial-link posterior-residual Gram matrix.

Every matrix entry then equals the SAME actual frozen full-link
residual of the constant physical input. In particular the matrix
has a rank-at-most-one constant-entry form and its last diagonal
controls the original frozen six-color initial energy independent of
Krylov depth r except through the frozen n.

This does NOT identify beta(n) with beta(n+1), and does NOT assert
that the shared frozen residual is zero or bounded uniformly for
positive frozen coupling. No posterior law, physical lambda factor,
signed output, or endpoint swap is changed. No Dobrushin, positive-depth
hard-support assertion, or continuum mass gap is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4FineZeroGramTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4FineZeroGramCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4FineZeroGramSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4FineZeroGramMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4FineZeroGramBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4FineZeroGramSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- For a constant family of REAL pair-Haar vectors, every spatial-link
residual Gram entry is the same literal full-link squared-residual sum. -/
theorem pairHaarSpatialLinkResidualGram_const_apply
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (v : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (i j : ι) :
    pairHaarSpatialLinkResidualGram H N hN beta hbeta
        (fun _ : ι => v) i j =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖v - pairHaarTransportedGroundStateSpatialLinkProjection
          H N hN beta hbeta e v‖ ^ 2 := by
  simp only [pairHaarSpatialLinkResidualGram, Matrix.sum_apply,
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
local notation "Frozen" =>
  physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "V" =>
  normalizedPhysicalOneSlabPairHaarReceiver
    Hn 2 Pos (beta n) (hbeta n)
local notation "Q" =>
  pairHaarTransportedGroundStateSpatialLinkProjection
    Hn 2 Pos (beta n) (hbeta n)
local notation "u" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2

/-- At fine beta(n+1)=0, ALL entries of the actual right Krylov
Gram matrix collapse to the same genuine frozen-beta(n) residual of the
physical constant unit. There is no condition on the frozen beta(n). -/
theorem fineRightKrylovPairHaarResidualGram_entry_eq_const_of_fine_beta_zero
    (hzero : beta (n + 1) = 0)
    (i j : Fin (r + 1)) :
    fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i j =
      ∑ e : Link, ‖V u - Q e (V u)‖ ^ 2 := by
  have hFamily :
      (fun k : Fin (r + 1) => V (RightFactor n (k : ℕ))) =
        (fun _ : Fin (r + 1) => V u) := by
    funext k
    rw [fineRightFactor_eq_constantUnit_of_fine_beta_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (k : ℕ) hzero]
  change pairHaarSpatialLinkResidualGram Hn 2 Pos (beta n) (hbeta n)
    (fun k : Fin (r + 1) => V (RightFactor n (k : ℕ))) i j =
      ∑ e : Link, ‖V u - Q e (V u)‖ ^ 2
  rw [hFamily]
  exact pairHaarSpatialLinkResidualGram_const_apply
    Hn 2 Pos (beta n) (hbeta n) (V u) i j

/-- Exact constant-entry (hence rank-at-most-one) matrix form.
The coefficient is the original full spatial-link frozen posterior
loss, NOT a substitute covariance or a worst-case single-link budget. -/
theorem fineRightKrylovPairHaarResidualGram_eq_constMatrix_of_fine_beta_zero
    (hzero : beta (n + 1) = 0) :
    fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r =
    Matrix.of (fun (_i _j : Fin (r + 1)) =>
      ∑ e : Link, ‖V u - Q e (V u)‖ ^ 2) := by
  ext i j
  exact fineRightKrylovPairHaarResidualGram_entry_eq_const_of_fine_beta_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hzero i j

/-- The ORIGINAL mode-dependent six-color frozen initial energy has
a common-right bound that is independent of the Krylov depth whenever
the fine one-slab coupling is beta(n+1)=0. The frozen posterior law
retains its distinct beta(n) coupling throughout. -/
theorem fineFrozenInitialEnergy_le_constantRightResidual_of_fine_beta_zero
    (hzero : beta (n + 1) = 0) (k : Fin 3) :
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n)
      (Frozen n r k) ≤
      (1 / 6 : ℝ) * ∑ e : Link, ‖V u - Q e (V u)‖ ^ 2 := by
  calc
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n)
        (Frozen n r k) ≤
      (1 / 6 : ℝ) *
        fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r ⟨r, Nat.lt_succ_self r⟩ ⟨r, Nat.lt_succ_self r⟩ :=
      fineFrozenInitialEnergy_le_rightKrylovResidualGram_last
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k
    _ = (1 / 6 : ℝ) * ∑ e : Link, ‖V u - Q e (V u)‖ ^ 2 := by
      rw [fineRightKrylovPairHaarResidualGram_entry_eq_const_of_fine_beta_zero
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hzero ⟨r, Nat.lt_succ_self r⟩ ⟨r, Nat.lt_succ_self r⟩]

end ActualAdjacentOrbit
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
