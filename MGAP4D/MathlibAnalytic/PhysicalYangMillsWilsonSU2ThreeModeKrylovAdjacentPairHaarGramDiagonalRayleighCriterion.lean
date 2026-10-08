import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarGramDiagonalCrossControl
import Mathlib.Tactic

/-!
# P4: uniform finite-mode Rayleigh estimates reduce to actual diagonal energies

PR #5272 proved that all mixed entries of the ORIGINAL pair-Haar
posterior residual Gram obey 2 * abs(G(i,j)) <= G(i,i) + G(j,j).

This stage proves the finite-dimensional reduction: when every TRUE
full-link diagonal loss is at most C >= 0, the entire Rayleigh form is
at most (number of modes) * C * sum of squared real coefficients.
The factor is r+1 for the actual fine right Krylov family, and 3 for
the original evolved three-mode left Gram. No factor counting the
original spatial links is introduced. This is CONDITIONAL on a
diagonal estimate; the uniform-in-volume diagonal estimate remains open.

The original signed physical receiver, half-density, output drift,
posterior, and beta(n+1) orbit / beta(n) frozen distinction are retained.
There is no Dobrushin, new covariance/L2 identification, hard support,
or continuum Yang-Mills mass gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4RayleighDiagTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4RayleighDiagCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4RayleighDiagSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4RayleighDiagMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4RayleighDiagBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4RayleighDiagSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Pure finite-matrix Rayleigh estimate from absolute entry bounds. -/
private theorem realMatrix_rayleigh_le_l1_sq_of_abs_entries_le
    {ι : Type*} [Fintype ι]
    (G : Matrix ι ι ℝ) (C : ℝ)
    (hEntry : ∀ i j : ι, |G i j| ≤ C)
    (a : ι → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec G a) ≤
      C * (∑ i : ι, |a i|) ^ 2 := by
  classical
  have hTerm (i j : ι) :
      a i * (G i j * a j) ≤ |a i| * C * |a j| := by
    calc
      a i * (G i j * a j) ≤ |a i * (G i j * a j)| :=
        le_abs_self _
      _ = |a i| * |G i j| * |a j| := by rw [abs_mul, abs_mul]
      _ ≤ |a i| * C * |a j| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hEntry i j) (abs_nonneg _))
          (abs_nonneg _)
  calc
    star a ⬝ᵥ (Matrix.mulVec G a) =
      ∑ i : ι, ∑ j : ι, a i * (G i j * a j) := by
        simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    _ ≤ ∑ i : ι, ∑ j : ι, |a i| * C * |a j| := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      exact hTerm i j
    _ = (∑ i : ι, |a i| * C) * (∑ j : ι, |a j|) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
    _ = C * (∑ i : ι, |a i|) ^ 2 := by
      rw [← Finset.sum_mul]
      ring

/-- Finite Cauchy-Schwarz: coefficient l1 mass vs squared Euclidean mass. -/
private theorem realFinite_l1_sq_le_card_mul_l2_sq
    {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (∑ i : ι, |a i|) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i : ι, a i ^ 2 := by
  classical
  have hCS :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
      (fun i : ι => |a i|) (fun _ : ι => (1 : ℝ))
  have hNormalized :
      (∑ i : ι, |a i|) ^ 2 ≤
        (∑ i : ι, a i ^ 2) * (Fintype.card ι : ℝ) := by
    simpa [sq_abs] using hCS
  nlinarith

/-- Any volume-independent bound on each genuine diagonal loss gives
an entire fixed-mode Rayleigh estimate, without a link-count factor. -/
theorem pairHaarSpatialLinkResidualGram_rayleigh_le_card_diagonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (v : ι → PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (C : ℝ) (hC : 0 ≤ C)
    (hDiag : ∀ i : ι,
      pairHaarSpatialLinkResidualGram H N hN beta hbeta v i i ≤ C)
    (a : ι → ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec (pairHaarSpatialLinkResidualGram H N hN beta hbeta v) a) ≤
      ((Fintype.card ι : ℝ) * C) * ∑ i : ι, a i ^ 2 := by
  have hEntry (i j : ι) :
      |pairHaarSpatialLinkResidualGram H N hN beta hbeta v i j| ≤ C :=
    pairHaarSpatialLinkResidualGram_offdiag_abs_le_of_diagonal_bounds
      H N hN beta hbeta v i j C (hDiag i) (hDiag j)
  have hL1 :=
    realMatrix_rayleigh_le_l1_sq_of_abs_entries_le
      (pairHaarSpatialLinkResidualGram H N hN beta hbeta v) C hEntry a
  have hCS := realFinite_l1_sq_le_card_mul_l2_sq a
  calc
    star a ⬝ᵥ
      (Matrix.mulVec (pairHaarSpatialLinkResidualGram H N hN beta hbeta v) a) ≤
      C * (∑ i : ι, |a i|) ^ 2 := hL1
    _ ≤ C * ((Fintype.card ι : ℝ) * ∑ i : ι, a i ^ 2) :=
      mul_le_mul_of_nonneg_left hCS hC
    _ = ((Fintype.card ι : ℝ) * C) * ∑ i : ι, a i ^ 2 := by ring

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- Actual right Krylov: conditional coefficient r+1, no spatial volume. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_of_diagonal_bounds
    (C : ℝ) (hC : 0 ≤ C)
    (hDiag : ∀ i : Fin (r + 1),
      fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i i ≤ C)
    (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      (((r + 1 : ℕ) : ℝ) * C) * ∑ i : Fin (r + 1), a i ^ 2 := by
  simpa using
    (pairHaarSpatialLinkResidualGram_rayleigh_le_card_diagonal
      Hn 2 Pos (beta n) (hbeta n)
      (fun i : Fin (r + 1) =>
        normalizedPhysicalOneSlabPairHaarReceiver
          Hn 2 Pos (beta n) (hbeta n) (RightFactor n (i : ℕ)))
      C hC hDiag a)

/-- Three actual left modes: conditional coefficient three. -/
theorem fineLeftThreeModePairHaarResidualGram_rayleigh_le_of_diagonal_bounds
    (C : ℝ) (hC : 0 ≤ C)
    (hDiag : ∀ i : Fin 3,
      fineLeftThreeModePairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i i ≤ C)
    (a : Fin 3 → ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec (fineLeftThreeModePairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      (3 * C) * ∑ i : Fin 3, a i ^ 2 := by
  simpa using
    (pairHaarSpatialLinkResidualGram_rayleigh_le_card_diagonal
      Hn 2 Pos (beta n) (hbeta n)
      (fun i : Fin 3 =>
        normalizedPhysicalOneSlabPairHaarReceiver
          Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r i))
      C hC hDiag a)

end ActualAdjacentOrbit
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
