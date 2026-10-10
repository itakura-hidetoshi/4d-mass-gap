import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalFactorBounds
import Mathlib.Tactic

/-!
# P4-Q2-AR: exact Wilson one-link pair Dirichlet comparison

The literal finite-volume SU(N) temporal-gauge Wilson one-slab kernel obeys
an EXACT right-target-link factorization. Replacing a single right-boundary
link changes only its crossing plaquette and six or fewer touching spatial
plaquettes. The exact local action increment is bounded by 8, INDEPENDENT
OF THE TOTAL spatial volume H.

For any nonnegative Wilson coupling beta and any TWO proposed values g,h
of that same physical right-boundary link, let
  w_beta(g) = K_beta(A, B[target := g]) / K_beta(A,B)
be the already-constructed exact local Boltzmann multiplier (the ratio
notation is explanatory; the formal proof uses the exact multiplier).

The two-link local Dirichlet pair factor satisfies
  exp(-16 beta) <= w_beta(g) w_beta(h) <= exp(16 beta)
with no C_H or global Wilson minorization. Therefore for any real physical
one-link test observable phi,
  exp(-16 beta) * (phi(g)-phi(h))^2
    <= w_beta(g) w_beta(h) * (phi(g)-phi(h))^2.

We moreover identify the right side with the two ACTUAL Wilson kernels,
normalized ONLY by the original raw kernel at the unmodified boundary,
and prove the corresponding finite-sample local Dirichlet bound.

IMPORTANT: this is a real one-link conditional/relative pair-energy
certificate, NOT a volume-uniform spectral gap of the entire transfer,
NOT a claim about the fully normalized conditional fiber measure, and
NOT an a-independent Yang-Mills mass gap. In particular the original
raw base kernel can still decay with the spatial volume. No synthetic
posterior, substitute Gram, Dobrushin argument or extra axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 850000

/-- Genuine one-link relative Wilson two-copy Dirichlet integrand:
the two exact right-target Boltzmann factors multiply the squared
difference of two evaluations of a real one-link test observable. -/
def periodicHypercubicEvenSpecialUnitaryTemporalGaugeRightTargetLocalPairDirichlet
    (H N : ℕ) (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta A B target g *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta A B target h * (phi g - phi h) ^ 2

/-- The TRUE Wilson local two-copy likelihood multiplier is bounded below
independently of the spatial volume. This is not a global-kernel floor. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeRightTargetLocalPairFactor_lower
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp (-16 * beta) ≤
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target g *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target h := by
  let fg := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
    H N beta A B target g
  let fh := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
    H N beta A B target h
  have hg : Real.exp (-8 * beta) ≤ fg :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_exp_neg_eight_mul_le
      H N hN beta hbeta A B target g
  have hh : Real.exp (-8 * beta) ≤ fh :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_exp_neg_eight_mul_le
      H N hN beta hbeta A B target h
  have hfg : 0 ≤ fg :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
      H N beta A B target g).le
  have hprod : Real.exp (-8 * beta) * Real.exp (-8 * beta) ≤ fg * fh := by
    calc
      Real.exp (-8 * beta) * Real.exp (-8 * beta) ≤
          fg * Real.exp (-8 * beta) :=
        mul_le_mul_of_nonneg_right hg (Real.exp_pos _).le
      _ ≤ fg * fh := mul_le_mul_of_nonneg_left hh hfg
  have hExp : Real.exp (-16 * beta) =
      Real.exp (-8 * beta) * Real.exp (-8 * beta) := by
    calc
      Real.exp (-16 * beta) = Real.exp ((-8 * beta) + (-8 * beta)) := by
        congr 1
        ring
      _ = Real.exp (-8 * beta) * Real.exp (-8 * beta) := Real.exp_add _ _
  rw [hExp]
  exact hprod

/-- The same exact Wilson relative two-copy multiplier has an H-independent
upper bound. Both inequalities come from the TRUE local action increment. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeRightTargetLocalPairFactor_upper
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target g *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target h ≤ Real.exp (16 * beta) := by
  let fg := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
    H N beta A B target g
  let fh := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
    H N beta A B target h
  have hg : fg ≤ Real.exp (8 * beta) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
      H N hN beta hbeta A B target g
  have hh : fh ≤ Real.exp (8 * beta) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
      H N hN beta hbeta A B target h
  have hfh : 0 ≤ fh :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
      H N beta A B target h).le
  have hprod : fg * fh ≤ Real.exp (8 * beta) * Real.exp (8 * beta) := by
    calc
      fg * fh ≤ Real.exp (8 * beta) * fh := mul_le_mul_of_nonneg_right hg hfh
      _ ≤ Real.exp (8 * beta) * Real.exp (8 * beta) :=
        mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
  calc
    fg * fh ≤ Real.exp (8 * beta) * Real.exp (8 * beta) := hprod
    _ = Real.exp (16 * beta) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The finite-volume ACTUAL Wilson one-link pair Dirichlet integrand
dominates a Haar-reference pair difference with explicit positive
volume-independent factor exp(-16 beta). No substitute operator is used. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeRightTargetLocalPairDirichlet_lower
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ) :
    Real.exp (-16 * beta) * (phi g - phi h) ^ 2 ≤
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeRightTargetLocalPairDirichlet
        H N beta A B target g h phi := by
  have hPair :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeRightTargetLocalPairFactor_lower
      H N hN beta hbeta A B target g h
  change Real.exp (-16 * beta) * (phi g - phi h) ^ 2 ≤
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta A B target g *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target h) * (phi g - phi h) ^ 2
  exact mul_le_mul_of_nonneg_right hPair (sq_nonneg _)

/-- Exact two-copy identity for the ORIGINAL, literal Wilson one-slab kernel.
The background kernel appears squared and is NOT replaced by a proxy Gram. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeRightTargetActualKernelPair_eq
    (H N : ℕ) (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
        (Function.update B target g) *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
        (Function.update B target h) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target g *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target h *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B ^ 2 := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul]
  ring

/-- The unnormalized ACTUAL two-copy Wilson kernel Dirichlet expression
has an explicit local factor exp(-16 beta), with NO total-volume action
budget. Its original base Wilson kernel remains visible: a full
volume-uniform physical mass gap is NOT being inferred. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeRightTargetActualKernelPairDirichlet_lower
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ) :
    Real.exp (-16 * beta) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B ^ 2 * (phi g - phi h) ^ 2 ≤
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
          (Function.update B target g) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
          (Function.update B target h)) * (phi g - phi h) ^ 2 := by
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
    H N beta A B
  let fg := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
    H N beta A B target g
  let fh := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
    H N beta A B target h
  have hPair : Real.exp (-16 * beta) ≤ fg * fh :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeRightTargetLocalPairFactor_lower
      H N hN beta hbeta A B target g h
  have hStep := mul_le_mul_of_nonneg_right hPair
    (mul_nonneg (sq_nonneg K) (sq_nonneg (phi g - phi h)))
  calc
    Real.exp (-16 * beta) * K ^ 2 * (phi g - phi h) ^ 2 =
        Real.exp (-16 * beta) * (K ^ 2 * (phi g - phi h) ^ 2) := by ring
    _ ≤ (fg * fh) * (K ^ 2 * (phi g - phi h) ^ 2) := hStep
    _ = (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A (Function.update B target g) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A (Function.update B target h)) * (phi g - phi h) ^ 2 := by
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul]
      ring

/-- Any FINITE family of true physical link-pair samples inherits exactly
the same H-independent local Dirichlet factor, without new hypotheses
about Gibbs limits or continuum measures. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeRightTargetLocalFinitePairDirichlet_lower
    {ι : Type*} [Fintype ι]
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : ι → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ) :
    (∑ i : ι, Real.exp (-16 * beta) * (phi (g i) - phi (h i)) ^ 2) ≤
      ∑ i : ι,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeRightTargetLocalPairDirichlet
          H N beta A B target (g i) (h i) phi := by
  classical
  apply Finset.sum_le_sum
  intro i _
  exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeRightTargetLocalPairDirichlet_lower
    H N hN beta hbeta A B target (g i) (h i) phi

end
end MathlibAnalytic
end MGAP4D
