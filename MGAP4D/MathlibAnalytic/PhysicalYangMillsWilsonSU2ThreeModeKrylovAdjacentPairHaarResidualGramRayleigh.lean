import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarResidualGram
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# P4: exact Rayleigh forms for the actual pair-Haar residual Gram matrices

PR #5268 constructs positive-semidefinite Gram matrices on the genuine
fine right Krylov family and left three-mode physical family.  Here the
entire quadratic form (not only the diagonal) is identified with the sum
of squared norm residuals of arbitrary finite REAL combinations.

For real coefficients a_i and physical pair-Haar vectors v_i, this gives

  aᵀ G a = ∑_e ‖∑_i a_i (v_i - Q_e v_i)‖²,

where Q_e is the ORIGINAL posterior CondExpL2 transported through the
actual joint half-density, not a free Haar projection or covariance proxy.

At every frozen scale n, the right-family matrix has size (r+1) and the
left-family matrix has size 3.  These exact Rayleigh identities provide
finite-dimensional input for future operator or spectral arguments.
No Dobrushin, hard spatial support, finite-volume-independent bound on
matrix entries, or continuum Yang--Mills mass-gap conclusion is claimed.
The original orbit coupling beta(n+1) and frozen coupling beta(n) remain
distinct.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4RayleighTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p4RayleighCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p4RayleighSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p4RayleighMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p4RayleighBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p4RayleighSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- A matrix sum distributes through the concrete real Rayleigh form.
Keeping the finite sums explicit avoids a hidden cardinality multiplier. -/
private theorem pairHaar_matrixSum_rayleigh
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (M : ε → Matrix ι ι ℝ) (a : ι → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec (∑ e : ε, M e) a) =
      ∑ e : ε, star a ⬝ᵥ (Matrix.mulVec (M e) a) := by
  classical
  simp only [dotProduct, Matrix.mulVec, Matrix.sum_apply]
  calc
    (∑ i : ι, (star a) i * (∑ j : ι, (∑ e : ε, M e i j) * a j)) =
        ∑ i : ι, ∑ j : ι, ∑ e : ε,
          (star a) i * (M e i j * a j) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ e : ε, ∑ i : ι, ∑ j : ι,
          (star a) i * (M e i j * a j) := by
      calc
        _ = ∑ i : ι, ∑ e : ε, ∑ j : ι,
              (star a) i * (M e i j * a j) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = ∑ e : ε, ∑ i : ι,
          (star a) i * (∑ j : ι, M e i j * a j) := by
      simp only [Finset.mul_sum]

/-- Exact finite-dimensional Rayleigh identity for the sum of ALL genuine
posterior pair-Haar squared residuals.  This also gives a constructive
sum-of-squares certificate for positivity for any coefficient vector. -/
theorem pairHaarSpatialLinkResidualGram_rayleigh
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (v : ι → PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (a : ι → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec (pairHaarSpatialLinkResidualGram
        H N hN beta hbeta v) a) =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖∑ i : ι, a i •
          (v i - pairHaarTransportedGroundStateSpatialLinkProjection
            H N hN beta hbeta e (v i))‖ ^ 2 := by
  classical
  let R (e : PeriodicHypercubicEvenSpatialSliceLink H) (i : ι) :=
    v i - pairHaarTransportedGroundStateSpatialLinkProjection
      H N hN beta hbeta e (v i)
  change star a ⬝ᵥ
      (Matrix.mulVec (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        Matrix.gram ℝ (R e)) a) =
    ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖∑ i : ι, a i • R e i‖ ^ 2
  rw [pairHaar_matrixSum_rayleigh]
  apply Finset.sum_congr rfl
  intro e _he
  rw [Matrix.star_dotProduct_gram_mulVec]
  exact real_inner_self_eq_norm_sq _

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
local notation "Q" =>
  pairHaarTransportedGroundStateSpatialLinkProjection
    Hn 2 Pos (beta n) (hbeta n)
local notation "VR" =>
  (fun j : ℕ =>
    normalizedPhysicalOneSlabPairHaarReceiver
      Hn 2 Pos (beta n) (hbeta n) (RightFactor n j))
local notation "VL" =>
  (fun k : Fin 3 =>
    normalizedPhysicalOneSlabPairHaarReceiver
      Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k))

/-- ALL finite right-Krylov combinations have an exact real Rayleigh
representation through the original frozen posterior projections. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh
    (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) =
      ∑ e : Link,
        ‖∑ j : Fin (r + 1), a j •
          (VR (j : ℕ) - Q e (VR (j : ℕ)))‖ ^ 2 := by
  exact pairHaarSpatialLinkResidualGram_rayleigh
    Hn 2 Pos (beta n) (hbeta n)
    (fun j : Fin (r + 1) => VR (j : ℕ)) a

/-- ALL genuine three-mode left combinations have the corresponding
exact frozen posterior Rayleigh representation. -/
theorem fineLeftThreeModePairHaarResidualGram_rayleigh
    (a : Fin 3 → ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec (fineLeftThreeModePairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) =
      ∑ e : Link,
        ‖∑ k : Fin 3, a k •
          (VL k - Q e (VL k))‖ ^ 2 := by
  exact pairHaarSpatialLinkResidualGram_rayleigh
    Hn 2 Pos (beta n) (hbeta n) (fun k : Fin 3 => VL k) a

end ActualAdjacentOrbit
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
