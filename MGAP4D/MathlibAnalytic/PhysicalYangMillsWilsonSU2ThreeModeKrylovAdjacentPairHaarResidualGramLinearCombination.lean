import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarResidualGramRayleigh
import Mathlib.Tactic

/-!
# The actual transported posterior projection is linear on the pair-Haar carrier

PR #5269 constructs exact Rayleigh quadratic forms on the right Krylov
and three original physical left modes, but the right-hand side initially
remains a sum of individual residual vectors.

The actual transported posterior operator is
    Q_e v = U.symm (P_e (U v)),
where U is the original joint-half-density linear isometry equivalence
and P_e is the original joint conditional-expectation continuous linear
projection. Therefore Q_e is REAL linear, with no new conditional law.

This file proves that the entire Gram Rayleigh form is literally the sum
of squared residuals of the FINITE COMBINED PAIR-HAAR RECEIVER, not a
worst-case bound multiplied by the number of links. The specialization
keeps the true right Krylov family and the three evolved Gram-Schmidt
left inputs, and retains the distinct orbit and frozen beta scales.

These are exact finite-volume identities. They do not prove that the
finite residual sums or Gram entries are volume-uniform. There is no
Dobrushin estimate, hard support, covariance/L2-coordinate identification,
or continuum Yang-Mills mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4LinearRayleighTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4LinearRayleighCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4LinearRayleighSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4LinearRayleighMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4LinearRayleighBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4LinearRayleighSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Q_e is additive because both ground-state half-density transports
and the ORIGINAL conditional expectation are real-linear operators. -/
theorem pairHaarTransportedGroundStateSpatialLinkProjection_add
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (v w : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e (v + w) =
      pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e v +
      pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e w := by
  simp only [pairHaarTransportedGroundStateSpatialLinkProjection, map_add]

/-- Q_e respects arbitrary REAL coefficients, not merely the Gram basis. -/
theorem pairHaarTransportedGroundStateSpatialLinkProjection_smul
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) (a : ℝ)
    (v : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e (a • v) =
      a • pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e v := by
  simp only [pairHaarTransportedGroundStateSpatialLinkProjection, map_smul]

/-- The transported ORIGINAL posterior projection commutes with finite
real-linear combinations of pair-Haar receivers. -/
theorem pairHaarTransportedGroundStateSpatialLinkProjection_sum_smul
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    {ι : Type*} [Fintype ι]
    (v : ι → PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (a : ι → ℝ) :
    pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
        (∑ i : ι, a i • v i) =
      ∑ i : ι, a i •
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e (v i) := by
  classical
  simp only [pairHaarTransportedGroundStateSpatialLinkProjection, map_sum, map_smul]

/-- The finite sum of the true one-link residuals is exactly the one-link
residual of the combined receiver. This is an identity, not an estimate. -/
theorem pairHaarTransportedGroundStateSpatialLinkProjection_residual_sum_smul
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    {ι : Type*} [Fintype ι]
    (v : ι → PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (a : ι → ℝ) :
    (∑ i : ι, a i •
       (v i - pairHaarTransportedGroundStateSpatialLinkProjection
           H N hN beta hbeta e (v i))) =
      (∑ i : ι, a i • v i) -
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (∑ i : ι, a i • v i) := by
  classical
  rw [pairHaarTransportedGroundStateSpatialLinkProjection_sum_smul]
  simp only [smul_sub, Finset.sum_sub_distrib]

/-- Full Rayleigh form = genuine full-link posterior residual sum of the
single combined pair-Haar vector. Every cross term remains present. -/
theorem pairHaarSpatialLinkResidualGram_rayleigh_combined
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (v : ι → PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (a : ι → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H N hN beta hbeta v) a) =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖(∑ i : ι, a i • v i) -
          pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
            (∑ i : ι, a i • v i)‖ ^ 2 := by
  rw [pairHaarSpatialLinkResidualGram_rayleigh]
  apply Finset.sum_congr rfl
  intro e _he
  rw [pairHaarTransportedGroundStateSpatialLinkProjection_residual_sum_smul]

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

/-- The ACTUAL right Krylov Gram matrix sees one combined pair-Haar
physical receiver at the frozen beta(n), for any finite real coefficients. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_combined
    (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) =
      ∑ e : Link,
        ‖(∑ j : Fin (r + 1), a j • VR (j : ℕ)) -
          Q e (∑ j : Fin (r + 1), a j • VR (j : ℕ))‖ ^ 2 := by
  exact pairHaarSpatialLinkResidualGram_rayleigh_combined
    Hn 2 Pos (beta n) (hbeta n)
    (fun j : Fin (r + 1) => VR (j : ℕ)) a

/-- Three actual fine left Gram-Schmidt modes enjoy the same full-vector
Rayleigh identity for every real linear combination of the true receivers. -/
theorem fineLeftThreeModePairHaarResidualGram_rayleigh_combined
    (a : Fin 3 → ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec (fineLeftThreeModePairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) =
      ∑ e : Link,
        ‖(∑ k : Fin 3, a k • VL k) -
          Q e (∑ k : Fin 3, a k • VL k)‖ ^ 2 := by
  exact pairHaarSpatialLinkResidualGram_rayleigh_combined
    Hn 2 Pos (beta n) (hbeta n) (fun k : Fin 3 => VL k) a

end ActualAdjacentOrbit
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
