import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFineRightCenteredGramWeightedRayleigh
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveBetaOrthogonalReceiverExact
import Mathlib.Tactic

/-!
# P4-Q2: original uncentered right Gram versus exact vacuum/excitation sectors

PR #5314 controls the centered fine-right physical Krylov Gram with its
original frozen-beta Wilson posterior. We now restore the ACTUAL uncentered
right Krylov family rather than silently identifying it with the centered one.

Every combined physical input F admits its exact Hilbert decomposition
  F = inner(u,F) • u + F_perp
where u is the ORIGINAL constant physical Haar unit.
The true positive-beta signed receiver V_beta and the original transported
posterior projection Q_beta,e are linear. Their residuals therefore split,
linkwise, into a constant-input receiver residual and a centered-excitation
receiver residual, with the cross term controlled by Hilbert norm geometry.

Consequently the TRUE uncentered right-Krylov Gram Rayleigh form is bounded by

  2 * [inner(u,sum_j a_j R_j)^2 * E_beta(V_beta u)
       + |Links(H)| * (C_H(beta_frozen)
                        * sum_j |a_j| j M_H(beta_fine))^2].

Here E_beta(V_beta u) is the actual ORIGINAL positive-beta unit-receiver
posterior residual, NOT the beta-zero vacuum energy E_beta(U_beta 1).
The two are deliberately not conflated. Explicit control of their
difference is a separate next step. All finite-H and link-count
dependencies are visible. No Dobrushin, replacement posterior, uniform
volume or continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

/-- Elementary sharp factor-two Hilbert bound for the cross term. -/
private theorem p4_uncentered_norm_add_sq_le_two
    {E : Type*} [NormedAddCommGroup E]
    (x y : E) :
    ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have h := norm_add_le x y
  have hpow : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  have halg : (‖x‖ + ‖y‖) ^ 2 ≤
      2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  exact hpow.trans halg

local instance p4UncenteredTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4UncenteredCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4UncenteredSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4UncenteredMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4UncenteredBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4UncenteredLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The genuine positive-beta residual energy of the physical CONSTANT
INPUT after applying the original signed normalized receiver, with no
replacement by the beta-zero-anchored half-density vacuum. -/
noncomputable def physicalOriginalUnitReceiverFullLinkEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : ℝ :=
  ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
    ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) -
      pairHaarTransportedGroundStateSpatialLinkProjection
        H N hN beta hbeta e
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N))‖ ^ 2

theorem physicalOriginalUnitReceiverFullLinkEnergy_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 ≤ physicalOriginalUnitReceiverFullLinkEnergy H N hN beta hbeta := by
  unfold physicalOriginalUnitReceiverFullLinkEnergy
  apply Finset.sum_nonneg
  intro e _he
  exact sq_nonneg _

/-- Constant-orthogonal projection respects a finite real linear
combination of ACTUAL physical inputs, using the mathlib real-inner
continuous linear functional and the original norm-one constant u. -/
theorem physicalConstantOrthogonalComponent_sum_smul
    (H N : ℕ)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ) :
    physicalConstantOrthogonalComponent H N (∑ i : ι, a i • f i) =
      ∑ i : ι, a i • physicalConstantOrthogonalComponent H N (f i) := by
  classical
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  have hInner :
      inner ℝ u (∑ i : ι, a i • f i) =
        ∑ i : ι, a i * inner ℝ u (f i) := by
    calc
      inner ℝ u (∑ i : ι, a i • f i) =
          ∑ i : ι, inner ℝ u (a i • f i) := by
        exact map_sum (innerₛₗ ℝ u) _ _
      _ = ∑ i : ι, a i * inner ℝ u (f i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact real_inner_smul_right u (f i) (a i)
  change
    (∑ i : ι, a i • f i) -
      (inner ℝ u (∑ i : ι, a i • f i)) • u =
    ∑ i : ι, a i • (f i - (inner ℝ u (f i)) • u)
  rw [hInner]
  simp only [smul_sub, smul_smul, Finset.sum_sub_distrib, Finset.sum_smul]

/-- A genuine all-link residual of the original physical receiver splits
into the unit-receiver residual plus the constant-orthogonal receiver.
The cross term is bounded, not discarded. The coefficient 2 is the exact
general Hilbert inequality, with NO volume or number-of-modes factor. -/
theorem pairHaarPhysicalFamily_rayleigh_le_unitReceiver_and_orthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ) :
    star a ⬝ᵥ
        (Matrix.mulVec
          (pairHaarSpatialLinkResidualGram H N hN beta hbeta
            (fun i : ι =>
              normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta (f i))) a) ≤
      2 * ((inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
          (∑ i : ι, a i • f i)) ^ 2 *
        physicalOriginalUnitReceiverFullLinkEnergy H N hN beta hbeta +
        physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy
          H N hN beta hbeta
          (physicalConstantOrthogonalComponent H N (∑ i : ι, a i • f i))) := by
  classical
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let F := ∑ i : ι, a i • f i
  let g := physicalConstantOrthogonalComponent H N F
  let c : ℝ := inner ℝ u F
  let V := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta
  have hsplit : F = c • u + g :=
    physicalInput_eq_constant_add_orthogonal H N F
  let L := normalizedPhysicalOneSlabPairHaarReceiverLinearMap H N hN beta hbeta
  have hV : V F = c • V u + V g := by
    have hlinear : L F = c • L u + L g := by
      rw [hsplit, map_add, map_smul]
    simpa only [L, normalizedPhysicalOneSlabPairHaarReceiverLinearMap_apply] using hlinear
  have hOrth : inner ℝ u g = 0 :=
    physicalConstantOrthogonalComponent_inner_zero H N F
  have hEnergy :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖V g - Q e (V g)‖ ^ 2) =
      physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy H N hN beta hbeta g :=
    normalizedPhysicalOneSlabPairHaarReceiver_beta_fullResidual_eq_receiverDrift_of_orthogonal
      H N hN beta hbeta g hOrth
  have hOne (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      ‖V F - Q e (V F)‖ ^ 2 ≤
        2 * (c ^ 2 * ‖V u - Q e (V u)‖ ^ 2 +
          ‖V g - Q e (V g)‖ ^ 2) := by
    have hQ : Q e (V F) = c • Q e (V u) + Q e (V g) := by
      have hAdd :
          Q e (c • V u + V g) = Q e (c • V u) + Q e (V g) :=
        pairHaarTransportedGroundStateSpatialLinkProjection_add
          H N hN beta hbeta e (c • V u) (V g)
      have hSmul : Q e (c • V u) = c • Q e (V u) :=
        pairHaarTransportedGroundStateSpatialLinkProjection_smul
          H N hN beta hbeta e c (V u)
      calc
        Q e (V F) = Q e (c • V u + V g) := by rw [hV]
        _ = Q e (c • V u) + Q e (V g) := hAdd
        _ = c • Q e (V u) + Q e (V g) := by rw [hSmul]
    have hResidual : V F - Q e (V F) =
        c • (V u - Q e (V u)) + (V g - Q e (V g)) := by
      rw [hQ, hV, smul_sub]
      abel
    have hTwo := p4_uncentered_norm_add_sq_le_two
      (c • (V u - Q e (V u))) (V g - Q e (V g))
    have hScale :
        ‖c • (V u - Q e (V u))‖ ^ 2 =
          c ^ 2 * ‖V u - Q e (V u)‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    calc
      ‖V F - Q e (V F)‖ ^ 2 =
          ‖c • (V u - Q e (V u)) + (V g - Q e (V g))‖ ^ 2 := by
        rw [hResidual]
      _ ≤ 2 * (‖c • (V u - Q e (V u))‖ ^ 2 +
          ‖V g - Q e (V g)‖ ^ 2) := hTwo
      _ = 2 * (c ^ 2 * ‖V u - Q e (V u)‖ ^ 2 +
          ‖V g - Q e (V g)‖ ^ 2) := by rw [hScale]
  have hSum :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖V F - Q e (V F)‖ ^ 2) ≤
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        2 * (c ^ 2 * ‖V u - Q e (V u)‖ ^ 2 +
          ‖V g - Q e (V g)‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro e _he
    exact hOne e
  have hReorder :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        2 * (c ^ 2 * ‖V u - Q e (V u)‖ ^ 2 +
          ‖V g - Q e (V g)‖ ^ 2)) =
      2 * (c ^ 2 *
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ‖V u - Q e (V u)‖ ^ 2) +
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ‖V g - Q e (V g)‖ ^ 2)) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hRay := pairHaarSpatialLinkResidualGram_rayleigh_physicalInput
    H N hN beta hbeta f a
  have hBound :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖V F - Q e (V F)‖ ^ 2) ≤
      2 * (c ^ 2 *
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ‖V u - Q e (V u)‖ ^ 2) +
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ‖V g - Q e (V g)‖ ^ 2)) :=
    hSum.trans_eq hReorder
  have hUnit :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖V u - Q e (V u)‖ ^ 2) =
      physicalOriginalUnitReceiverFullLinkEnergy H N hN beta hbeta := rfl
  rw [hUnit, hEnergy] at hBound
  rw [hRay]
  change (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
    ‖V F - Q e (V F)‖ ^ 2) ≤
      2 * (c ^ 2 * physicalOriginalUnitReceiverFullLinkEnergy
        H N hN beta hbeta +
      physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy
        H N hN beta hbeta g)
  exact hBound

/-- FINALLY the ORIGINAL UN-CENTERED fine-right Krylov residual Gram,
not the centered Gram of #5314, is bounded by its true unit-receiver
posterior loss and an explicit TWO-beta weighted physical excitation
budget. No spurious equality with the centered Gram or beta-zero vacuum. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_unitReceiver_weightedTwoBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r) a) ≤
      2 * ((inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
          (halfExtent (n + 1)) 2)
        (∑ j : Fin (r + 1), a j •
          physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n (j : ℕ))) ^ 2 *
        physicalOriginalUnitReceiverFullLinkEnergy
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) +
        (Fintype.card
          (PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : ℝ) *
          (physicalOriginalOrthogonalReceiverBetaLipschitzBudget
              (halfExtent (n + 1)) (beta n) *
            (∑ j : Fin (r + 1), |a j| *
              ((j : ℝ) *
                physicalOriginalNormalizedTransferConstantStepBetaBudget
                  (halfExtent (n + 1)) (beta (n + 1))))) ^ 2) := by
  classical
  let H := halfExtent (n + 1)
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let f : Fin (r + 1) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    fun j => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ)
  let F := ∑ j : Fin (r + 1), a j • f j
  let g := physicalConstantOrthogonalComponent H 2 F
  let C := physicalOriginalOrthogonalReceiverBetaLipschitzBudget H (beta n)
  let M := physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n + 1))
  let W : ℝ := ∑ j : Fin (r + 1), |a j| * ((j : ℝ) * M)
  have hGeneric :
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
      2 * ((inner ℝ u F) ^ 2 *
        physicalOriginalUnitReceiverFullLinkEnergy
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) +
        physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) g) := by
    simpa only [fineRightKrylovPairHaarResidualGram, f, F, H, u, g] using
      (pairHaarPhysicalFamily_rayleigh_le_unitReceiver_and_orthogonal
        H 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) f a)
  have hGsum :
      g = ∑ j : Fin (r + 1), a j •
        fineRightConstantOrthogonalKrylovInput
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ) := by
    simpa only [g, f, F, H, fineRightConstantOrthogonalKrylovInput] using
      (physicalConstantOrthogonalComponent_sum_smul H 2 f a)
  have hGnorm : ‖g‖ ≤ W := by
    rw [hGsum]
    simpa only [W, M, H] using
      (fineRightCenteredKrylovCombination_norm_le_weightedFineBeta
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a)
  have hOrth : inner ℝ u g = 0 :=
    physicalConstantOrthogonalComponent_inner_zero H 2 F
  have hEnergy :
      physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) g ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        (C * ‖g‖) ^ 2 :=
    physicalOrthogonalReceiverBetaZeroDriftFullLinkEnergy_le_explicitBetaSquared
      H 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n) g hOrth
  have hC : 0 ≤ C :=
    physicalOriginalOrthogonalReceiverBetaLipschitzBudget_nonneg H (beta n) (hbeta n)
  have hCW : C * ‖g‖ ≤ C * W :=
    mul_le_mul_of_nonneg_left hGnorm hC
  have hSq : (C * ‖g‖) ^ 2 ≤ (C * W) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hC (norm_nonneg g)) hCW 2
  have hCentered :
      physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) g ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        (C * W) ^ 2 :=
    hEnergy.trans (mul_le_mul_of_nonneg_left hSq (Nat.cast_nonneg _))
  change star a ⬝ᵥ
      (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
    2 * ((inner ℝ u F) ^ 2 *
      physicalOriginalUnitReceiverFullLinkEnergy
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) +
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        (C * W) ^ 2)
  exact hGeneric.trans
    (mul_le_mul_of_nonneg_left
      (add_le_add_right hCentered _) (by norm_num))

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
