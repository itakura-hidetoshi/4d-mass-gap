import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveBetaOrthogonalReceiverExplicitBetaSquared
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarBetaZeroRightKrylovCollapse
import Mathlib.Tactic

/-!
# P4-Q2: genuine fine-right Krylov orbit orthogonal leakage, separate couplings

PR #5311 proves an explicit O_H(beta_frozen^2) bound for the TRUE
physical positive-beta receiver on constant-orthogonal input.
The actual adjacent fine-right Krylov vector is NOT in general orthogonal:
  R(n,r) = S_(H,n+1,beta(n+1))^r u_H.

Here we keep the distinct FINE beta(n+1) and FROZEN beta(n) strictly
separate. The mathlib contraction norm for the normalized physical
one-slab operator, together with an exact telescope around the
physical constant reference unit u_H, gives

  ||R(n,r) - u_H|| <= r ||S_fine u_H - u_H||.

An exact real Hilbert Pythagoras shows that removing the physical
constant Fourier component cannot increase this distance. Therefore
the REAL centered physical right Krylov input R(n,r)^\perp obeys the
same bound with coefficient one (no factor two).

Combining with #5311:
  A_frozen(R(n,r)^\perp)
    <= |SpatialLinks(H)| *
       (C_H(beta(n)) * r * ||S_fine u_H-u_H||)^2,
  C_H(beta) = m_H(beta)^(-2) B_H beta.

No claim is made for the uncentered full right Gram diagonal, where
the genuine vacuum term also contributes. No volume-uniform estimate,
no Dobrushin, no substitute receiver or posterior, and no continuum
mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

/-- Telescoping a norm-one contraction around any reference vector,
without falsely assuming that the reference is fixed at positive beta.
This is an exact finite-depth bound independent of the ambient dimension. -/
private theorem p4_norm_pow_sub_reference_le_depth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : E →L[ℝ] E) (hS : ‖S‖ ≤ 1) (u : E) (r : ℕ) :
    ‖(S ^ r) u - u‖ ≤ (r : ℝ) * ‖S u - u‖ := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      have hstep :
          (S ^ (r + 1)) u - u =
            S ((S ^ r) u - u) + (S u - u) := by
        rw [pow_succ', ContinuousLinearMap.mul_apply, map_sub]
        abel
      have hcontraction :
          ‖S ((S ^ r) u - u)‖ ≤ ‖(S ^ r) u - u‖ := by
        calc
          ‖S ((S ^ r) u - u)‖ ≤
              ‖S‖ * ‖(S ^ r) u - u‖ :=
            ContinuousLinearMap.le_opNorm S _
          _ ≤ 1 * ‖(S ^ r) u - u‖ :=
            mul_le_mul_of_nonneg_right hS (norm_nonneg _)
          _ = ‖(S ^ r) u - u‖ := one_mul _
      calc
        ‖(S ^ (r + 1)) u - u‖ =
            ‖S ((S ^ r) u - u) + (S u - u)‖ := by rw [hstep]
        _ ≤ ‖S ((S ^ r) u - u)‖ + ‖S u - u‖ :=
          norm_add_le _ _
        _ ≤ ‖(S ^ r) u - u‖ + ‖S u - u‖ :=
          add_le_add_right hcontraction _
        _ ≤ (r : ℝ) * ‖S u - u‖ + ‖S u - u‖ :=
          add_le_add_right ih _
        _ = ((r + 1 : ℕ) : ℝ) * ‖S u - u‖ := by
          push_cast
          ring

local instance p4FineDepthTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4FineDepthCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4FineDepthSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4FineDepthMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4FineDepthBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4FineDepthLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The true physical constant-orthogonal component is the closest
part of f-u to the constant-orthogonal sector: no factor 2.
The proof uses the orthogonal decomposition and the norm-squared
Pythagoras theorem from the real mathlib Hilbert-space API. -/
theorem physicalConstantOrthogonalComponent_norm_le_sub_constant
    (H N : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖physicalConstantOrthogonalComponent H N f‖ ≤
      ‖f - periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N‖ := by
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let g := physicalConstantOrthogonalComponent H N f
  let c : ℝ := inner ℝ u f
  have hsplit : f = c • u + g :=
    physicalInput_eq_constant_add_orthogonal H N f
  have horth : inner ℝ u g = 0 :=
    physicalConstantOrthogonalComponent_inner_zero H N f
  have hsub : f - u = (c - 1) • u + g := by
    calc
      f - u = (c • u + g) - u := by rw [hsplit]
      _ = (c - 1) • u + g := by
        rw [sub_smul, one_smul]
        abel
  have hcross : inner ℝ ((c - 1) • u) g = 0 := by
    rw [real_inner_smul_left, horth]
    ring
  have hpyth :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      ((c - 1) • u) g hcross
  rw [← hsub] at hpyth
  nlinarith [sq_nonneg (‖(c - 1) • u‖),
    norm_nonneg g, norm_nonneg (f - u)]

/-- An explicit ORIGINAL frozen-beta receiver estimate for the
constant-orthogonal part of ANY physical input: the distance to the
fixed beta-zero constant reference controls the excitation energy. -/
theorem physicalCenteredInputReceiverFullLinkEnergy_le_distance
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy H N hN beta hbeta
      (physicalConstantOrthogonalComponent H N f) ≤
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
      (physicalOriginalOrthogonalReceiverBetaLipschitzBudget H beta *
        ‖f - periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N‖) ^ 2 := by
  let g := physicalConstantOrthogonalComponent H N f
  let C := physicalOriginalOrthogonalReceiverBetaLipschitzBudget H beta
  have hG :
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) g = 0 :=
    physicalConstantOrthogonalComponent_inner_zero H N f
  have hInitial :
      physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy H N hN beta hbeta g ≤
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          (C * ‖g‖) ^ 2 := by
    simpa only [C, g] using
      (physicalOrthogonalReceiverBetaZeroDriftFullLinkEnergy_le_explicitBetaSquared
        H N hN beta hbeta g hG)
  have hGNorm : ‖g‖ ≤
      ‖f - periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N‖ :=
    physicalConstantOrthogonalComponent_norm_le_sub_constant H N f
  have hC : 0 ≤ C :=
    physicalOriginalOrthogonalReceiverBetaLipschitzBudget_nonneg H beta hbeta
  have hMul := mul_le_mul_of_nonneg_left hGNorm hC
  have hSq : (C * ‖g‖) ^ 2 ≤
      (C * ‖f -
        periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N‖) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hC (norm_nonneg g)) hMul 2
  exact hInitial.trans
    (mul_le_mul_of_nonneg_left hSq (Nat.cast_nonneg _))

/-- In the ACTUAL fine-right orbit the normalized fine physical
transfer is a contraction; the reference unit is the beta-zero
physical Haar vacuum, and beta(n+1) remains distinct from beta(n). -/
theorem fineRightFactor_norm_sub_constant_le_depth_stepDefect
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) :
    ‖physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r -
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
        (halfExtent (n + 1)) 2‖ ≤
      (r : ℝ) *
        ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta (n + 1)) (hbeta (n + 1))
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
              (halfExtent (n + 1)) 2) -
          periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
            (halfExtent (n + 1)) 2‖ := by
  let H := halfExtent (n + 1)
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive
    (beta (n + 1)) (hbeta (n + 1))
  have hS : ‖S‖ ≤ 1 := by
    rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
      H 2 specialUnitaryTwoWilsonRankPositive
      (beta (n + 1)) (hbeta (n + 1))]
  change ‖(S ^ r) u - u‖ ≤ (r : ℝ) * ‖S u - u‖
  exact p4_norm_pow_sub_reference_le_depth S hS u r

/-- The ACTUAL fine-right Krylov input, centered against the same
physical Haar constant on the fine slice, without changing the
frozen Wilson posterior or the fine transfer. -/
noncomputable def fineRightConstantOrthogonalKrylovInput
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent (n + 1)) 2 :=
  physicalConstantOrthogonalComponent (halfExtent (n + 1)) 2
    (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r)

/-- Centering is EXACTLY orthogonal to the real physical constant unit. -/
theorem fineRightConstantOrthogonalKrylovInput_inner_zero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) :
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
        (halfExtent (n + 1)) 2)
      (fineRightConstantOrthogonalKrylovInput
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) = 0 := by
  exact physicalConstantOrthogonalComponent_inner_zero
    (halfExtent (n + 1)) 2
    (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r)

/-- The actual fine-right constant-orthogonal leakage grows at most
linearly with the exact original fine-transfer one-step vacuum defect. -/
theorem fineRightConstantOrthogonalKrylovInput_norm_le_depth_stepDefect
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) :
    ‖fineRightConstantOrthogonalKrylovInput
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r‖ ≤
      (r : ℝ) *
        ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta (n + 1)) (hbeta (n + 1))
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
              (halfExtent (n + 1)) 2) -
          periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
            (halfExtent (n + 1)) 2‖ := by
  let H := halfExtent (n + 1)
  let f := physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r
  exact (physicalConstantOrthogonalComponent_norm_le_sub_constant H 2 f).trans
    (fineRightFactor_norm_sub_constant_le_depth_stepDefect
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)

/-- Actual fine-right orthogonal mode, but the ORIGINAL distinct
FROZEN beta(n) receiver/projection: no fictitious identification of
beta(n) with beta(n+1), nor an all-volume uniform claim. -/
theorem fineRightConstantOrthogonalKrylovInput_frozenReceiverEnergy_le_depth
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) :
    physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n)
        (fineRightConstantOrthogonalKrylovInput
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) ≤
      (Fintype.card
        (PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : ℝ) *
      (physicalOriginalOrthogonalReceiverBetaLipschitzBudget
          (halfExtent (n + 1)) (beta n) *
        ((r : ℝ) *
          ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
              (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
              (beta (n + 1)) (hbeta (n + 1))
              (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
                (halfExtent (n + 1)) 2) -
            periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
              (halfExtent (n + 1)) 2‖)) ^ 2 := by
  let H := halfExtent (n + 1)
  let g := fineRightConstantOrthogonalKrylovInput
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r
  let C := physicalOriginalOrthogonalReceiverBetaLipschitzBudget H (beta n)
  let δ : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive
          (beta (n + 1)) (hbeta (n + 1))
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) -
        periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2‖
  have horth : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) g = 0 :=
    fineRightConstantOrthogonalKrylovInput_inner_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r
  have hEnergy :=
    physicalOrthogonalReceiverBetaZeroDriftFullLinkEnergy_le_explicitBetaSquared
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) g horth
  have hDepth : ‖g‖ ≤ (r : ℝ) * δ :=
    fineRightConstantOrthogonalKrylovInput_norm_le_depth_stepDefect
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have hC : 0 ≤ C :=
    physicalOriginalOrthogonalReceiverBetaLipschitzBudget_nonneg H (beta n) (hbeta n)
  have hMul : C * ‖g‖ ≤ C * ((r : ℝ) * δ) :=
    mul_le_mul_of_nonneg_left hDepth hC
  have hSq : (C * ‖g‖) ^ 2 ≤ (C * ((r : ℝ) * δ)) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hC (norm_nonneg g)) hMul 2
  exact hEnergy.trans
    (mul_le_mul_of_nonneg_left hSq (Nat.cast_nonneg _))

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
