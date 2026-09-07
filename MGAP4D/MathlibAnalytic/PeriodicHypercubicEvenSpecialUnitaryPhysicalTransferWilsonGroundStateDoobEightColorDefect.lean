import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateBoundaryProjection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonMarginalCondExpComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 1000000

/-- The old physical-descent interface is substantially stronger than a mere
carrier realization.  For every color it forces the feature analysis to kill
the corresponding physical residual.

This audit theorem is useful when deciding whether a proposed concrete
`WilsonMarginalCondExpComparisonData` can exist: an exact color intertwining
with a coarser projection fixed by that color implies `A (x - P_c x) = 0`. -/
theorem WilsonMarginalCondExpComparisonData.analysis_residual_eq_zero
    {G H C : Type*}
    [NormedAddCommGroup G]
    [InnerProductSpace ℝ G]
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace G]
    [CompleteSpace H]
    [Fintype C]
    (P : C → G →L[ℝ] G)
    (A : G →L[ℝ] H)
    (D : WilsonMarginalCondExpComparisonData P A)
    (c : C)
    (x : G) :
    A (x - P c x) = 0 := by
  let u : G := x - P c x
  let y : D.Marginal := D.lift x
  let q : D.Marginal := D.marginalCondExp (D.lift u)
  have hliftResidual : D.lift u = y - D.marginalColor c y := by
    dsimp [u, y]
    rw [map_sub, D.lift_color_intertwining]
  have hqfixed : D.marginalColor c q = q := by
    simpa [q] using D.coarse_fixed_by_color c u
  have horth : inner ℝ (D.lift u) q = 0 := by
    rw [hliftResidual, inner_sub_left]
    have hs := D.color_symmetric c y q
    rw [hqfixed] at hs
    exact sub_eq_zero.mpr hs.symm
  have hQq : D.marginalCondExp q = q := by
    have h := congrArg
      (fun R : D.Marginal →L[ℝ] D.Marginal => R (D.lift u))
      D.coarse_idempotent
    simpa [q] using h
  have hinner : inner ℝ (D.lift u) q = inner ℝ q q := by
    have hs := D.coarse_symmetric (D.lift u) q
    rw [hQq] at hs
    simpa [q] using hs.symm
  have hqnorm : ‖q‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    rw [← hinner, horth]
  have hAuSq : ‖A u‖ ^ 2 = 0 := by
    rw [← D.coarse_norm_sq u]
    simpa [q] using hqnorm
  have hAu : ‖A u‖ = 0 := by
    nlinarith [norm_nonneg (A u)]
  exact norm_eq_zero.mp hAu

/-- Equivalently, every color operator admitted by the old exact-descent
interface is invisible to the analysis map: `A (P_c x) = A x`. -/
theorem WilsonMarginalCondExpComparisonData.analysis_color_eq
    {G H C : Type*}
    [NormedAddCommGroup G]
    [InnerProductSpace ℝ G]
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace G]
    [CompleteSpace H]
    [Fintype C]
    (P : C → G →L[ℝ] G)
    (A : G →L[ℝ] H)
    (D : WilsonMarginalCondExpComparisonData P A)
    (c : C)
    (x : G) :
    A (P c x) = A x := by
  have hzero := D.analysis_residual_eq_zero P A c x
  have hmap : A (x - P c x) = A x - A (P c x) := by
    rw [map_sub]
  rw [hmap] at hzero
  exact sub_eq_zero.mp hzero |>.symm

/-- Correct squared-defect comparison when the color conditional expectations
are kept on the genuine marginal Hilbert carrier instead of being forced to
descend to physical projections.

The lift only has to be isometric.  If every color projection fixes the coarse
conditional-expectation image, Pythagoras gives the marginal color energy
below the squared defect of the target operator `S`. -/
theorem boundedColorMarginalResidualEnergy_le_squaredDefect_of_isometricLift
    {G M C : Type*}
    [NormedAddCommGroup G]
    [InnerProductSpace ℝ G]
    [NormedAddCommGroup M]
    [InnerProductSpace ℝ M]
    [Fintype C]
    [Nonempty C]
    (L : G →L[ℝ] M)
    (hL : ∀ x, ‖L x‖ ^ 2 = ‖x‖ ^ 2)
    (P : C → M →L[ℝ] M)
    (hPid : ∀ c, (P c).comp (P c) = P c)
    (hPsymm : ∀ c, ((P c : M →L[ℝ] M) : M →ₗ[ℝ] M).IsSymmetric)
    (Q : M →L[ℝ] M)
    (hQid : Q.comp Q = Q)
    (hQsymm : (Q : M →ₗ[ℝ] M).IsSymmetric)
    (S : G →L[ℝ] G)
    (hfixed : ∀ c x, P c (Q (L x)) = Q (L x))
    (hcoarse : ∀ x, ‖Q (L x)‖ ^ 2 = ‖S x‖ ^ 2)
    (x : G) :
    boundedColorNormalizedResidualEnergy P (L x) ≤
      ‖x‖ ^ 2 - ‖S x‖ ^ 2 := by
  have hMarginal :=
    boundedColorNormalizedResidualEnergy_le_coarseProjectionResidual_sq
      P hPid hPsymm Q (L x) (fun c => hfixed c x)
  have hPyth :=
    realHilbert_idempotent_symmetric_residual_sq_eq_defect
      Q hQid hQsymm (L x)
  calc
    boundedColorNormalizedResidualEnergy P (L x) ≤
        ‖L x - Q (L x)‖ ^ 2 := hMarginal
    _ = ‖L x‖ ^ 2 - ‖Q (L x)‖ ^ 2 := hPyth
    _ = ‖x‖ ^ 2 - ‖S x‖ ^ 2 := by rw [hL, hcoarse]

/-- A coefficient `eta ∈ [0,1]` may be retained without changing the exact
marginal theorem. -/
theorem eta_mul_boundedColorMarginalResidualEnergy_le_squaredDefect_of_isometricLift
    {G M C : Type*}
    [NormedAddCommGroup G]
    [InnerProductSpace ℝ G]
    [NormedAddCommGroup M]
    [InnerProductSpace ℝ M]
    [Fintype C]
    [Nonempty C]
    (L : G →L[ℝ] M)
    (hL : ∀ x, ‖L x‖ ^ 2 = ‖x‖ ^ 2)
    (P : C → M →L[ℝ] M)
    (hPid : ∀ c, (P c).comp (P c) = P c)
    (hPsymm : ∀ c, ((P c : M →L[ℝ] M) : M →ₗ[ℝ] M).IsSymmetric)
    (Q : M →L[ℝ] M)
    (hQid : Q.comp Q = Q)
    (hQsymm : (Q : M →ₗ[ℝ] M).IsSymmetric)
    (S : G →L[ℝ] G)
    (hfixed : ∀ c x, P c (Q (L x)) = Q (L x))
    (hcoarse : ∀ x, ‖Q (L x)‖ ^ 2 = ‖S x‖ ^ 2)
    (eta : ℝ)
    (heta0 : 0 ≤ eta)
    (heta1 : eta ≤ 1)
    (x : G) :
    eta * boundedColorNormalizedResidualEnergy P (L x) ≤
      ‖x‖ ^ 2 - ‖S x‖ ^ 2 := by
  have hmain :=
    boundedColorMarginalResidualEnergy_le_squaredDefect_of_isometricLift
      L hL P hPid hPsymm Q hQid hQsymm S hfixed hcoarse x
  have hE0 := boundedColorNormalizedResidualEnergy_nonneg P (L x)
  have hetaE :
      eta * boundedColorNormalizedResidualEnergy P (L x) ≤
        boundedColorNormalizedResidualEnergy P (L x) := by
    nlinarith
  exact hetaE.trans hmain

section GroundStateDoobMarginal

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "V" =>
  Lp ℝ 2
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
      H N hN beta hbeta)
local notation "J" =>
  Lp ℝ 2
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta)
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
    H N hN beta hbeta
local notation "Q" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp
    H N hN beta hbeta
local notation "D" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobBoundaryOperator
    H N hN beta hbeta
local notation "Color" => Fin 8

/-- The right-boundary pullback, viewed as a continuous linear isometric lift
into the genuine ground-state one-slab joint Hilbert carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift :
    V →L[ℝ] J :=
  R.toContinuousLinearMap

/-- Exact norm-square preservation of the ground-state right-boundary lift. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift_norm_sq
    (u : V) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
        H N hN beta hbeta u‖ ^ 2 = ‖u‖ ^ 2 := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift]
  rw [R.norm_map]

/-- Any genuine eight-color orthogonal conditional-expectation family on the
joint law whose fixed ranges contain the coarse left-boundary image has its
normalized residual energy bounded by the exact Doob squared defect.

No physical-carrier descent is assumed or needed. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidual_le_doobDefect
    (P : Color → J →L[ℝ] J)
    (hPid : ∀ c, (P c).comp (P c) = P c)
    (hPsymm : ∀ c, ((P c : J →L[ℝ] J) : J →ₗ[ℝ] J).IsSymmetric)
    (hfixed : ∀ c u,
      P c (Q (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
        H N hN beta hbeta u)) =
        Q (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
          H N hN beta hbeta u))
    (u : V) :
    boundedColorNormalizedResidualEnergy P
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
          H N hN beta hbeta u) ≤
      ‖u‖ ^ 2 - ‖D u‖ ^ 2 := by
  apply boundedColorMarginalResidualEnergy_le_squaredDefect_of_isometricLift
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift_norm_sq
      H N hN beta hbeta)
    P hPid hPsymm Q
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_idempotent
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_inner_symm
      H N hN beta hbeta)
    D hfixed
  intro v
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift]
  have hnorm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_rightBoundary_norm
      H N hN beta hbeta v
  nlinarith [norm_nonneg (Q (R v)), norm_nonneg (D v)]

/-- The same concrete Doob comparison with a retained loss factor
`eta ∈ [0,1]`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidual_eta_le_doobDefect
    (P : Color → J →L[ℝ] J)
    (hPid : ∀ c, (P c).comp (P c) = P c)
    (hPsymm : ∀ c, ((P c : J →L[ℝ] J) : J →ₗ[ℝ] J).IsSymmetric)
    (hfixed : ∀ c u,
      P c (Q (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
        H N hN beta hbeta u)) =
        Q (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
          H N hN beta hbeta u))
    (eta : ℝ)
    (heta0 : 0 ≤ eta)
    (heta1 : eta ≤ 1)
    (u : V) :
    eta * boundedColorNormalizedResidualEnergy P
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
          H N hN beta hbeta u) ≤
      ‖u‖ ^ 2 - ‖D u‖ ^ 2 := by
  have hmain :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidual_le_doobDefect
      H N hN beta hbeta P hPid hPsymm hfixed u
  have hE0 := boundedColorNormalizedResidualEnergy_nonneg P
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
      H N hN beta hbeta u)
  have hetaE :
      eta * boundedColorNormalizedResidualEnergy P
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
            H N hN beta hbeta u) ≤
        boundedColorNormalizedResidualEnergy P
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
            H N hN beta hbeta u) := by
    nlinarith
  exact hetaE.trans hmain

end GroundStateDoobMarginal

end

end MathlibAnalytic
end MGAP4D
