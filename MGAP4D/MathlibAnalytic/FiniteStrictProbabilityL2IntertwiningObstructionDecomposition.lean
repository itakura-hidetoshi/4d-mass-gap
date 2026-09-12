import MGAP4D.MathlibAnalytic.FiniteStrictProbabilityL2ConditionalExpectationCompression
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

namespace FiniteStrictProbabilityMap

variable
    {X Y : Type}
    [Fintype X]
    [Fintype Y]
    {P : FiniteStrictProbabilityL2Data X}
    {Q : FiniteStrictProbabilityL2Data Y}

/-- Difference between the operator obtained by exact finite-probability
compression and an independently supplied target operator. -/
noncomputable def compressionDiscrepancyLinearMap
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (B : FiniteProbabilityL2Carrier Y →L[ℝ]
      FiniteProbabilityL2Carrier Y) :
    FiniteProbabilityL2Carrier Y →ₗ[ℝ]
      FiniteProbabilityL2Carrier Y :=
  (M.compressContinuousLinearOperator A).toLinearMap - B.toLinearMap

@[simp] theorem compressionDiscrepancyLinearMap_apply
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (B : FiniteProbabilityL2Carrier Y →L[ℝ]
      FiniteProbabilityL2Carrier Y)
    (y : FiniteProbabilityL2Carrier Y) :
    M.compressionDiscrepancyLinearMap A B y =
      M.compressContinuousLinearOperator A y - B y :=
  rfl

/-- Leakage of source evolution out of the pulled-back coarse subspace.  It is
exactly the strong intertwining residual against the compressed operator itself:
`A U - U (E A U)`. -/
noncomputable def coarseSubspaceLeakageLinearMap
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X) :
    FiniteProbabilityL2Carrier Y →ₗ[ℝ]
      FiniteProbabilityL2Carrier X :=
  M.intertwiningResidualLinearMap A
    (M.compressContinuousLinearOperator A)

@[simp] theorem coarseSubspaceLeakageLinearMap_apply
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (y : FiniteProbabilityL2Carrier Y) :
    M.coarseSubspaceLeakageLinearMap A y =
      A (M.l2PullbackLinearMap y) -
        M.l2PullbackLinearMap (M.compressContinuousLinearOperator A y) :=
  rfl

/-- Leakage is invisible to coarse conditional expectation.  Equivalently it
lies in the orthogonal complement of the pulled-back coarse subspace. -/
theorem l2ConditionalExpectation_coarseSubspaceLeakage_eq_zero
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (y : FiniteProbabilityL2Carrier Y) :
    M.l2ConditionalExpectationLinearMap
        (M.coarseSubspaceLeakageLinearMap A y) = 0 := by
  change
    M.l2ConditionalExpectationLinearMap
      (A (M.l2PullbackLinearMap y) -
        M.l2PullbackLinearMap (M.compressContinuousLinearOperator A y)) = 0
  rw [map_sub, M.l2ConditionalExpectation_l2Pullback]
  change
    M.compressContinuousLinearOperator A y -
      M.compressContinuousLinearOperator A y = 0
  simp

/-- Exact algebraic decomposition of the strong intertwining residual into a
pulled-back compression discrepancy plus source-operator leakage. -/
theorem intertwiningResidual_decomposition
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (B : FiniteProbabilityL2Carrier Y →L[ℝ]
      FiniteProbabilityL2Carrier Y) :
    M.intertwiningResidualLinearMap A B =
      M.l2PullbackLinearMap.comp
          (M.compressionDiscrepancyLinearMap A B) +
        M.coarseSubspaceLeakageLinearMap A := by
  apply LinearMap.ext
  intro y
  change
    A (M.l2PullbackLinearMap y) - M.l2PullbackLinearMap (B y) =
      M.l2PullbackLinearMap
          (M.compressContinuousLinearOperator A y - B y) +
        (A (M.l2PullbackLinearMap y) -
          M.l2PullbackLinearMap (M.compressContinuousLinearOperator A y))
  rw [map_sub]
  abel

/-- Pointwise form of the exact strong-residual decomposition. -/
theorem intertwiningResidual_decomposition_apply
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (B : FiniteProbabilityL2Carrier Y →L[ℝ]
      FiniteProbabilityL2Carrier Y)
    (y : FiniteProbabilityL2Carrier Y) :
    M.intertwiningResidualLinearMap A B y =
      M.l2PullbackLinearMap (M.compressionDiscrepancyLinearMap A B y) +
        M.coarseSubspaceLeakageLinearMap A y := by
  exact LinearMap.congr_fun (M.intertwiningResidual_decomposition A B) y

/-- The two obstruction components are orthogonal.  The discrepancy component
is coarse-measurable, while leakage has zero conditional expectation. -/
theorem pullback_compressionDiscrepancy_inner_coarseSubspaceLeakage_eq_zero
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (B : FiniteProbabilityL2Carrier Y →L[ℝ]
      FiniteProbabilityL2Carrier Y)
    (y : FiniteProbabilityL2Carrier Y) :
    inner ℝ
        (M.l2PullbackLinearMap (M.compressionDiscrepancyLinearMap A B y))
        (M.coarseSubspaceLeakageLinearMap A y) = 0 := by
  rw [M.l2Pullback_adjoint_pairing]
  rw [M.l2ConditionalExpectation_coarseSubspaceLeakage_eq_zero]
  simp

/-- Exact Pythagorean identity for the strong intertwining obstruction.  This
separates target-operator mismatch from failure of coarse-subspace invariance. -/
theorem norm_sq_intertwiningResidual_eq_discrepancy_add_leakage
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (B : FiniteProbabilityL2Carrier Y →L[ℝ]
      FiniteProbabilityL2Carrier Y)
    (y : FiniteProbabilityL2Carrier Y) :
    ‖M.intertwiningResidualLinearMap A B y‖ ^ 2 =
      ‖M.compressionDiscrepancyLinearMap A B y‖ ^ 2 +
        ‖M.coarseSubspaceLeakageLinearMap A y‖ ^ 2 := by
  rw [M.intertwiningResidual_decomposition_apply A B y]
  rw [norm_add_sq_real]
  rw [M.pullback_compressionDiscrepancy_inner_coarseSubspaceLeakage_eq_zero
    A B y]
  rw [M.norm_sq_l2PullbackLinearMap]
  ring

/-- Compression discrepancy vanishes exactly when the compressed source
operator equals the supplied target operator. -/
theorem compressionDiscrepancyLinearMap_eq_zero_iff
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (B : FiniteProbabilityL2Carrier Y →L[ℝ]
      FiniteProbabilityL2Carrier Y) :
    M.compressionDiscrepancyLinearMap A B = 0 ↔
      M.compressContinuousLinearOperator A = B := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro y
    have hy := LinearMap.congr_fun h y
    change M.compressContinuousLinearOperator A y - B y = 0 at hy
    exact sub_eq_zero.mp hy
  · intro h
    apply LinearMap.ext
    intro y
    change M.compressContinuousLinearOperator A y - B y = 0
    rw [h]
    simp

/-- Source evolution preserves the pulled-back coarse subspace exactly when its
coarse projection fixes every evolved pulled-back vector. -/
def PullbackCoarseSubspaceInvariant
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X) : Prop :=
  ∀ y : FiniteProbabilityL2Carrier Y,
    M.l2CoarseProjectionLinearMap
        (A (M.l2PullbackLinearMap y)) =
      A (M.l2PullbackLinearMap y)

/-- Leakage vanishes exactly when the source operator preserves the pulled-back
coarse subspace. -/
theorem coarseSubspaceLeakageLinearMap_eq_zero_iff
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X) :
    M.coarseSubspaceLeakageLinearMap A = 0 ↔
      M.PullbackCoarseSubspaceInvariant A := by
  constructor
  · intro h y
    have hy := LinearMap.congr_fun h y
    change
      A (M.l2PullbackLinearMap y) -
        M.l2PullbackLinearMap (M.compressContinuousLinearOperator A y) = 0
      at hy
    have hAU := sub_eq_zero.mp hy
    change
      M.l2PullbackLinearMap
          (M.l2ConditionalExpectationLinearMap
            (A (M.l2PullbackLinearMap y))) =
        A (M.l2PullbackLinearMap y)
    exact hAU.symm
  · intro h
    apply LinearMap.ext
    intro y
    change
      A (M.l2PullbackLinearMap y) -
        M.l2PullbackLinearMap (M.compressContinuousLinearOperator A y) = 0
    apply sub_eq_zero.mpr
    have hy := h y
    change
      M.l2PullbackLinearMap
          (M.l2ConditionalExpectationLinearMap
            (A (M.l2PullbackLinearMap y))) =
        A (M.l2PullbackLinearMap y)
      at hy
    exact hy.symm

/-- Strong intertwining is equivalent to the simultaneous vanishing of the two
orthogonal obstruction components: compression mismatch and coarse-subspace
leakage. -/
theorem intertwiningResidualLinearMap_eq_zero_iff_discrepancy_and_leakage
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (B : FiniteProbabilityL2Carrier Y →L[ℝ]
      FiniteProbabilityL2Carrier Y) :
    M.intertwiningResidualLinearMap A B = 0 ↔
      M.compressionDiscrepancyLinearMap A B = 0 ∧
        M.coarseSubspaceLeakageLinearMap A = 0 := by
  constructor
  · intro hres
    have hinter :=
      (M.intertwiningResidualLinearMap_eq_zero_iff A B).mp hres
    have hcomp := M.compressContinuousLinearOperator_eq_of_intertwining A B hinter
    have hdisc : M.compressionDiscrepancyLinearMap A B = 0 :=
      (M.compressionDiscrepancyLinearMap_eq_zero_iff A B).2 hcomp
    have hleak : M.coarseSubspaceLeakageLinearMap A = 0 := by
      apply LinearMap.ext
      intro y
      change
        A (M.l2PullbackLinearMap y) -
          M.l2PullbackLinearMap (M.compressContinuousLinearOperator A y) = 0
      rw [hcomp]
      exact sub_eq_zero.mpr (hinter y)
    exact ⟨hdisc, hleak⟩
  · rintro ⟨hdisc, hleak⟩
    have hcomp :=
      (M.compressionDiscrepancyLinearMap_eq_zero_iff A B).mp hdisc
    apply (M.intertwiningResidualLinearMap_eq_zero_iff A B).2
    intro y
    have hy := LinearMap.congr_fun hleak y
    change
      A (M.l2PullbackLinearMap y) -
        M.l2PullbackLinearMap (M.compressContinuousLinearOperator A y) = 0
      at hy
    have hAU := sub_eq_zero.mp hy
    rw [hcomp] at hAU
    exact hAU

/-- Equivalent conceptual criterion: exact strong intertwining means both that
compression gives the target operator and that the source evolution preserves
the pulled-back coarse subspace. -/
theorem intertwiningResidualLinearMap_eq_zero_iff_compression_and_invariant
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (B : FiniteProbabilityL2Carrier Y →L[ℝ]
      FiniteProbabilityL2Carrier Y) :
    M.intertwiningResidualLinearMap A B = 0 ↔
      M.compressContinuousLinearOperator A = B ∧
        M.PullbackCoarseSubspaceInvariant A := by
  rw [M.intertwiningResidualLinearMap_eq_zero_iff_discrepancy_and_leakage A B]
  rw [M.compressionDiscrepancyLinearMap_eq_zero_iff A B]
  rw [M.coarseSubspaceLeakageLinearMap_eq_zero_iff A]

/-- Audit-visible generic obstruction decomposition package. -/
structure IntertwiningObstructionDecompositionPackage
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (B : FiniteProbabilityL2Carrier Y →L[ℝ]
      FiniteProbabilityL2Carrier Y) where
  discrepancy :
    FiniteProbabilityL2Carrier Y →ₗ[ℝ]
      FiniteProbabilityL2Carrier Y
  discrepancy_eq : discrepancy = M.compressionDiscrepancyLinearMap A B
  leakage :
    FiniteProbabilityL2Carrier Y →ₗ[ℝ]
      FiniteProbabilityL2Carrier X
  leakage_eq : leakage = M.coarseSubspaceLeakageLinearMap A
  decomposition :
    M.intertwiningResidualLinearMap A B =
      M.l2PullbackLinearMap.comp discrepancy + leakage
  orthogonal : ∀ y,
    inner ℝ (M.l2PullbackLinearMap (discrepancy y)) (leakage y) = 0
  pythagorean : ∀ y,
    ‖M.intertwiningResidualLinearMap A B y‖ ^ 2 =
      ‖discrepancy y‖ ^ 2 + ‖leakage y‖ ^ 2
  zeroCriterion :
    M.intertwiningResidualLinearMap A B = 0 ↔
      discrepancy = 0 ∧ leakage = 0
  conceptualCriterion :
    M.intertwiningResidualLinearMap A B = 0 ↔
      M.compressContinuousLinearOperator A = B ∧
        M.PullbackCoarseSubspaceInvariant A

/-- Construct the complete generic strong-obstruction decomposition receipt. -/
noncomputable def intertwiningObstructionDecompositionPackage
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (B : FiniteProbabilityL2Carrier Y →L[ℝ]
      FiniteProbabilityL2Carrier Y) :
    IntertwiningObstructionDecompositionPackage M A B where
  discrepancy := M.compressionDiscrepancyLinearMap A B
  discrepancy_eq := rfl
  leakage := M.coarseSubspaceLeakageLinearMap A
  leakage_eq := rfl
  decomposition := M.intertwiningResidual_decomposition A B
  orthogonal := M.pullback_compressionDiscrepancy_inner_coarseSubspaceLeakage_eq_zero A B
  pythagorean := M.norm_sq_intertwiningResidual_eq_discrepancy_add_leakage A B
  zeroCriterion :=
    M.intertwiningResidualLinearMap_eq_zero_iff_discrepancy_and_leakage A B
  conceptualCriterion :=
    M.intertwiningResidualLinearMap_eq_zero_iff_compression_and_invariant A B

end FiniteStrictProbabilityMap

end

end MathlibAnalytic
end MGAP4D
