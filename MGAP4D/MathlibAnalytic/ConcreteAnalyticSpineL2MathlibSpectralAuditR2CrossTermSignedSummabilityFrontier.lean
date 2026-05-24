import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermAbsSummable

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Positive part of the concrete cross term. -/
def concreteL2GraphPairCrossTermPos
    (p q : ConcreteL2GraphPairSpace) (n : ℕ) : ℝ :=
  max (concreteL2GraphPairCrossTerm p q n) 0

/-- Negative part of the concrete cross term, as a nonnegative function. -/
def concreteL2GraphPairCrossTermNeg
    (p q : ConcreteL2GraphPairSpace) (n : ℕ) : ℝ :=
  max (-(concreteL2GraphPairCrossTerm p q n)) 0

/-- The positive part of the cross term is nonnegative. -/
theorem concrete_l2_graph_pair_cross_term_pos_nonneg
    (p q : ConcreteL2GraphPairSpace) (n : ℕ) :
    0 ≤ concreteL2GraphPairCrossTermPos p q n := by
  unfold concreteL2GraphPairCrossTermPos
  exact le_max_right _ _

/-- The negative part of the cross term is nonnegative. -/
theorem concrete_l2_graph_pair_cross_term_neg_nonneg
    (p q : ConcreteL2GraphPairSpace) (n : ℕ) :
    0 ≤ concreteL2GraphPairCrossTermNeg p q n := by
  unfold concreteL2GraphPairCrossTermNeg
  exact le_max_right _ _

/-- The positive part is bounded by the absolute value. -/
theorem concrete_l2_graph_pair_cross_term_pos_le_abs
    (p q : ConcreteL2GraphPairSpace) (n : ℕ) :
    concreteL2GraphPairCrossTermPos p q n ≤
      |concreteL2GraphPairCrossTerm p q n| := by
  unfold concreteL2GraphPairCrossTermPos
  exact max_le (le_abs_self _) (abs_nonneg _)

/-- The negative part is bounded by the absolute value. -/
theorem concrete_l2_graph_pair_cross_term_neg_le_abs
    (p q : ConcreteL2GraphPairSpace) (n : ℕ) :
    concreteL2GraphPairCrossTermNeg p q n ≤
      |concreteL2GraphPairCrossTerm p q n| := by
  unfold concreteL2GraphPairCrossTermNeg
  exact max_le (neg_le_abs _) (abs_nonneg _)

/-- The cross term is the difference of its positive and negative parts. -/
theorem concrete_l2_graph_pair_cross_term_pos_sub_neg
    (p q : ConcreteL2GraphPairSpace) (n : ℕ) :
    concreteL2GraphPairCrossTermPos p q n -
        concreteL2GraphPairCrossTermNeg p q n =
      concreteL2GraphPairCrossTerm p q n := by
  unfold concreteL2GraphPairCrossTermPos concreteL2GraphPairCrossTermNeg
  by_cases h : 0 ≤ concreteL2GraphPairCrossTerm p q n
  · have hmax_pos : max (concreteL2GraphPairCrossTerm p q n) 0 =
        concreteL2GraphPairCrossTerm p q n := max_eq_left h
    have hmax_neg : max (-(concreteL2GraphPairCrossTerm p q n)) 0 = 0 := by
      exact max_eq_right (by nlinarith)
    rw [hmax_pos, hmax_neg]
    ring
  · have hle : concreteL2GraphPairCrossTerm p q n ≤ 0 := le_of_not_ge h
    have hmax_pos : max (concreteL2GraphPairCrossTerm p q n) 0 = 0 :=
      max_eq_right hle
    have hmax_neg : max (-(concreteL2GraphPairCrossTerm p q n)) 0 =
        -(concreteL2GraphPairCrossTerm p q n) := by
      exact max_eq_left (by nlinarith)
    rw [hmax_pos, hmax_neg]
    ring

/-- Signed summability frontier for the cross term. -/
def concreteL2MathlibSpectralAuditR2CrossTermSignedSummabilityFrontier : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermAbsSummableSurfaceReady

/-- Readiness theorem for the signed summability frontier. -/
theorem concrete_l2_mathlib_spectral_audit_r2_cross_term_signed_summability_frontier_ready :
    concreteL2MathlibSpectralAuditR2CrossTermSignedSummabilityFrontier := by
  exact concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_abs_summable_surface_ready

/-- Target: summability of the signed cross-term series. -/
def concreteL2MathlibSpectralAuditR2CrossTermSignedSummableTarget : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    Summable fun n : ℕ => concreteL2GraphPairCrossTerm p q n

/-- Surface for signed cross-term summability frontier. -/
structure ConcreteL2MathlibSpectralAuditR2CrossTermSignedSummabilityFrontierSurface where
  absSummableReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermAbsSummableSurfaceReady
  posNonneg : ∀ (p q : ConcreteL2GraphPairSpace) (n : ℕ),
    0 ≤ concreteL2GraphPairCrossTermPos p q n
  negNonneg : ∀ (p q : ConcreteL2GraphPairSpace) (n : ℕ),
    0 ≤ concreteL2GraphPairCrossTermNeg p q n
  posLeAbs : ∀ (p q : ConcreteL2GraphPairSpace) (n : ℕ),
    concreteL2GraphPairCrossTermPos p q n ≤ |concreteL2GraphPairCrossTerm p q n|
  negLeAbs : ∀ (p q : ConcreteL2GraphPairSpace) (n : ℕ),
    concreteL2GraphPairCrossTermNeg p q n ≤ |concreteL2GraphPairCrossTerm p q n|
  posSubNeg : ∀ (p q : ConcreteL2GraphPairSpace) (n : ℕ),
    concreteL2GraphPairCrossTermPos p q n -
        concreteL2GraphPairCrossTermNeg p q n =
      concreteL2GraphPairCrossTerm p q n
  signedSummableTarget : Prop
  boundaryNotSignedSummable : Prop
  boundaryNotCrossTermSummedCauchy : Prop

/-- Concrete signed cross-term summability frontier surface. -/
def concreteL2MathlibSpectralAuditR2CrossTermSignedSummabilityFrontierSurface :
    ConcreteL2MathlibSpectralAuditR2CrossTermSignedSummabilityFrontierSurface :=
  { absSummableReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_abs_summable_surface_ready
    posNonneg := concrete_l2_graph_pair_cross_term_pos_nonneg
    negNonneg := concrete_l2_graph_pair_cross_term_neg_nonneg
    posLeAbs := concrete_l2_graph_pair_cross_term_pos_le_abs
    negLeAbs := concrete_l2_graph_pair_cross_term_neg_le_abs
    posSubNeg := concrete_l2_graph_pair_cross_term_pos_sub_neg
    signedSummableTarget := concreteL2MathlibSpectralAuditR2CrossTermSignedSummableTarget
    boundaryNotSignedSummable := True
    boundaryNotCrossTermSummedCauchy := True }

/-- Readiness predicate for signed cross-term summability frontier. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSignedSummabilityFrontierSurfaceReady : Prop :=
  concreteL2MathlibSpectralAuditR2CrossTermSignedSummabilityFrontier ∧
  (∀ (p q : ConcreteL2GraphPairSpace) (n : ℕ),
    concreteL2GraphPairCrossTermPos p q n -
        concreteL2GraphPairCrossTermNeg p q n =
      concreteL2GraphPairCrossTerm p q n)

/-- Readiness theorem for signed cross-term summability frontier. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_signed_summability_frontier_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSignedSummabilityFrontierSurfaceReady := by
  exact ⟨
    concrete_l2_mathlib_spectral_audit_r2_cross_term_signed_summability_frontier_ready,
    concrete_l2_graph_pair_cross_term_pos_sub_neg⟩

end

end MathlibAnalytic
end MGAP4D
