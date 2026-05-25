import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermPosNegSummable

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Summability of the signed cross-term series.

The cross term is decomposed as `cross⁺ - cross⁻`, and both parts are summable
because they are dominated by `|cross|`.
-/
theorem concrete_l2_graph_pair_cross_term_summable
    (p q : ConcreteL2GraphPairSpace) :
    Summable fun n : ℕ => concreteL2GraphPairCrossTerm p q n := by
  have hpos : Summable fun n : ℕ => concreteL2GraphPairCrossTermPos p q n :=
    concrete_l2_graph_pair_cross_term_pos_summable p q
  have hneg : Summable fun n : ℕ => concreteL2GraphPairCrossTermNeg p q n :=
    concrete_l2_graph_pair_cross_term_neg_summable p q
  have hsub : Summable fun n : ℕ =>
      concreteL2GraphPairCrossTermPos p q n -
        concreteL2GraphPairCrossTermNeg p q n :=
    hpos.sub hneg
  have hfun :
      (fun n : ℕ =>
        concreteL2GraphPairCrossTermPos p q n -
          concreteL2GraphPairCrossTermNeg p q n) =
        (fun n : ℕ => concreteL2GraphPairCrossTerm p q n) := by
    funext n
    exact concrete_l2_graph_pair_cross_term_pos_sub_neg p q n
  simpa [hfun] using hsub

/-- Package: summability of the signed cross-term series. -/
def concreteL2MathlibSpectralAuditR2CrossTermSignedSummable : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    Summable fun n : ℕ => concreteL2GraphPairCrossTerm p q n

/-- The signed cross-term summability package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_cross_term_signed_summable :
    concreteL2MathlibSpectralAuditR2CrossTermSignedSummable := by
  intro p q
  exact concrete_l2_graph_pair_cross_term_summable p q

/-- Surface for signed cross-term summability. -/
structure ConcreteL2MathlibSpectralAuditR2CrossTermSignedSummableSurface where
  posNegReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermPosNegSummableSurfaceReady
  signedSummable : concreteL2MathlibSpectralAuditR2CrossTermSignedSummable
  boundaryNotCrossTermSummedCauchy : Prop
  boundaryNotMinkowskiSquare : Prop
  boundaryNotExactTriangle : Prop

/-- Concrete surface for signed cross-term summability. -/
def concreteL2MathlibSpectralAuditR2CrossTermSignedSummableSurface :
    ConcreteL2MathlibSpectralAuditR2CrossTermSignedSummableSurface :=
  { posNegReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_pos_neg_summable_surface_ready
    signedSummable :=
      concrete_l2_mathlib_spectral_audit_r2_cross_term_signed_summable
    boundaryNotCrossTermSummedCauchy := True
    boundaryNotMinkowskiSquare := True
    boundaryNotExactTriangle := True }

/-- Readiness predicate for signed cross-term summability. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSignedSummableSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermPosNegSummableSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2CrossTermSignedSummable

/-- Readiness theorem for signed cross-term summability. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_signed_summable_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSignedSummableSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_pos_neg_summable_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_cross_term_signed_summable⟩

end

end MathlibAnalytic
end MGAP4D
