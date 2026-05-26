import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2TailSmallnessReduction

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Pointwise `if` normal form for the truncation graph-error energy.

Inside the cutoff the truncation-error graph energy is zero.  Outside the cutoff
it is exactly the target diagonal graph energy.  This is the pointwise form that
will feed the exact `tsum` tail comparison.
-/
theorem concrete_l2_raw_truncation_graph_error_energy_eq_ite
    (x : ConcreteL2DiagonalDomainCarrier) (N n : ℕ) :
    concreteL2GraphPairEnergyTerm (concreteL2RawTruncationGraphError x N) n =
      if n < N then
        0
      else
        concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n := by
  by_cases hn : n < N
  · simp [hn, concrete_l2_raw_truncation_graph_error_energy_eq_zero_of_lt x N n hn]
  · simp [hn, concrete_l2_raw_truncation_graph_error_energy_eq_target_of_not_lt x N n hn]

/--
Pointwise domination of truncation-error energy by the target diagonal graph
energy.
-/
theorem concrete_l2_raw_truncation_graph_error_energy_le_target
    (x : ConcreteL2DiagonalDomainCarrier) (N n : ℕ) :
    concreteL2GraphPairEnergyTerm (concreteL2RawTruncationGraphError x N) n ≤
      concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n := by
  by_cases hn : n < N
  · rw [concrete_l2_raw_truncation_graph_error_energy_eq_zero_of_lt x N n hn]
    exact concrete_l2_graph_pair_energy_term_nonneg (x.1, concreteL2DiagonalActionL2 x) n
  · rw [concrete_l2_raw_truncation_graph_error_energy_eq_target_of_not_lt x N n hn]

/--
Outside-cutoff equality for the truncation-error energy term, restated as a
named tail law for downstream `tsum` work.
-/
def concreteL2RawTruncationGraphErrorEnergyOutsideTailLaw : Prop :=
  ∀ x : ConcreteL2DiagonalDomainCarrier,
  ∀ N n : ℕ,
    ¬ n < N →
      concreteL2GraphPairEnergyTerm (concreteL2RawTruncationGraphError x N) n =
        concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n

/-- The outside-tail law is ready. -/
theorem concrete_l2_raw_truncation_graph_error_energy_outside_tail_law_ready :
    concreteL2RawTruncationGraphErrorEnergyOutsideTailLaw := by
  exact concrete_l2_raw_truncation_graph_error_energy_eq_target_of_not_lt

/--
Pointwise package for the truncation-error energy tail normal form.
-/
def concreteL2MathlibSpectralAuditR2TruncationErrorEnergyItePackage : Prop :=
  (∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N n : ℕ,
      concreteL2GraphPairEnergyTerm (concreteL2RawTruncationGraphError x N) n =
        if n < N then
          0
        else
          concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n) ∧
  (∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N n : ℕ,
      concreteL2GraphPairEnergyTerm (concreteL2RawTruncationGraphError x N) n ≤
        concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n) ∧
  concreteL2RawTruncationGraphErrorEnergyOutsideTailLaw

/-- The pointwise truncation-error energy tail package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_truncation_error_energy_ite_package_ready :
    concreteL2MathlibSpectralAuditR2TruncationErrorEnergyItePackage := by
  exact ⟨
    concrete_l2_raw_truncation_graph_error_energy_eq_ite,
    concrete_l2_raw_truncation_graph_error_energy_le_target,
    concrete_l2_raw_truncation_graph_error_energy_outside_tail_law_ready⟩

/--
Boundary retained after the pointwise `if` normalization.

This file proves the pointwise tail shape.  It does not yet turn that pointwise
shape into a `tsum` equality or inequality for completed graph energies.
-/
def concreteL2MathlibSpectralAuditR2TruncationErrorEnergyIteBoundaryHeld : Prop :=
  True

/-- Surface for truncation-error energy `if` normalization. -/
structure ConcreteL2MathlibSpectralAuditR2TruncationErrorEnergyIteSurface where
  tailSmallnessReductionReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2TailSmallnessReductionSurfaceReady
  pointwiseItePackage :
    concreteL2MathlibSpectralAuditR2TruncationErrorEnergyItePackage
  boundaryHeld : concreteL2MathlibSpectralAuditR2TruncationErrorEnergyIteBoundaryHeld
  boundaryNotTsumTailEquality : Prop
  boundaryNotCompletedEnergyComparison : Prop
  boundaryNotTailSmallnessClosed : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotExactAtomDerivation : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for truncation-error energy `if` normalization. -/
def concreteL2MathlibSpectralAuditR2TruncationErrorEnergyIteSurface :
    ConcreteL2MathlibSpectralAuditR2TruncationErrorEnergyIteSurface :=
  { tailSmallnessReductionReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_tail_smallness_reduction_surface_ready
    pointwiseItePackage :=
      concrete_l2_mathlib_spectral_audit_r2_truncation_error_energy_ite_package_ready
    boundaryHeld := True.intro
    boundaryNotTsumTailEquality := True
    boundaryNotCompletedEnergyComparison := True
    boundaryNotTailSmallnessClosed := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotExactAtomDerivation := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for truncation-error energy `if` normalization. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorEnergyIteSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2TailSmallnessReductionSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2TruncationErrorEnergyItePackage ∧
  concreteL2MathlibSpectralAuditR2TruncationErrorEnergyIteBoundaryHeld

/-- Readiness theorem for truncation-error energy `if` normalization. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_truncation_error_energy_ite_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorEnergyIteSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_tail_smallness_reduction_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_truncation_error_energy_ite_package_ready,
    True.intro⟩

end

end MathlibAnalytic
end MGAP4D
