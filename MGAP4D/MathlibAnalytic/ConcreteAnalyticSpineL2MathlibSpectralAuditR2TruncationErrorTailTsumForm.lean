import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorEnergyIte

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
The pointwise tail function associated to the diagonal target graph.
-/
def concreteL2TargetGraphEnergyTailIte
    (x : ConcreteL2DiagonalDomainCarrier) (N : ℕ) (n : ℕ) : ℝ :=
  if n < N then
    0
  else
    concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n

/--
The truncation-error energy series is pointwise the target tail-`ite` series.
-/
theorem concrete_l2_raw_truncation_graph_error_energy_eq_tail_ite_fun
    (x : ConcreteL2DiagonalDomainCarrier) (N : ℕ) :
    (fun n : ℕ =>
      concreteL2GraphPairEnergyTerm (concreteL2RawTruncationGraphError x N) n) =
      fun n : ℕ => concreteL2TargetGraphEnergyTailIte x N n := by
  funext n
  exact concrete_l2_raw_truncation_graph_error_energy_eq_ite x N n

/--
The target tail-`ite` series is summable, because it is pointwise the
truncation-error energy series.
-/
theorem concrete_l2_target_graph_energy_tail_ite_summable
    (x : ConcreteL2DiagonalDomainCarrier) (N : ℕ) :
    Summable fun n : ℕ => concreteL2TargetGraphEnergyTailIte x N n := by
  have h := concrete_l2_completed_graph_energy_summable
    (concreteL2RawTruncationGraphError x N)
  simpa [concrete_l2_raw_truncation_graph_error_energy_eq_tail_ite_fun x N]
    using h

/--
Completed truncation-error graph energy is exactly the `tsum` of the target
outside-cutoff tail-`ite` series.
-/
theorem concrete_l2_completed_truncation_error_energy_eq_tail_ite_tsum
    (x : ConcreteL2DiagonalDomainCarrier) (N : ℕ) :
    concreteL2CompletedGraphEnergy (concreteL2RawTruncationGraphError x N) =
      ∑' n : ℕ, concreteL2TargetGraphEnergyTailIte x N n := by
  unfold concreteL2CompletedGraphEnergy
  rw [concrete_l2_raw_truncation_graph_error_energy_eq_tail_ite_fun x N]

/--
Pointwise nonnegativity of the target tail-`ite` series.
-/
theorem concrete_l2_target_graph_energy_tail_ite_nonneg
    (x : ConcreteL2DiagonalDomainCarrier) (N n : ℕ) :
    0 ≤ concreteL2TargetGraphEnergyTailIte x N n := by
  unfold concreteL2TargetGraphEnergyTailIte
  by_cases hn : n < N
  · simp [hn]
  · simp [hn, concrete_l2_graph_pair_energy_term_nonneg (x.1, concreteL2DiagonalActionL2 x) n]

/--
The target tail-`ite` series is pointwise bounded by the full target graph energy
series.
-/
theorem concrete_l2_target_graph_energy_tail_ite_le_target
    (x : ConcreteL2DiagonalDomainCarrier) (N n : ℕ) :
    concreteL2TargetGraphEnergyTailIte x N n ≤
      concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n := by
  unfold concreteL2TargetGraphEnergyTailIte
  by_cases hn : n < N
  · simp [hn, concrete_l2_graph_pair_energy_term_nonneg (x.1, concreteL2DiagonalActionL2 x) n]
  · simp [hn]

/--
`tsum`-form package for the truncation-error energy tail.
-/
def concreteL2MathlibSpectralAuditR2TruncationErrorTailTsumFormPackage : Prop :=
  (∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N : ℕ,
      concreteL2CompletedGraphEnergy (concreteL2RawTruncationGraphError x N) =
        ∑' n : ℕ, concreteL2TargetGraphEnergyTailIte x N n) ∧
  (∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N : ℕ,
      Summable fun n : ℕ => concreteL2TargetGraphEnergyTailIte x N n) ∧
  (∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N n : ℕ,
      0 ≤ concreteL2TargetGraphEnergyTailIte x N n) ∧
  (∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N n : ℕ,
      concreteL2TargetGraphEnergyTailIte x N n ≤
        concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n)

/-- The `tsum`-form package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_truncation_error_tail_tsum_form_package_ready :
    concreteL2MathlibSpectralAuditR2TruncationErrorTailTsumFormPackage := by
  exact ⟨
    concrete_l2_completed_truncation_error_energy_eq_tail_ite_tsum,
    concrete_l2_target_graph_energy_tail_ite_summable,
    concrete_l2_target_graph_energy_tail_ite_nonneg,
    concrete_l2_target_graph_energy_tail_ite_le_target⟩

/--
Boundary retained after rewriting completed truncation-error energy as a tail
`tsum`.  The next step is the exact finite-prefix subtraction theorem for this
nonnegative tail series.
-/
def concreteL2MathlibSpectralAuditR2TruncationErrorTailTsumFormBoundaryHeld : Prop :=
  True

/-- Surface for the truncation-error tail `tsum` form. -/
structure ConcreteL2MathlibSpectralAuditR2TruncationErrorTailTsumFormSurface where
  pointwiseIteReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorEnergyIteSurfaceReady
  tailTsumFormPackage :
    concreteL2MathlibSpectralAuditR2TruncationErrorTailTsumFormPackage
  boundaryHeld : concreteL2MathlibSpectralAuditR2TruncationErrorTailTsumFormBoundaryHeld
  boundaryNotTailTsumSubPrefix : Prop
  boundaryNotCompletedEnergyComparison : Prop
  boundaryNotTailSmallnessClosed : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotExactAtomDerivation : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the truncation-error tail `tsum` form. -/
def concreteL2MathlibSpectralAuditR2TruncationErrorTailTsumFormSurface :
    ConcreteL2MathlibSpectralAuditR2TruncationErrorTailTsumFormSurface :=
  { pointwiseIteReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_truncation_error_energy_ite_surface_ready
    tailTsumFormPackage :=
      concrete_l2_mathlib_spectral_audit_r2_truncation_error_tail_tsum_form_package_ready
    boundaryHeld := True.intro
    boundaryNotTailTsumSubPrefix := True
    boundaryNotCompletedEnergyComparison := True
    boundaryNotTailSmallnessClosed := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotExactAtomDerivation := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the truncation-error tail `tsum` form. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorTailTsumFormSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorEnergyIteSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2TruncationErrorTailTsumFormPackage ∧
  concreteL2MathlibSpectralAuditR2TruncationErrorTailTsumFormBoundaryHeld

/-- Readiness theorem for the truncation-error tail `tsum` form. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_truncation_error_tail_tsum_form_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorTailTsumFormSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_truncation_error_energy_ite_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_truncation_error_tail_tsum_form_package_ready,
    True.intro⟩

end

end MathlibAnalytic
end MGAP4D
