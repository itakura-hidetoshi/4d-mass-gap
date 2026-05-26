import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorPointwise

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
The range-`N` prefix of the truncation-error energy is zero, because the
pointwise truncation-error energy vanishes on every index `n < N`.
-/
theorem concrete_l2_raw_truncation_graph_error_prefix_energy_zero
    (x : ConcreteL2DiagonalDomainCarrier) (N : ℕ) :
    Finset.sum (Finset.range N)
      (fun n : ℕ => concreteL2GraphPairEnergyTerm
        (concreteL2RawTruncationGraphError x N) n) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  exact concrete_l2_raw_truncation_graph_error_energy_eq_zero_of_lt x N n
    (Finset.mem_range.mp hn)

/--
The same prefix-zero theorem in a target-friendly eventual form.
-/
theorem concrete_l2_raw_truncation_graph_error_prefix_energy_zero_eventually
    (x : ConcreteL2DiagonalDomainCarrier) :
    ∀ᶠ N in Filter.atTop,
      Finset.sum (Finset.range N)
        (fun n : ℕ => concreteL2GraphPairEnergyTerm
          (concreteL2RawTruncationGraphError x N) n) = 0 := by
  filter_upwards [] with N
  exact concrete_l2_raw_truncation_graph_error_prefix_energy_zero x N

/-- Surface for the truncation-error prefix-zero theorem. -/
structure ConcreteL2MathlibSpectralAuditR2TruncationErrorPrefixZeroSurface where
  pointwiseReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorPointwiseSurfaceReady
  prefixEnergyZero :
    ∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N : ℕ,
      Finset.sum (Finset.range N)
        (fun n : ℕ => concreteL2GraphPairEnergyTerm
          (concreteL2RawTruncationGraphError x N) n) = 0
  prefixEnergyZeroEventually :
    ∀ x : ConcreteL2DiagonalDomainCarrier,
      ∀ᶠ N in Filter.atTop,
        Finset.sum (Finset.range N)
          (fun n : ℕ => concreteL2GraphPairEnergyTerm
            (concreteL2RawTruncationGraphError x N) n) = 0
  boundaryNotTailEnergyTheorem : Prop
  boundaryNotTruncationEnergyEpsilonTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the truncation-error prefix-zero theorem. -/
def concreteL2MathlibSpectralAuditR2TruncationErrorPrefixZeroSurface :
    ConcreteL2MathlibSpectralAuditR2TruncationErrorPrefixZeroSurface :=
  { pointwiseReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_truncation_error_pointwise_surface_ready
    prefixEnergyZero :=
      concrete_l2_raw_truncation_graph_error_prefix_energy_zero
    prefixEnergyZeroEventually :=
      concrete_l2_raw_truncation_graph_error_prefix_energy_zero_eventually
    boundaryNotTailEnergyTheorem := True
    boundaryNotTruncationEnergyEpsilonTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the truncation-error prefix-zero theorem. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorPrefixZeroSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorPointwiseSurfaceReady ∧
  (∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N : ℕ,
      Finset.sum (Finset.range N)
        (fun n : ℕ => concreteL2GraphPairEnergyTerm
          (concreteL2RawTruncationGraphError x N) n) = 0)

/-- Readiness theorem for the truncation-error prefix-zero theorem. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_truncation_error_prefix_zero_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorPrefixZeroSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_truncation_error_pointwise_surface_ready,
    concrete_l2_raw_truncation_graph_error_prefix_energy_zero⟩

end

end MathlibAnalytic
end MGAP4D