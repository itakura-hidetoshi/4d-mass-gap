import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormEnergyPrefixLimit

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- First coordinate of the truncation graph error. -/
def concreteL2RawTruncationGraphErrorFst
    (x : ConcreteL2DiagonalDomainCarrier) (N n : ℕ) : ℝ :=
  (concreteL2GraphPairFst (concreteL2RawTruncationGraphError x N)).1 n

/-- Second coordinate of the truncation graph error. -/
def concreteL2RawTruncationGraphErrorSnd
    (x : ConcreteL2DiagonalDomainCarrier) (N n : ℕ) : ℝ :=
  (concreteL2GraphPairSnd (concreteL2RawTruncationGraphError x N)).1 n

/-- Inside the cutoff, the first coordinate of the truncation graph error is zero. -/
theorem concrete_l2_raw_truncation_graph_error_fst_eq_zero_of_lt
    (x : ConcreteL2DiagonalDomainCarrier) (N n : ℕ) (hn : n < N) :
    concreteL2RawTruncationGraphErrorFst x N n = 0 := by
  unfold concreteL2RawTruncationGraphErrorFst
  unfold concreteL2RawTruncationGraphError
  unfold concreteL2MathlibSpectralAuditR2GraphNormCanonicalGraphSequence
  unfold concreteL2RawTruncationDomainSequence
  unfold concreteL2RawTruncationDomainPoint
  unfold concreteL2GraphPairSub concreteL2GraphPairNeg concreteL2GraphPairAdd
  unfold concreteL2GraphPairSmul concreteL2GraphPairFst
  unfold concreteL2RealAdd concreteL2RealSmul
  rw [concrete_l2_raw_truncation_eq_of_lt x.1 N n hn]
  ring

/-- Inside the cutoff, the second coordinate of the truncation graph error is zero. -/
theorem concrete_l2_raw_truncation_graph_error_snd_eq_zero_of_lt
    (x : ConcreteL2DiagonalDomainCarrier) (N n : ℕ) (hn : n < N) :
    concreteL2RawTruncationGraphErrorSnd x N n = 0 := by
  unfold concreteL2RawTruncationGraphErrorSnd
  unfold concreteL2RawTruncationGraphError
  unfold concreteL2MathlibSpectralAuditR2GraphNormCanonicalGraphSequence
  unfold concreteL2RawTruncationDomainSequence
  unfold concreteL2RawTruncationDomainPoint
  unfold concreteL2GraphPairSub concreteL2GraphPairNeg concreteL2GraphPairAdd
  unfold concreteL2GraphPairSmul concreteL2GraphPairSnd
  unfold concreteL2RealAdd concreteL2RealSmul
  unfold concreteL2DiagonalActionL2 concreteL2DiagonalRawAction
  rw [concrete_l2_raw_truncation_eq_of_lt x.1 N n hn]
  ring

/-- Outside the cutoff, the first coordinate of the truncation graph error is `-x`. -/
theorem concrete_l2_raw_truncation_graph_error_fst_eq_neg_of_not_lt
    (x : ConcreteL2DiagonalDomainCarrier) (N n : ℕ) (hn : ¬ n < N) :
    concreteL2RawTruncationGraphErrorFst x N n = - x.1.1 n := by
  unfold concreteL2RawTruncationGraphErrorFst
  unfold concreteL2RawTruncationGraphError
  unfold concreteL2MathlibSpectralAuditR2GraphNormCanonicalGraphSequence
  unfold concreteL2RawTruncationDomainSequence
  unfold concreteL2RawTruncationDomainPoint
  unfold concreteL2GraphPairSub concreteL2GraphPairNeg concreteL2GraphPairAdd
  unfold concreteL2GraphPairSmul concreteL2GraphPairFst
  unfold concreteL2RealAdd concreteL2RealSmul
  rw [concrete_l2_raw_truncation_eq_zero_of_not_lt x.1 N n hn]
  ring

/-- Outside the cutoff, the second coordinate of the truncation graph error is `-A x`. -/
theorem concrete_l2_raw_truncation_graph_error_snd_eq_neg_of_not_lt
    (x : ConcreteL2DiagonalDomainCarrier) (N n : ℕ) (hn : ¬ n < N) :
    concreteL2RawTruncationGraphErrorSnd x N n =
      - (concreteL2DiagonalActionL2 x).1 n := by
  unfold concreteL2RawTruncationGraphErrorSnd
  unfold concreteL2RawTruncationGraphError
  unfold concreteL2MathlibSpectralAuditR2GraphNormCanonicalGraphSequence
  unfold concreteL2RawTruncationDomainSequence
  unfold concreteL2RawTruncationDomainPoint
  unfold concreteL2GraphPairSub concreteL2GraphPairNeg concreteL2GraphPairAdd
  unfold concreteL2GraphPairSmul concreteL2GraphPairSnd
  unfold concreteL2RealAdd concreteL2RealSmul
  unfold concreteL2DiagonalActionL2 concreteL2DiagonalRawAction
  rw [concrete_l2_raw_truncation_eq_zero_of_not_lt x.1 N n hn]
  ring

/-- Inside the cutoff, the truncation graph-error energy term is zero. -/
theorem concrete_l2_raw_truncation_graph_error_energy_eq_zero_of_lt
    (x : ConcreteL2DiagonalDomainCarrier) (N n : ℕ) (hn : n < N) :
    concreteL2GraphPairEnergyTerm (concreteL2RawTruncationGraphError x N) n = 0 := by
  unfold concreteL2GraphPairEnergyTerm
  rw [
    ← concreteL2RawTruncationGraphErrorFst,
    ← concreteL2RawTruncationGraphErrorSnd,
    concrete_l2_raw_truncation_graph_error_fst_eq_zero_of_lt x N n hn,
    concrete_l2_raw_truncation_graph_error_snd_eq_zero_of_lt x N n hn]
  ring

/-- Outside the cutoff, the truncation graph-error energy term equals the target graph energy. -/
theorem concrete_l2_raw_truncation_graph_error_energy_eq_target_of_not_lt
    (x : ConcreteL2DiagonalDomainCarrier) (N n : ℕ) (hn : ¬ n < N) :
    concreteL2GraphPairEnergyTerm (concreteL2RawTruncationGraphError x N) n =
      concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n := by
  unfold concreteL2GraphPairEnergyTerm
  rw [
    ← concreteL2RawTruncationGraphErrorFst,
    ← concreteL2RawTruncationGraphErrorSnd,
    concrete_l2_raw_truncation_graph_error_fst_eq_neg_of_not_lt x N n hn,
    concrete_l2_raw_truncation_graph_error_snd_eq_neg_of_not_lt x N n hn]
  ring

/-- Surface for the pointwise truncation graph-error laws. -/
structure ConcreteL2MathlibSpectralAuditR2TruncationErrorPointwiseSurface where
  energyPrefixLimitReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormEnergyPrefixLimitSurfaceReady
  fstZeroInside :
    ∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N n : ℕ,
      n < N → concreteL2RawTruncationGraphErrorFst x N n = 0
  sndZeroInside :
    ∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N n : ℕ,
      n < N → concreteL2RawTruncationGraphErrorSnd x N n = 0
  energyZeroInside :
    ∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N n : ℕ,
      n < N → concreteL2GraphPairEnergyTerm
        (concreteL2RawTruncationGraphError x N) n = 0
  energyTargetOutside :
    ∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N n : ℕ,
      ¬ n < N → concreteL2GraphPairEnergyTerm
        (concreteL2RawTruncationGraphError x N) n =
          concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n
  boundaryNotTailEnergyTheorem : Prop
  boundaryNotTruncationEnergyEpsilonTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the pointwise truncation graph-error laws. -/
def concreteL2MathlibSpectralAuditR2TruncationErrorPointwiseSurface :
    ConcreteL2MathlibSpectralAuditR2TruncationErrorPointwiseSurface :=
  { energyPrefixLimitReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_energy_prefix_limit_surface_ready
    fstZeroInside :=
      concrete_l2_raw_truncation_graph_error_fst_eq_zero_of_lt
    sndZeroInside :=
      concrete_l2_raw_truncation_graph_error_snd_eq_zero_of_lt
    energyZeroInside :=
      concrete_l2_raw_truncation_graph_error_energy_eq_zero_of_lt
    energyTargetOutside :=
      concrete_l2_raw_truncation_graph_error_energy_eq_target_of_not_lt
    boundaryNotTailEnergyTheorem := True
    boundaryNotTruncationEnergyEpsilonTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for pointwise truncation graph-error laws. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorPointwiseSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormEnergyPrefixLimitSurfaceReady ∧
  (∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N n : ℕ,
      n < N → concreteL2GraphPairEnergyTerm
        (concreteL2RawTruncationGraphError x N) n = 0) ∧
  (∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N n : ℕ,
      ¬ n < N → concreteL2GraphPairEnergyTerm
        (concreteL2RawTruncationGraphError x N) n =
          concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n)

/-- Readiness theorem for pointwise truncation graph-error laws. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_truncation_error_pointwise_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2TruncationErrorPointwiseSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_energy_prefix_limit_surface_ready,
    concrete_l2_raw_truncation_graph_error_energy_eq_zero_of_lt,
    concrete_l2_raw_truncation_graph_error_energy_eq_target_of_not_lt⟩

end

end MathlibAnalytic
end MGAP4D