import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSpecialUnitaryGaugeFamily
import Mathlib.LinearAlgebra.Matrix.Trace

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The diagonal-sum definition of the normalized unitary real trace agrees
with the standard real part of `Matrix.trace`, divided by the matrix rank. -/
theorem normalizedUnitaryRealTrace_eq_trace_re_div
    (N : ℕ)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    normalizedUnitaryRealTrace N U =
      (Matrix.trace (U : Matrix (Fin N) (Fin N) ℂ)).re / (N : ℝ) := by
  simp [normalizedUnitaryRealTrace, Matrix.trace, Matrix.diag]

/-- The normalized special-unitary real trace is the standard real matrix trace
divided by the rank. -/
theorem normalizedSpecialUnitaryRealTrace_eq_trace_re_div
    (N : ℕ)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    normalizedSpecialUnitaryRealTrace N U =
      (Matrix.trace (U : Matrix (Fin N) (Fin N) ℂ)).re / (N : ℝ) := by
  exact normalizedUnitaryRealTrace_eq_trace_re_div N (specialUnitaryToUnitary N U)

/-- A Wilson scaling family stated directly with the conventional matrix-trace
formula `1 - Re Tr(U) / N`. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonSpecialUnitaryMatrixTraceFormulaFamily
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding) where
  rank : ℕ
  rank_pos : 0 < rank
  gaugeEquiv :
    ∀ n,
      (E.system n).base.Gauge ≃*
        Matrix.specialUnitaryGroup (Fin rank) ℂ
  plaquetteEnergy_eq :
    ∀ n (g : (E.system n).base.Gauge),
      (E.system n).base.plaquetteEnergy g =
        1 -
          (Matrix.trace
            (gaugeEquiv n g : Matrix (Fin rank) (Fin rank) ℂ)).re /
              (rank : ℝ)

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonSpecialUnitaryMatrixTraceFormulaFamily

/-- The conventional matrix-trace formula supplies the normalized
special-unitary gauge receipt. -/
def toWilsonSpecialUnitaryGaugeFamily
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (T : E.WilsonSpecialUnitaryMatrixTraceFormulaFamily) :
    E.WilsonSpecialUnitaryGaugeFamily :=
  { rank := T.rank
    rank_pos := T.rank_pos
    gaugeEquiv := T.gaugeEquiv
    plaquetteEnergy_eq := by
      intro n g
      rw [normalizedSpecialUnitaryRealTrace_eq_trace_re_div]
      exact T.plaquetteEnergy_eq n g }

/-- The standard matrix-trace Wilson energy is bounded above by two. -/
theorem plaquetteEnergy_le_two
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (T : E.WilsonSpecialUnitaryMatrixTraceFormulaFamily)
    (n : ℕ)
    (g : (E.system n).base.Gauge) :
    (E.system n).base.plaquetteEnergy g ≤ 2 :=
  T.toWilsonSpecialUnitaryGaugeFamily.plaquetteEnergy_le_two n g

end ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonSpecialUnitaryMatrixTraceFormulaFamily

/-- Exact periodic geometry, the conventional `SU(N)` matrix-trace Wilson
energy, and one proper `NNReal` physical functional controlled by the
reciprocal-volume action produce a physical continuum weak limit. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicSpecialUnitaryMatrixTraceProperNNRealFunctional
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (T : E.WilsonSpecialUnitaryMatrixTraceFormulaFamily)
    (functional : E.PhysicalConfiguration → NNReal)
    (functional_proper : IsProperMap functional)
    (functional_le_action :
      ∀ n U,
        (functional (E.interpolate n U) : ENNReal) ≤
          E.renormalizedWilsonActionObservable
            H.reciprocalPlaquetteScale
            (fun _ : ℕ => (0 : ENNReal)) n U) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicSpecialUnitaryGaugeProperNNRealFunctional
    E H T.toWilsonSpecialUnitaryGaugeFamily
      functional functional_proper functional_le_action

end

end MathlibAnalytic
end MGAP4D
