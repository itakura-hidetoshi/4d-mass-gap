import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSpecialUnitaryMatrixTraceFormula

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def periodic_special_unitary_matrix_trace_weak_limit_compile_smoke
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
  continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicSpecialUnitaryMatrixTraceProperNNRealFunctional
    E H T functional functional_proper functional_le_action

end

end MathlibAnalytic
end MGAP4D
