import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonProperFunctionalLimitCompileSmoke
import MGAP4D.MathlibAnalytic.SpecialUnitaryCompactGaugeWilsonSystemCompileSmoke
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSpecialUnitaryStandardEnergyCompileSmoke

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

structure PhysicalYangMillsSpecialUnitaryFinalFrontier where
  finiteSystem : ContinuousCompactGaugeWilsonSystem
  weakLimit : PhysicalFourDimensionalYangMillsWeakLimit

noncomputable def assemblePhysicalYangMillsSpecialUnitaryFinalFrontier
    (finiteGeometry : FiniteFourDimensionalPlaquetteGeometry)
    (rank : ℕ)
    (rank_pos : 0 < rank)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin rank) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (S : E.WilsonSpecialUnitaryStandardEnergyFamily)
    (functional : E.PhysicalConfiguration → NNReal)
    (functional_proper : IsProperMap functional)
    (functional_le_action :
      ∀ n U,
        (functional (E.interpolate n U) : ENNReal) ≤
          E.renormalizedWilsonActionObservable
            H.reciprocalPlaquetteScale
            (fun _ : ℕ => (0 : ENNReal)) n U) :
    PhysicalYangMillsSpecialUnitaryFinalFrontier :=
  { finiteSystem :=
      specialUnitaryContinuousCompactGaugeWilsonSystem
        finiteGeometry rank rank_pos beta beta_nonneg
    weakLimit :=
      continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicSpecialUnitaryStandardEnergyProperNNRealFunctional
        E H S functional functional_proper functional_le_action }

end

end MathlibAnalytic
end MGAP4D
