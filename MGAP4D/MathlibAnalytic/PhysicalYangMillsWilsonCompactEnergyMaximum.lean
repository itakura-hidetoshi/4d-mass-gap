import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonPlaquetteControl
import Mathlib.Topology.Order.Compact

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
open MeasureTheory Set

noncomputable section

/-- A continuous plaquette energy on a compact gauge group attains a global
maximum. -/
theorem ContinuousCompactGaugeWilsonSystem.exists_plaquetteEnergy_maximizer
    (C : ContinuousCompactGaugeWilsonSystem) :
    ∃ g : C.base.Gauge,
      ∀ h : C.base.Gauge,
        C.base.plaquetteEnergy h ≤ C.base.plaquetteEnergy g := by
  obtain ⟨g, _hg, hmax⟩ :=
    isCompact_univ.exists_isMaxOn
      (Set.univ_nonempty : (Set.univ : Set C.base.Gauge).Nonempty)
      C.plaquetteEnergy_continuous.continuousOn
  exact ⟨g, fun h => hmax h (Set.mem_univ h)⟩

/-- A chosen maximizer of the plaquette energy. -/
noncomputable def ContinuousCompactGaugeWilsonSystem.plaquetteEnergyMaximizer
    (C : ContinuousCompactGaugeWilsonSystem) : C.base.Gauge :=
  Classical.choose C.exists_plaquetteEnergy_maximizer

/-- The canonical maximum plaquette-energy value at one compact-gauge scale. -/
noncomputable def ContinuousCompactGaugeWilsonSystem.plaquetteEnergyMaximum
    (C : ContinuousCompactGaugeWilsonSystem) : ℝ :=
  C.base.plaquetteEnergy C.plaquetteEnergyMaximizer

/-- Every plaquette energy is bounded by the canonical compact maximum. -/
theorem ContinuousCompactGaugeWilsonSystem.plaquetteEnergy_le_maximum
    (C : ContinuousCompactGaugeWilsonSystem)
    (g : C.base.Gauge) :
    C.base.plaquetteEnergy g ≤ C.plaquetteEnergyMaximum :=
  Classical.choose_spec C.exists_plaquetteEnergy_maximizer g

/-- The canonical maximum remains nonnegative. -/
theorem ContinuousCompactGaugeWilsonSystem.plaquetteEnergyMaximum_nonneg
    (C : ContinuousCompactGaugeWilsonSystem) :
    0 ≤ C.plaquetteEnergyMaximum :=
  C.base.plaquetteEnergy_nonneg C.plaquetteEnergyMaximizer

/-- The canonical extended-real maximum plaquette energy at lattice scale `n`. -/
noncomputable def
    ContinuousCompactGaugeWilsonPhysicalEmbedding.compactPlaquetteEnergyMaximum
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (n : ℕ) : ENNReal :=
  ENNReal.ofReal ((E.system n).plaquetteEnergyMaximum)

/-- Compactness and continuity automatically control every scale-`n`
plaquette energy by the canonical maximum. -/
theorem ContinuousCompactGaugeWilsonPhysicalEmbedding.plaquetteEnergyObservable_le_compactMaximum
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (n : ℕ)
    (g : (E.system n).base.Gauge) :
    E.plaquetteEnergyObservable n g ≤
      E.compactPlaquetteEnergyMaximum n :=
  ENNReal.ofReal_le_ofReal ((E.system n).plaquetteEnergy_le_maximum g)

/-- The only remaining deterministic size condition after compactness generates
all per-scale plaquette maxima. The scale may cancel the growing plaquette
multiplicity and the varying energy maximum. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonCompactPlaquetteNormalizationEnvelope
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (scale offset : ℕ → ENNReal) where
  bound : ENNReal
  bound_ne_top : bound ≠ ⊤
  envelope_le :
    ∀ n,
      scale n *
          (∑ _p : (E.system n).base.Plaquette,
            E.compactPlaquetteEnergyMaximum n) +
        offset n ≤ bound

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonCompactPlaquetteNormalizationEnvelope

/-- Compactness-generated plaquette maxima and the normalization envelope give
one uniform pointwise bound for the renormalized Wilson action. -/
def toWilsonActionControlUniformPointwiseBound
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {scale offset : ℕ → ENNReal}
    (N : E.WilsonCompactPlaquetteNormalizationEnvelope scale offset) :
    E.WilsonActionControlUniformPointwiseBound scale offset :=
  { bound := N.bound
    bound_ne_top := N.bound_ne_top
    pointwise_le := by
      classical
      intro n U
      rw [E.renormalizedWilsonActionObservable_eq]
      calc
        scale n * E.wilsonActionObservable n U + offset n ≤
            scale n *
                (∑ _p : (E.system n).base.Plaquette,
                  E.compactPlaquetteEnergyMaximum n) +
              offset n := by
          gcongr
          rw [E.wilsonActionObservable_eq_plaquette_sum]
          exact Finset.sum_le_sum fun p _hp =>
            E.plaquetteEnergyObservable_le_compactMaximum n
              ((E.system n).base.plaquetteHolonomy U p)
        _ ≤ N.bound := N.envelope_le n }

/-- Compactness-generated plaquette control and deterministic physical
coercivity imply tightness. -/
theorem isTight
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (N : E.WilsonCompactPlaquetteNormalizationEnvelope scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    IsTightMeasureSet E.toLatticeEmbedding.embeddedMeasureSet :=
  N.toWilsonActionControlUniformPointwiseBound.isTight D

/-- Compactness-generated plaquette control produces a physical continuum weak
limit. -/
noncomputable def toWeakLimit
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (N : E.WilsonCompactPlaquetteNormalizationEnvelope scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  N.toWilsonActionControlUniformPointwiseBound.toWeakLimit D

end ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonCompactPlaquetteNormalizationEnvelope

/-- Public constructor requiring only the physical coercive estimate and the
normalization envelope built from compactness-generated plaquette maxima. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_compactPlaquetteEnvelope
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (N : E.WilsonCompactPlaquetteNormalizationEnvelope scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  N.toWeakLimit D

end

end MathlibAnalytic
end MGAP4D
