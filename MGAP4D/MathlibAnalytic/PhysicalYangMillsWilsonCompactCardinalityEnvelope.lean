import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCompactEnergyMaximum
import Mathlib.Data.ENNReal.BigOperators

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
open MeasureTheory Set

noncomputable section

/-- The finite sum of one compactness-generated plaquette maximum is exactly
its plaquette-cardinality multiple. -/
theorem ContinuousCompactGaugeWilsonPhysicalEmbedding.compactPlaquetteMaximum_sum_eq_card_mul
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (n : ℕ) :
    (∑ _p : (E.system n).base.Plaquette,
        E.compactPlaquetteEnergyMaximum n) =
      ((Fintype.card (E.system n).base.Plaquette : ℕ) : ENNReal) *
        E.compactPlaquetteEnergyMaximum n := by
  simp

/-- A cardinality-normalized deterministic envelope for the compactness-generated
plaquette maximum. This is the explicit finite-volume form of the abstract
compact plaquette envelope: only the number of plaquettes, the compact maximum,
and the affine renormalization coefficients remain. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonCompactPlaquetteCardinalityEnvelope
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (scale offset : ℕ → ENNReal) where
  bound : ENNReal
  bound_ne_top : bound ≠ ⊤
  envelope_le :
    ∀ n,
      scale n *
          (((Fintype.card (E.system n).base.Plaquette : ℕ) : ENNReal) *
            E.compactPlaquetteEnergyMaximum n) +
        offset n ≤ bound

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonCompactPlaquetteCardinalityEnvelope

/-- Rewrite the cardinality envelope as the finite-sum envelope consumed by the
compact-maximum weak-limit constructor. -/
def toWilsonCompactPlaquetteNormalizationEnvelope
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {scale offset : ℕ → ENNReal}
    (N : E.WilsonCompactPlaquetteCardinalityEnvelope scale offset) :
    E.WilsonCompactPlaquetteNormalizationEnvelope scale offset :=
  { bound := N.bound
    bound_ne_top := N.bound_ne_top
    envelope_le := by
      intro n
      rw [E.compactPlaquetteMaximum_sum_eq_card_mul n]
      exact N.envelope_le n }

/-- A cardinality envelope and the physical coercive interpolation estimate imply
tightness of the embedded Wilson Gibbs laws. -/
theorem isTight
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (N : E.WilsonCompactPlaquetteCardinalityEnvelope scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    IsTightMeasureSet E.toLatticeEmbedding.embeddedMeasureSet :=
  N.toWilsonCompactPlaquetteNormalizationEnvelope.isTight D

/-- A cardinality envelope and the physical coercive interpolation estimate
produce a physical continuum weak limit. -/
noncomputable def toWeakLimit
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (N : E.WilsonCompactPlaquetteCardinalityEnvelope scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  N.toWilsonCompactPlaquetteNormalizationEnvelope.toWeakLimit D

end ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonCompactPlaquetteCardinalityEnvelope

/-- Public weak-limit constructor whose normalization hypothesis is written in
the explicit finite-volume form
`scale n * (#plaquettes n * compactEnergyMaximum n) + offset n ≤ bound`. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_compactPlaquetteCardinalityEnvelope
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (N : E.WilsonCompactPlaquetteCardinalityEnvelope scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  N.toWeakLimit D

end

end MathlibAnalytic
end MGAP4D
