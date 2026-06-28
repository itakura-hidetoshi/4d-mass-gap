import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonActionControlPointwiseBound
import Mathlib.Data.ENNReal.BigOperators

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
open MeasureTheory

noncomputable section

/-- The nonnegative extended-real plaquette energy at one compact-gauge scale. -/
def ContinuousCompactGaugeWilsonPhysicalEmbedding.plaquetteEnergyObservable
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (n : ℕ)
    (g : (E.system n).base.Gauge) : ENNReal :=
  ENNReal.ofReal ((E.system n).base.plaquetteEnergy g)

/-- The extended-real Wilson action is exactly the finite sum of the
extended-real plaquette energies. -/
theorem ContinuousCompactGaugeWilsonPhysicalEmbedding.wilsonActionObservable_eq_plaquette_sum
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (n : ℕ)
    (U : (E.system n).base.Configuration) :
    E.wilsonActionObservable n U =
      ∑ p : (E.system n).base.Plaquette,
        E.plaquetteEnergyObservable n
          ((E.system n).base.plaquetteHolonomy U p) := by
  change
    ENNReal.ofReal
        (∑ p : (E.system n).base.Plaquette,
          (E.system n).base.plaquetteEnergy
            ((E.system n).base.plaquetteHolonomy U p)) =
      ∑ p : (E.system n).base.Plaquette,
        ENNReal.ofReal
          ((E.system n).base.plaquetteEnergy
            ((E.system n).base.plaquetteHolonomy U p))
  simpa using
    (ENNReal.ofReal_sum_of_nonneg
      (s := Finset.univ)
      (f := fun p : (E.system n).base.Plaquette =>
        (E.system n).base.plaquetteEnergy
          ((E.system n).base.plaquetteHolonomy U p))
      (fun p _hp => (E.system n).base.plaquetteEnergy_nonneg _))

/-- One finite bound for all plaquette energies across the scaling family. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonPlaquetteEnergyUniformBound
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding) where
  energyBound : ENNReal
  energyBound_ne_top : energyBound ≠ ⊤
  pointwise_le :
    ∀ n (g : (E.system n).base.Gauge),
      E.plaquetteEnergyObservable n g ≤ energyBound

/-- A volume-compatible envelope for the affine-renormalized action. The
finite sum of `energyBound` is exactly the plaquette multiplicity factor, while
`scale` may decay with the number of plaquettes. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonPlaquetteNormalizationEnvelope
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (scale offset : ℕ → ENNReal)
    (B : E.WilsonPlaquetteEnergyUniformBound) where
  bound : ENNReal
  bound_ne_top : bound ≠ ⊤
  envelope_le :
    ∀ n,
      scale n *
          (∑ _p : (E.system n).base.Plaquette, B.energyBound) +
        offset n ≤ bound

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonPlaquetteNormalizationEnvelope

/-- Plaquette-energy control and the normalization envelope imply a uniform
pointwise bound for the renormalized Wilson action. -/
def toWilsonActionControlUniformPointwiseBound
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {scale offset : ℕ → ENNReal}
    {B : E.WilsonPlaquetteEnergyUniformBound}
    (N : E.WilsonPlaquetteNormalizationEnvelope scale offset B) :
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
                (∑ _p : (E.system n).base.Plaquette, B.energyBound) +
              offset n := by
          gcongr
          rw [E.wilsonActionObservable_eq_plaquette_sum]
          exact Finset.sum_le_sum fun p _hp =>
            B.pointwise_le n ((E.system n).base.plaquetteHolonomy U p)
        _ ≤ N.bound := N.envelope_le n }

/-- The plaquette-level deterministic receipts imply tightness. -/
theorem isTight
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    {B : E.WilsonPlaquetteEnergyUniformBound}
    (N : E.WilsonPlaquetteNormalizationEnvelope scale offset B)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    IsTightMeasureSet E.toLatticeEmbedding.embeddedMeasureSet :=
  N.toWilsonActionControlUniformPointwiseBound.isTight D

/-- The plaquette-level deterministic receipts produce a physical continuum
weak limit. -/
noncomputable def toWeakLimit
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    {B : E.WilsonPlaquetteEnergyUniformBound}
    (N : E.WilsonPlaquetteNormalizationEnvelope scale offset B)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  N.toWilsonActionControlUniformPointwiseBound.toWeakLimit D

end ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonPlaquetteNormalizationEnvelope

/-- Public constructor from plaquette-energy control, a lattice-volume
normalization envelope, and deterministic physical coercivity. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_plaquetteControl
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (B : E.WilsonPlaquetteEnergyUniformBound)
    (N : E.WilsonPlaquetteNormalizationEnvelope scale offset B)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  N.toWeakLimit D

end

end MathlibAnalytic
end MGAP4D
