import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonActionControl

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A finite uniform pointwise bound for the affine-renormalized signed Wilson
action on physical positive-link configurations. -/
structure ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.WilsonActionControlUniformPointwiseBound
    (E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding)
    (scale offset : ℕ → ENNReal) where
  bound : ENNReal
  bound_ne_top : bound ≠ ⊤
  pointwise_le :
    ∀ n U,
      E.renormalizedWilsonActionObservable scale offset n U ≤ bound

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.WilsonActionControlUniformPointwiseBound

/-- Probability normalization converts a deterministic signed-action bound into
its uniform Gibbs first-moment receipt. -/
def toWilsonActionControlMomentBound
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {scale offset : ℕ → ENNReal}
    (B : E.WilsonActionControlUniformPointwiseBound scale offset) :
    E.WilsonActionControlMomentBound scale offset :=
  { momentBound := B.bound
    momentBound_ne_top := B.bound_ne_top
    uniform_lintegral_le := by
      intro n
      letI : IsProbabilityMeasure (E.system n).gibbsMeasure :=
        continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure
          (E.system n)
      calc
        ∫⁻ U,
            E.renormalizedWilsonActionObservable scale offset n U
            ∂((E.system n).gibbsProbabilityMeasure :
              Measure (E.system n).base.Configuration) ≤
            ∫⁻ _U, B.bound
              ∂((E.system n).gibbsProbabilityMeasure :
                Measure (E.system n).base.Configuration) :=
          lintegral_mono (B.pointwise_le n)
        _ = B.bound := by simp }

/-- A uniform pointwise signed-action bound and physical coercivity imply
tightness of the interpolated laws. -/
theorem isTight
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (B : E.WilsonActionControlUniformPointwiseBound scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    IsTightMeasureSet E.toLatticeEmbedding.embeddedMeasureSet :=
  D.isTight B.toWilsonActionControlMomentBound

/-- The deterministic pointwise route produces a physical continuum weak
limit without an independently supplied Gibbs expectation estimate. -/
noncomputable def toWeakLimit
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (B : E.WilsonActionControlUniformPointwiseBound scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  D.toWeakLimit B.toWilsonActionControlMomentBound

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.WilsonActionControlUniformPointwiseBound

/-- Public orientation-correct weak-limit constructor from a deterministic
signed-action bound and physical coercivity. -/
noncomputable def
    continuous_compact_oriented_gauge_wilson_weak_limit_of_actionPointwiseBound
    (E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (B : E.WilsonActionControlUniformPointwiseBound scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  B.toWeakLimit D

end

end MathlibAnalytic
end MGAP4D
