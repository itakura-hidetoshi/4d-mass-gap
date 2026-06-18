import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeObservablePointwiseBound
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonActionExpectation

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A single finite constant bounding the nonnegative Wilson action observable
at every scale and configuration. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonActionUniformPointwiseBound
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding) where
  bound : ENNReal
  bound_ne_top : bound ≠ ⊤
  pointwise_le : ∀ n U, E.wilsonActionObservable n U ≤ bound

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonActionUniformPointwiseBound

/-- Probability normalization converts a deterministic action bound into a
uniform Gibbs expectation bound. -/
def toWilsonActionMomentBound
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (B : E.WilsonActionUniformPointwiseBound) :
    E.WilsonActionMomentBound :=
  { momentBound := B.bound
    momentBound_ne_top := B.bound_ne_top
    uniform_lintegral_le := by
      intro n
      calc
        ∫⁻ U, E.wilsonActionObservable n U
            ∂((E.system n).gibbsProbabilityMeasure :
              Measure (E.system n).base.Configuration) ≤
            ∫⁻ _U, B.bound
              ∂((E.system n).gibbsProbabilityMeasure :
                Measure (E.system n).base.Configuration) :=
          lintegral_mono (B.pointwise_le n)
        _ = B.bound := by simp }

/-- A physical coercive estimate, bounded affine coefficients, and a uniform
pointwise Wilson-action bound imply tightness. -/
theorem isTight
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (B : E.WilsonActionUniformPointwiseBound)
    (C : WilsonActionAffineCoefficientBounds scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    IsTightMeasureSet E.toLatticeEmbedding.embeddedMeasureSet :=
  C.isTight B.toWilsonActionMomentBound D

/-- The deterministic uniform-action route produces a physical continuum weak
limit without a separately supplied expectation estimate. -/
noncomputable def toWeakLimit
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (B : E.WilsonActionUniformPointwiseBound)
    (C : WilsonActionAffineCoefficientBounds scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  C.toWeakLimit B.toWilsonActionMomentBound D

end ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonActionUniformPointwiseBound

/-- Public constructor from deterministic physical coercivity, bounded affine
renormalization coefficients, and a uniform pointwise Wilson-action bound. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_actionPointwiseBound
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (B : E.WilsonActionUniformPointwiseBound)
    (C : WilsonActionAffineCoefficientBounds scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  B.toWeakLimit C D

end

end MathlibAnalytic
end MGAP4D
