import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsHeatBathOrbitMarkovCompression
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFiniteGibbsHeatBathMarkovCompression
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

namespace PositiveTimeObservableContractionSemigroup

variable {P : D.OSPreHilbertData}

/-- A realization of the canonical finite Gibbs forward-orbit path space inside
the actual OS positive-time observable submodule.

The realization preserves time-zero conditioning and intertwines forward path
shift with Euclidean positive-time translation.  The finite Gibbs Markov
compression is generated from these two compatibility laws below. -/
structure FiniteGibbsHeatBathPositiveTimeOrbitRealization
    (L : FiniteLatticeWilsonSystem)
    (O : P.PositiveTimeObservableContractionSemigroup) where
  realize :
    LinearSemigroupOrbitSpace (L.Configuration → ℝ) →ₗ[ℝ]
      D.positiveTimeSubalgebra.toSubmodule
  condition :
    D.positiveTimeSubalgebra.toSubmodule →ₗ[ℝ]
      (L.Configuration → ℝ)
  condition_realize : ∀ F,
    condition (realize F) = F 0
  translate_realize : ∀ (t : NNReal) F,
    O.translatedPositiveTimeSubmodule t (realize F) =
      realize (linearSemigroupOrbitTranslate t F)

namespace FiniteGibbsHeatBathPositiveTimeOrbitRealization

variable {L : FiniteLatticeWilsonSystem}
variable {O : P.PositiveTimeObservableContractionSemigroup}

/-- The canonical finite Gibbs orbit realization theorem-generates the concrete
positive-time Markov compression used by the OS graph-transport lane. -/
noncomputable def toPositiveTimeMarkovCompression
    (R : FiniteGibbsHeatBathPositiveTimeOrbitRealization L O) :
    FiniteGibbsHeatBathPositiveTimeMarkovCompression L O where
  toLinearMarkovCompression :=
    { lift := R.realize.comp
        L.gibbsObservableHeatBathOrbitMarkovCompression.lift
      condition := R.condition
      condition_lift := by
        intro f
        rw [LinearMap.comp_apply, R.condition_realize]
        simpa only [
          finite_lattice_gibbsObservableHeatBathOrbitMarkovCompression_condition_apply]
          using
            L.gibbsObservableHeatBathOrbitMarkovCompression.condition_lift f
      condition_translate_lift := by
        intro t f
        rw [LinearMap.comp_apply, R.translate_realize,
          R.condition_realize]
        simpa only [
          finite_lattice_gibbsObservableHeatBathOrbitMarkovCompression_condition_apply]
          using
            L.gibbsObservableHeatBathOrbitMarkovCompression
              |>.condition_translate_lift t f }

@[simp] theorem toPositiveTimeMarkovCompression_lift_apply
    (R : FiniteGibbsHeatBathPositiveTimeOrbitRealization L O)
    (f : L.Configuration → ℝ) :
    R.toPositiveTimeMarkovCompression.lift f =
      R.realize
        (L.gibbsObservableHeatBathOrbitMarkovCompression.lift f) :=
  rfl

@[simp] theorem toPositiveTimeMarkovCompression_condition_apply
    (R : FiniteGibbsHeatBathPositiveTimeOrbitRealization L O)
    (F : D.positiveTimeSubalgebra.toSubmodule) :
    R.toPositiveTimeMarkovCompression.condition F = R.condition F :=
  rfl

/-- Time-zero conditioning of the generated OS-positive-time lift returns the
original finite Gibbs observable. -/
@[simp] theorem condition_generated_lift
    (R : FiniteGibbsHeatBathPositiveTimeOrbitRealization L O)
    (f : L.Configuration → ℝ) :
    R.condition (R.toPositiveTimeMarkovCompression.lift f) = f :=
  R.toPositiveTimeMarkovCompression.toLinearMarkovCompression.condition_lift f

/-- Conditioning after Euclidean translation of the generated lift is exactly
the concrete finite Gibbs heat-bath evolution. -/
theorem condition_translate_generated_lift
    (R : FiniteGibbsHeatBathPositiveTimeOrbitRealization L O)
    (t : NNReal)
    (f : L.Configuration → ℝ) :
    R.condition
        (O.translatedPositiveTimeSubmodule t
          (R.toPositiveTimeMarkovCompression.lift f)) =
      L.gibbsObservableHeatBathSpectralSemigroup t f :=
  R.toPositiveTimeMarkovCompression.toLinearMarkovCompression
    |>.condition_translate_lift t f

end FiniteGibbsHeatBathPositiveTimeOrbitRealization
end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
