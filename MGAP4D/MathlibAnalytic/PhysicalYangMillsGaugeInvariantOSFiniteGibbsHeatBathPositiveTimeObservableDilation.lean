import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsHeatBathSpectralSemigroup
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPositiveTimeObservableSemigroup
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- Repackage a positive-time submodule element as the original positive-time
subalgebra element. -/
def positiveTimeSubalgebraOfSubmodule
    (F : D.positiveTimeSubalgebra.toSubmodule) :
    D.positiveTimeSubalgebra :=
  ⟨F.1, F.2⟩

/-- Repackage positive-time observables in an OS carrier, bundled as a real-linear
map through the explicit positive-time submodule.  This is canonical for every
OS state on the same positive-time observable algebra. -/
noncomputable def carrierOfPositiveTimeLinearMap
    (P : D.OSPreHilbertData) :
    D.positiveTimeSubalgebra.toSubmodule →ₗ[ℝ] P.Carrier where
  toFun := fun F =>
    P.carrierOfPositiveTime (positiveTimeSubalgebraOfSubmodule F)
  map_add' := by
    intro F G
    apply Carrier.observable_injective P
    rfl
  map_smul' := by
    intro r F
    apply Carrier.observable_injective P
    rfl

@[simp] theorem carrierOfPositiveTimeLinearMap_apply
    (P : D.OSPreHilbertData)
    (F : D.positiveTimeSubalgebra.toSubmodule) :
    P.carrierOfPositiveTimeLinearMap F =
      P.carrierOfPositiveTime (positiveTimeSubalgebraOfSubmodule F) :=
  rfl

namespace PositiveTimeObservableContractionSemigroup

variable {P : D.OSPreHilbertData}

/-- A positive-time observable dilation of the concrete finite Gibbs heat-bath
semigroup.

The finite observable is represented by a genuine positive-time continuum
observable.  Euclidean positive-time translation of that representative is
required to equal the representative of the finite Gibbs heat-bath evolution.
The carrier-valued lift used by graph transport is generated canonically below. -/
structure FiniteGibbsHeatBathPositiveTimeObservableDilation
    (L : FiniteLatticeWilsonSystem)
    (O : P.PositiveTimeObservableContractionSemigroup) where
  lift :
    (L.Configuration → ℝ) →ₗ[ℝ] D.positiveTimeSubalgebra.toSubmodule
  translate_lift : ∀ (t : NNReal) (f : L.Configuration → ℝ),
    O.translate t
        (positiveTimeSubalgebraOfSubmodule (lift f)) =
      positiveTimeSubalgebraOfSubmodule
        (lift (L.gibbsObservableHeatBathSpectralSemigroup t f))

namespace FiniteGibbsHeatBathPositiveTimeObservableDilation

variable {L : FiniteLatticeWilsonSystem}
variable {O : P.PositiveTimeObservableContractionSemigroup}

/-- The OS-carrier realization generated from a positive-time observable
dilation. -/
noncomputable def carrierMap
    (K : FiniteGibbsHeatBathPositiveTimeObservableDilation L O) :
    (L.Configuration → ℝ) →ₗ[ℝ] P.Carrier :=
  P.carrierOfPositiveTimeLinearMap.comp K.lift

@[simp] theorem carrierMap_apply
    (K : FiniteGibbsHeatBathPositiveTimeObservableDilation L O)
    (f : L.Configuration → ℝ) :
    K.carrierMap f =
      P.carrierOfPositiveTime
        (positiveTimeSubalgebraOfSubmodule (K.lift f)) :=
  rfl

/-- The generated carrier map represents exactly the positive-time observable
supplied by the dilation. -/
@[simp] theorem positiveTimeElement_carrierMap
    (K : FiniteGibbsHeatBathPositiveTimeObservableDilation L O)
    (f : L.Configuration → ℝ) :
    P.positiveTimeElement (K.carrierMap f) =
      positiveTimeSubalgebraOfSubmodule (K.lift f) := by
  rw [carrierMap_apply, P.positiveTimeElement_carrierOfPositiveTime]

/-- Dilation covariance theorem-generates the carrier-side observable
translation intertwining required by finite Wilson graph transport. -/
theorem translate_positiveTimeElement_carrierMap
    (K : FiniteGibbsHeatBathPositiveTimeObservableDilation L O)
    (t : NNReal) (f : L.Configuration → ℝ) :
    O.translate t (P.positiveTimeElement (K.carrierMap f)) =
      P.positiveTimeElement
        (K.carrierMap
          (L.gibbsObservableHeatBathSpectralSemigroup t f)) := by
  calc
    O.translate t (P.positiveTimeElement (K.carrierMap f)) =
        O.translate t
          (positiveTimeSubalgebraOfSubmodule (K.lift f)) := by
      rw [K.positiveTimeElement_carrierMap]
    _ = positiveTimeSubalgebraOfSubmodule
          (K.lift
            (L.gibbsObservableHeatBathSpectralSemigroup t f)) :=
      K.translate_lift t f
    _ = P.positiveTimeElement
          (K.carrierMap
            (L.gibbsObservableHeatBathSpectralSemigroup t f)) := by
      symm
      exact K.positiveTimeElement_carrierMap _

end FiniteGibbsHeatBathPositiveTimeObservableDilation
end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
