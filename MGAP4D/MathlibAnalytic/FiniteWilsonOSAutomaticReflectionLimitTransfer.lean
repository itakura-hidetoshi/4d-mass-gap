import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticApproximationFamily
import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitOSPropertyTransfer

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- A sequential choice of finite Wilson systems, a common continuum observable
carrier, and pointwise convergence of the actual finite Wilson reflection forms.

The nonnegativity of every finite form is not an input: it is generated from the
Gram/character reflection certificate already contained in the automatic Wilson
family. -/
structure FiniteWilsonOSAutomaticReflectionLimitData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  Observable : Type
  scale : ℕ → W.index
  finiteObservable :
    (n : ℕ) → Observable →
      (W.reflectionData (scale n)).PositiveConfiguration → ℝ
  continuumReflectionForm : Observable → ℝ
  reflectionFormConverges :
    ∀ O : Observable,
      Tendsto
        (fun n : ℕ =>
          (W.reflectionData (scale n)).wilsonReflectionForm
            (finiteObservable n O))
        atTop (nhds (continuumReflectionForm O))

/-- The concrete continuum reflection-positivity statement carried by a
sequential finite Wilson approximation. -/
def FiniteWilsonOSAutomaticReflectionLimitData.ContinuumReflectionPositive
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticReflectionLimitData W) : Prop :=
  ∀ O : D.Observable, 0 ≤ D.continuumReflectionForm O

/-- Every finite reflection form in the chosen sequence is nonnegative by the
canonical finite Wilson Gram construction. -/
theorem finite_wilson_os_automatic_reflection_form_nonneg
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonOSAutomaticReflectionLimitData W)
    (n : ℕ) (O : D.Observable) :
    0 ≤ (W.reflectionData (D.scale n)).wilsonReflectionForm
      (D.finiteObservable n O) := by
  exact finite_wilson_os_automatic_family_actualReflectionPositive W
    (D.scale n) (D.finiteObservable n O)

/-- Convert the concrete finite Wilson sequence into the generic pointwise
reflection-positivity limit datum.  The finite positivity field is theorem
generated rather than separately assumed. -/
noncomputable def
    FiniteWilsonOSAutomaticReflectionLimitData.toReflectionPositivityLimitData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticReflectionLimitData W) :
    EuclideanYangMillsReflectionPositivityLimitData :=
  { Observable := D.Observable
    finiteReflectionForm := fun n O =>
      (W.reflectionData (D.scale n)).wilsonReflectionForm
        (D.finiteObservable n O)
    continuumReflectionForm := D.continuumReflectionForm
    finiteReflectionPositive := fun n O =>
      finite_wilson_os_automatic_reflection_form_nonneg W D n O
    reflectionFormConverges := D.reflectionFormConverges }

/-- Pointwise convergence of actual finite Wilson reflection forms transfers OS
reflection positivity to the continuum form. -/
theorem finite_wilson_os_automatic_reflection_positivity_passes_to_limit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticReflectionLimitData W) :
    D.ContinuumReflectionPositive := by
  exact euclidean_yang_mills_reflection_positivity_passes_to_limit
    D.toReflectionPositivityLimitData

/-- The concrete theorem is definitionally the generic closed-order limit
theorem specialized to Wilson reflection forms. -/
theorem finite_wilson_os_automatic_reflection_limit_matches_generic
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticReflectionLimitData W) :
    D.toReflectionPositivityLimitData.ContinuumReflectionPositive ↔
      D.ContinuumReflectionPositive := by
  rfl

end

end MathlibAnalytic
end MGAP4D
