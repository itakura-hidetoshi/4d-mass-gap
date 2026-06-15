import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticReflectionLimitTransfer

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable
  (W : FiniteWilsonOSAutomaticApproximationFamily)
  (D : FiniteWilsonOSAutomaticReflectionLimitData W)

/-- Compile gate for theorem-generated nonnegativity at every finite Wilson
scale and for every transported observable. -/
theorem finite_wilson_reflection_form_nonneg_compile_smoke
    (n : ℕ) (O : D.Observable) :
    0 ≤ (W.reflectionData (D.scale n)).wilsonReflectionForm
      (D.finiteObservable n O) :=
  finite_wilson_os_automatic_reflection_form_nonneg W D n O

/-- Compile gate for conversion to the generic reflection-limit package. -/
noncomputable def finite_wilson_reflection_limit_data_compile_smoke :
    EuclideanYangMillsReflectionPositivityLimitData :=
  D.toReflectionPositivityLimitData

/-- Compile gate for continuum reflection positivity obtained from actual finite
Wilson reflection forms and pointwise convergence. -/
theorem finite_wilson_reflection_positive_limit_compile_smoke :
    D.ContinuumReflectionPositive :=
  finite_wilson_os_automatic_reflection_positivity_passes_to_limit D

/-- Compile gate identifying the concrete and generic continuum predicates. -/
theorem finite_wilson_reflection_limit_predicate_compile_smoke :
    D.toReflectionPositivityLimitData.ContinuumReflectionPositive ↔
      D.ContinuumReflectionPositive :=
  finite_wilson_os_automatic_reflection_limit_matches_generic D

end

end MathlibAnalytic
end MGAP4D
