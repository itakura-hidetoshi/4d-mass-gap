import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalSemigroupBase

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

structure EuclideanYangMillsOSPhysicalTimeTranslationCore
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) where
  configurationTranslate :
    ℝ → S.measurePackage.configurationSpace →
      S.measurePackage.configurationSpace
  observableTranslate :
    ℝ → M.observables.PositiveTimeObservable →ₗ[ℝ]
      M.observables.PositiveTimeObservable
  realization_translate :
    ∀ (t : ℝ) (F : M.observables.PositiveTimeObservable)
      (omega : S.measurePackage.configurationSpace),
      M.observables.realization (observableTranslate t F) omega =
        M.observables.realization F (configurationTranslate t omega)
  operator :
    ℝ → M.observables.PhysicalHilbert →L[ℝ]
      M.observables.PhysicalHilbert
  operator_on_dense_state :
    ∀ (t : ℝ) (F : M.observables.PositiveTimeObservable), 0 ≤ t →
      operator t (M.observables.physicalState F) =
        M.observables.physicalState (observableTranslate t F)
  zero_operator : ∀ psi, operator 0 psi = psi
  add_operator :
    ∀ (s t : ℝ), 0 ≤ s → 0 ≤ t → ∀ psi,
      operator (s + t) psi = operator s (operator t psi)
  vacuum_fixed :
    ∀ (t : ℝ), 0 ≤ t → operator t M.vacuum = M.vacuum
  contraction :
    ∀ (t : ℝ), 0 ≤ t → ∀ psi, ‖operator t psi‖ ≤ ‖psi‖

def EuclideanYangMillsOSPhysicalTimeTranslationCore.toSemigroup
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslationCore M) :
    EuclideanYangMillsOSPhysicalSemigroup M :=
  { operator := T.operator
    zero_apply := T.zero_operator
    add_apply := T.add_operator
    vacuum_fixed := T.vacuum_fixed
    contraction := T.contraction }

end

end MathlibAnalytic
end MGAP4D
