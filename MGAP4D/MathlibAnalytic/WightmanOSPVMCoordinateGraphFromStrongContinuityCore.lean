import MGAP4D.MathlibAnalytic.WightmanOSPVMCoordinateGraphFromGap
import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalStrongContinuityCore

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Forget the support-preservation fields of the full physical time translation
package while retaining the exact configuration, observable, and Hilbert-space
operator data used by the lightweight strong-continuity core. -/
def EuclideanYangMillsOSPhysicalTimeTranslation.toCore
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) :
    EuclideanYangMillsOSPhysicalTimeTranslationCore M where
  configurationTranslate := T.configurationTranslate
  observableTranslate := T.observableTranslate
  realization_translate := T.realization_translate
  operator := T.operator
  operator_on_dense_state := T.operator_on_dense_state
  zero_operator := T.zero_operator
  add_operator := T.add_operator
  vacuum_fixed := T.vacuum_fixed
  contraction := T.contraction

@[simp] theorem EuclideanYangMillsOSPhysicalTimeTranslation.toCore_operator
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) :
    T.toCore.operator = T.operator :=
  rfl

/-- The lightweight strong-continuity package is already exactly the physical
Hamiltonian-generator package once its operator family is identified with the
full time-translation structure. -/
noncomputable def EuclideanYangMillsOSPhysicalStrongContinuityCore.toHamiltonianGenerator
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (C : EuclideanYangMillsOSPhysicalStrongContinuityCore T.toCore) :
    EuclideanYangMillsOSPhysicalHamiltonianGenerator T where
  stronglyContinuousAtZero := by
    intro psi
    simpa [EuclideanYangMillsOSPhysicalTimeTranslation.toCore] using
      C.stronglyContinuousAtZero psi
  generatorLimit := by
    intro x
    simpa [EuclideanYangMillsOSPhysicalTimeTranslation.toCore] using
      C.rightDerivativeLimit x

/-- Consequently the pure-PVM gap route consumes the actual strong-continuity
core directly; an independently postulated Hamiltonian-generator package is no
longer needed. -/
noncomputable def EuclideanYangMillsOSPhysicalTimeTranslation.toCanonicalPVMCoordinateGraphOfLaplaceExchangeGapAndStrongContinuity
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M.toExplicitModel)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M.toExplicitModel)
    {m : ℝ} (hGap : M.toExplicitModel.HasMassGap m)
    (L : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      M.toExplicitModel A.toScalarSpectralRealization T.toEuclideanTimeSemigroup)
    (C : EuclideanYangMillsOSPhysicalStrongContinuityCore T.toCore)
    (hExchange : T.ReflectionTimeTranslationExchange) :
    ExplicitWightmanOSCanonicalRestrictedPVMCoordinateGraph M.toExplicitModel :=
  T.toCanonicalPVMCoordinateGraphOfLaplaceExchangeAndGap
    A B hGap L C.toHamiltonianGenerator hExchange

end

end MathlibAnalytic
end MGAP4D
