import MGAP4D.MathlibAnalytic.WightmanOSPVMPhysicalDifferenceQuotientDerived

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Canonical PVM open-support identification and a positive Hamiltonian mass gap
supply positive spectral support automatically, so the physical positive
semigroup spectral action follows directly from the scalar Laplace formula and
OS exchange. -/
noncomputable def EuclideanYangMillsOSPhysicalTimeTranslation.toPositiveSemigroupSpectralActionOfLaplaceExchangeAndGap
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M.toExplicitModel)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M.toExplicitModel)
    {m : ℝ} (hGap : M.toExplicitModel.HasMassGap m)
    (L : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      M.toExplicitModel A.toScalarSpectralRealization T.toEuclideanTimeSemigroup)
    (hExchange : T.ReflectionTimeTranslationExchange) :
    EuclideanYangMillsOSPhysicalPositiveSemigroupSpectralAction T :=
  T.toPositiveSemigroupSpectralActionOfLaplaceAndExchange
    A
    (ExplicitWightmanOSCanonicalPVMOpenSupportBridge.toPositiveSpectralSupport
      A B hGap)
    L hExchange

/-- The canonical PVM open-support bridge and mass gap now feed the full
Laplace--semigroup--generator route, constructing the actual canonical PVM
coordinate graph without taking positive spectral support or a difference-
quotient action law as independent physical inputs. -/
noncomputable def EuclideanYangMillsOSPhysicalTimeTranslation.toCanonicalPVMCoordinateGraphOfLaplaceExchangeAndGap
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M.toExplicitModel)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M.toExplicitModel)
    {m : ℝ} (hGap : M.toExplicitModel.HasMassGap m)
    (L : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      M.toExplicitModel A.toScalarSpectralRealization T.toEuclideanTimeSemigroup)
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (hExchange : T.ReflectionTimeTranslationExchange) :
    ExplicitWightmanOSCanonicalRestrictedPVMCoordinateGraph M.toExplicitModel :=
  (T.toPositiveSemigroupSpectralActionOfLaplaceExchangeAndGap
      A B hGap L hExchange)
    |>.toCoordinateGraph G hExchange

end

end MathlibAnalytic
end MGAP4D
