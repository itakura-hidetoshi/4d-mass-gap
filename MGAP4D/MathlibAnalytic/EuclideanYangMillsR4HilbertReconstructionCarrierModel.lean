import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Carrier-level Hilbert reconstruction input induced by reflection positivity.

This is not a Hamiltonian spectral-gap theorem.  It packages the carrier that the
reflection-positive reconstruction route can consume: the dependent sum of the
R4 reconstruction input family, together with the reflection-positive,
Euclidean-invariant, and gauge-invariant evidence already produced upstream. -/
structure EuclideanYangMillsR4HilbertReconstructionCarrierModel
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H)
    (F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N)
    (C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F)
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) where
  reconstructionInput :
    EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C
  reconstructionInput_eq : reconstructionInput = I
  hilbertCarrier : Type
  hilbertCarrier_eq_sigmaInput :
    hilbertCarrier = Sigma I.inputModel.reconstructionInputCarrier
  observableCarrier : Type
  observableCarrier_eq_input : observableCarrier = I.inputModel.observableCarrier
  orbitCarrier : Type
  orbitCarrier_eq_input : orbitCarrier = I.inputModel.orbitCarrier
  reflectionPositive : S.measurePackage.reflectionPositive
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariant : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4HilbertReconstructionCarrierModel

/-- Build the carrier-level Hilbert reconstruction input from the R4
reflection-positive reconstruction input closure. -/
def ofReconstructionInputClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H)
    (F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N)
    (C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F)
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) :
    EuclideanYangMillsR4HilbertReconstructionCarrierModel S K R4 A G H N F C I :=
  { reconstructionInput := I
    reconstructionInput_eq := rfl
    hilbertCarrier := Sigma I.inputModel.reconstructionInputCarrier
    hilbertCarrier_eq_sigmaInput := rfl
    observableCarrier := I.inputModel.observableCarrier
    observableCarrier_eq_input := rfl
    orbitCarrier := I.inputModel.orbitCarrier
    orbitCarrier_eq_input := rfl
    reflectionPositive := I.reflectionPositiveInput
    euclideanInvariant := I.euclideanInvariantInput
    gaugeInvariant := I.gaugeInvariantInput }

/-- Extract the reconstructed carrier as the dependent sum of the input family. -/
theorem hilbertCarrier_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
    {F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N}
    {C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F}
    {I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C}
    (M : EuclideanYangMillsR4HilbertReconstructionCarrierModel S K R4 A G H N F C I) :
    M.hilbertCarrier = Sigma I.inputModel.reconstructionInputCarrier :=
  M.hilbertCarrier_eq_sigmaInput

end EuclideanYangMillsR4HilbertReconstructionCarrierModel

end

end MathlibAnalytic
end MGAP4D
