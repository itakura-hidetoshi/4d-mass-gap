import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionCarrierModel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4HilbertReconstructionCarrierModel

/-- Bundled outputs for the R4 Hilbert reconstruction carrier input. -/
def hilbertCarrierOutputs
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
    (M : EuclideanYangMillsR4HilbertReconstructionCarrierModel S K R4 A G H N F C I) : Prop :=
  M.hilbertCarrier = Sigma I.inputModel.reconstructionInputCarrier ∧
    M.observableCarrier = I.inputModel.observableCarrier ∧
      M.orbitCarrier = I.inputModel.orbitCarrier ∧
        S.measurePackage.reflectionPositive ∧
          G.orbitModel.euclideanInvariantConstruction ∧
            G.orbitModel.gaugeInvariantConstruction

/-- The R4 Hilbert reconstruction carrier model proves its bundled outputs. -/
theorem hilbertCarrierOutputs_holds
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
    M.hilbertCarrierOutputs :=
  ⟨M.hilbertCarrier_eq_sigmaInput,
    M.observableCarrier_eq_input,
    M.orbitCarrier_eq_input,
    M.reflectionPositive,
    M.euclideanInvariant,
    M.gaugeInvariant⟩

/-- The R4 reflection-positive reconstruction input closure induces a Hilbert
reconstruction carrier model. -/
theorem nonempty_ofReconstructionInputClosure
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
    Nonempty (EuclideanYangMillsR4HilbertReconstructionCarrierModel S K R4 A G H N F C I) :=
  ⟨ofReconstructionInputClosure S K R4 A G H N F C I⟩

end EuclideanYangMillsR4HilbertReconstructionCarrierModel

end

end MathlibAnalytic
end MGAP4D
