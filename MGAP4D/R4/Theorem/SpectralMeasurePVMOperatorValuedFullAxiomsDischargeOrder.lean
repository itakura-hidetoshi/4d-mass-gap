import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFullAxiomsDischargeSurface

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Ordered discharge plan for the future genuine operator-valued R4 PVM.

The order is a proof-engineering object: it fixes which obligations are meant
to be discharged before later obligations may be treated as meaningful.  It is
not a theorem that the obligations have already been discharged. -/
structure SpectralMeasurePVMOperatorValuedFullAxiomsDischargeOrder where
  fullAxiomsDischargeSurfaceReady : Prop
  step1CarrierIndexTargetBeforeLaws : Prop
  step2NormalizationBeforeProjectionUse : Prop
  step3ProjectionValuednessBeforeOrthogonality : Prop
  step4OrthogonalityBeforeSigmaAdditivity : Prop
  step5SigmaAdditivityBeforeSpectralCompatibility : Prop
  step6SpectralCompatibilityBeforeFunctionalCalculus : Prop
  step7FunctionalCalculusBeforeFinalReceipt : Prop
  monotoneNoCollapseAcrossSteps : Prop
  fullAxiomsRemainOpenUntilFinalReceipt : Prop
  finalReceiptNotYetClaimed : Prop

/-- Canonical ordered discharge plan for R4. -/
def spectralMeasurePVMOperatorValuedFullAxiomsDischargeOrder :
    SpectralMeasurePVMOperatorValuedFullAxiomsDischargeOrder :=
  { fullAxiomsDischargeSurfaceReady :=
      SpectralMeasurePVMOperatorValuedFullAxiomsDischargeSurfaceReady
    step1CarrierIndexTargetBeforeLaws := True
    step2NormalizationBeforeProjectionUse := True
    step3ProjectionValuednessBeforeOrthogonality := True
    step4OrthogonalityBeforeSigmaAdditivity := True
    step5SigmaAdditivityBeforeSpectralCompatibility := True
    step6SpectralCompatibilityBeforeFunctionalCalculus := True
    step7FunctionalCalculusBeforeFinalReceipt := True
    monotoneNoCollapseAcrossSteps := SpectralMeasurePVMNoShellToFullCollapseBoundary
    fullAxiomsRemainOpenUntilFinalReceipt := SpectralMeasurePVMFullAxiomsStillOpen
    finalReceiptNotYetClaimed := SpectralMeasurePVMFullAxiomsStillOpen }

/-- Readiness of the ordered full-axiom discharge plan. -/
def SpectralMeasurePVMOperatorValuedFullAxiomsDischargeOrderReady : Prop :=
  spectralMeasurePVMOperatorValuedFullAxiomsDischargeOrder.fullAxiomsDischargeSurfaceReady ∧
  spectralMeasurePVMOperatorValuedFullAxiomsDischargeOrder.step1CarrierIndexTargetBeforeLaws ∧
  spectralMeasurePVMOperatorValuedFullAxiomsDischargeOrder.step2NormalizationBeforeProjectionUse ∧
  spectralMeasurePVMOperatorValuedFullAxiomsDischargeOrder.step3ProjectionValuednessBeforeOrthogonality ∧
  spectralMeasurePVMOperatorValuedFullAxiomsDischargeOrder.step4OrthogonalityBeforeSigmaAdditivity ∧
  spectralMeasurePVMOperatorValuedFullAxiomsDischargeOrder.step5SigmaAdditivityBeforeSpectralCompatibility ∧
  spectralMeasurePVMOperatorValuedFullAxiomsDischargeOrder.step6SpectralCompatibilityBeforeFunctionalCalculus ∧
  spectralMeasurePVMOperatorValuedFullAxiomsDischargeOrder.step7FunctionalCalculusBeforeFinalReceipt ∧
  spectralMeasurePVMOperatorValuedFullAxiomsDischargeOrder.monotoneNoCollapseAcrossSteps ∧
  spectralMeasurePVMOperatorValuedFullAxiomsDischargeOrder.fullAxiomsRemainOpenUntilFinalReceipt ∧
  spectralMeasurePVMOperatorValuedFullAxiomsDischargeOrder.finalReceiptNotYetClaimed

/-- The ordered full-axiom discharge plan is ready. -/
theorem spectral_measure_pvm_operator_valued_full_axioms_discharge_order_ready :
    SpectralMeasurePVMOperatorValuedFullAxiomsDischargeOrderReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_full_axioms_discharge_surface_ready,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_full_axioms_still_open⟩

/-- R4 ordered final pre-closure packet.  This is the strongest current R4
operator-valued PVM staging statement: the staged route and its discharge order
are ready, while final closure remains explicitly future work. -/
def SpectralMeasurePVMOperatorValuedOrderedFinalPreClosurePacket : Prop :=
  SpectralMeasurePVMOperatorValuedFullAxiomsDischargeOrderReady ∧
  SpectralMeasurePVMOperatorValuedFinalPreClosurePacket ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The ordered final pre-closure packet is ready. -/
theorem spectral_measure_pvm_operator_valued_ordered_final_preclosure_packet_ready :
    SpectralMeasurePVMOperatorValuedOrderedFinalPreClosurePacket := by
  exact ⟨
    spectral_measure_pvm_operator_valued_full_axioms_discharge_order_ready,
    spectral_measure_pvm_operator_valued_final_preclosure_packet_ready,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D