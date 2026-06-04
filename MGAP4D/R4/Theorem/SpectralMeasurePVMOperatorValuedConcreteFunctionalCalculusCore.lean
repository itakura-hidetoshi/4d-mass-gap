import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedConcreteSpectralCompatibilityCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Minimal bounded-Borel-function surface for the concrete two-index R4
functional-calculus discharge.  This is not a genuine Borel functional calculus;
it is the first closed computational table that later mathlib/Hilbert layers can
replace. -/
inductive SpectralMeasurePVMConcreteBoundedBorelFunction where
  | zero
  | one
  | identity
  deriving DecidableEq

/-- Indicator function of a concrete spectral index on the two-index surface. -/
def spectralMeasurePVMConcreteIndicatorFunction :
    SpectralMeasurePVMConcreteIndex → SpectralMeasurePVMConcreteBoundedBorelFunction
  | SpectralMeasurePVMConcreteIndex.empty =>
      SpectralMeasurePVMConcreteBoundedBorelFunction.zero
  | SpectralMeasurePVMConcreteIndex.whole =>
      SpectralMeasurePVMConcreteBoundedBorelFunction.one

/-- Minimal concrete functional-calculus table. -/
def spectralMeasurePVMConcreteFunctionalCalculus :
    SpectralMeasurePVMConcreteBoundedBorelFunction →
      SpectralMeasurePVMConcreteBoundedOperator
  | SpectralMeasurePVMConcreteBoundedBorelFunction.zero =>
      SpectralMeasurePVMConcreteBoundedOperator.zero
  | SpectralMeasurePVMConcreteBoundedBorelFunction.one =>
      SpectralMeasurePVMConcreteBoundedOperator.identity
  | SpectralMeasurePVMConcreteBoundedBorelFunction.identity =>
      spectralMeasurePVMConcreteSpectralOperator

/-- The indicator of a concrete index recovers the corresponding spectral
projection under the concrete functional calculus. -/
theorem spectral_measure_pvm_concrete_indicator_function_projection
    (i : SpectralMeasurePVMConcreteIndex) :
    spectralMeasurePVMConcreteFunctionalCalculus
        (spectralMeasurePVMConcreteIndicatorFunction i) =
      spectralMeasurePVMConcreteSpectralProjection i := by
  cases i <;> rfl

/-- The zero function is sent to the zero operator. -/
theorem spectral_measure_pvm_concrete_functional_calculus_zero :
    spectralMeasurePVMConcreteFunctionalCalculus
        SpectralMeasurePVMConcreteBoundedBorelFunction.zero =
      SpectralMeasurePVMConcreteBoundedOperator.zero := by
  rfl

/-- The one function is sent to the identity operator. -/
theorem spectral_measure_pvm_concrete_functional_calculus_one :
    spectralMeasurePVMConcreteFunctionalCalculus
        SpectralMeasurePVMConcreteBoundedBorelFunction.one =
      SpectralMeasurePVMConcreteBoundedOperator.identity := by
  rfl

/-- The identity function is sent to the concrete spectral operator. -/
theorem spectral_measure_pvm_concrete_functional_calculus_identity :
    spectralMeasurePVMConcreteFunctionalCalculus
        SpectralMeasurePVMConcreteBoundedBorelFunction.identity =
      spectralMeasurePVMConcreteSpectralOperator := by
  rfl

/-- The concrete operator-integral interface agrees with the functional calculus
on the identity function. -/
theorem spectral_measure_pvm_concrete_functional_calculus_operator_integral_compatibility :
    spectralMeasurePVMConcreteFunctionalCalculus
        SpectralMeasurePVMConcreteBoundedBorelFunction.identity =
      spectralMeasurePVMConcreteIdentityFunctionIntegral := by
  rfl

/-- The concrete functional calculus recovers the spectral operator from the
identity function. -/
theorem spectral_measure_pvm_concrete_functional_calculus_identity_recovers_operator :
    spectralMeasurePVMConcreteFunctionalCalculus
        SpectralMeasurePVMConcreteBoundedBorelFunction.identity =
      spectralMeasurePVMConcreteSpectralOperator := by
  rfl

/-- Concrete bounded-Borel-function interface target. -/
def SpectralMeasurePVMConcreteBoundedBorelFunctionInterfaceTarget : Prop :=
  spectralMeasurePVMConcreteFunctionalCalculus
      SpectralMeasurePVMConcreteBoundedBorelFunction.zero =
    SpectralMeasurePVMConcreteBoundedOperator.zero ∧
  spectralMeasurePVMConcreteFunctionalCalculus
      SpectralMeasurePVMConcreteBoundedBorelFunction.one =
    SpectralMeasurePVMConcreteBoundedOperator.identity ∧
  spectralMeasurePVMConcreteFunctionalCalculus
      SpectralMeasurePVMConcreteBoundedBorelFunction.identity =
    spectralMeasurePVMConcreteSpectralOperator

/-- Concrete indicator-function projection target. -/
def SpectralMeasurePVMConcreteIndicatorFunctionProjectionTarget : Prop :=
  ∀ i : SpectralMeasurePVMConcreteIndex,
    spectralMeasurePVMConcreteFunctionalCalculus
        (spectralMeasurePVMConcreteIndicatorFunction i) =
      spectralMeasurePVMConcreteSpectralProjection i

/-- Concrete simple-function calculus target.  At the two-index stage, the simple
functions are represented by the three constructors of
`SpectralMeasurePVMConcreteBoundedBorelFunction`. -/
def SpectralMeasurePVMConcreteSimpleFunctionCalculusTarget : Prop :=
  SpectralMeasurePVMConcreteBoundedBorelFunctionInterfaceTarget ∧
  SpectralMeasurePVMConcreteIndicatorFunctionProjectionTarget

/-- Concrete bounded-limit calculus target.  The present finite three-function
surface has no nontrivial limiting process; the target is recorded as stability
of the already closed simple-function table. -/
def SpectralMeasurePVMConcreteBoundedLimitCalculusTarget : Prop :=
  SpectralMeasurePVMConcreteSimpleFunctionCalculusTarget

/-- Concrete operator-integral compatibility target. -/
def SpectralMeasurePVMConcreteFunctionalCalculusOperatorIntegralCompatibilityTarget : Prop :=
  spectralMeasurePVMConcreteFunctionalCalculus
      SpectralMeasurePVMConcreteBoundedBorelFunction.identity =
    spectralMeasurePVMConcreteIdentityFunctionIntegral

/-- Concrete identity-function recovery target for the functional calculus layer. -/
def SpectralMeasurePVMConcreteFunctionalCalculusIdentityFunctionRecoveryTarget : Prop :=
  spectralMeasurePVMConcreteFunctionalCalculus
      SpectralMeasurePVMConcreteBoundedBorelFunction.identity =
    spectralMeasurePVMConcreteSpectralOperator

/-- Concrete spectral-projection membership recovery target. -/
def SpectralMeasurePVMConcreteSpectralProjectionMembershipRecoveredTarget : Prop :=
  SpectralMeasurePVMConcreteIndicatorFunctionProjectionTarget

/-- Concrete functional-calculus target feeding the final PVM receipt layer. -/
def SpectralMeasurePVMConcreteFunctionalCalculusFeedsFinalPVMReceiptTarget : Prop :=
  SpectralMeasurePVMConcreteBoundedBorelFunctionInterfaceTarget ∧
  SpectralMeasurePVMConcreteIndicatorFunctionProjectionTarget ∧
  SpectralMeasurePVMConcreteFunctionalCalculusOperatorIntegralCompatibilityTarget ∧
  SpectralMeasurePVMOperatorValuedConcreteSpectralCompatibilityCoreReady

/-- Guard preventing the final PVM receipt from being used before functional
calculus and spectral compatibility have both been concretely recorded. -/
def SpectralMeasurePVMConcreteNoFinalReceiptBeforeFunctionalCalculusTarget : Prop :=
  SpectralMeasurePVMConcreteFunctionalCalculusFeedsFinalPVMReceiptTarget ∧
  SpectralMeasurePVMOperatorValuedConcreteSpectralCompatibilityCoreReady

/-- Concrete functional-calculus discharge receipt. -/
def SpectralMeasurePVMConcreteFunctionalCalculusDischargeReceiptTarget : Prop :=
  SpectralMeasurePVMConcreteBoundedBorelFunctionInterfaceTarget ∧
  SpectralMeasurePVMConcreteIndicatorFunctionProjectionTarget ∧
  SpectralMeasurePVMConcreteSimpleFunctionCalculusTarget ∧
  SpectralMeasurePVMConcreteBoundedLimitCalculusTarget ∧
  SpectralMeasurePVMConcreteFunctionalCalculusOperatorIntegralCompatibilityTarget ∧
  SpectralMeasurePVMConcreteFunctionalCalculusIdentityFunctionRecoveryTarget ∧
  SpectralMeasurePVMConcreteSpectralProjectionMembershipRecoveredTarget ∧
  SpectralMeasurePVMConcreteFunctionalCalculusFeedsFinalPVMReceiptTarget ∧
  SpectralMeasurePVMConcreteNoFinalReceiptBeforeFunctionalCalculusTarget ∧
  SpectralMeasurePVMOperatorValuedConcreteSpectralCompatibilityCoreReady ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Concrete final-PVM-receipt target.  This remains a non-closure target: it
collects the concrete functional-calculus receipt while preserving the open full
axioms boundary. -/
def SpectralMeasurePVMConcreteFinalPVMReceiptTarget : Prop :=
  SpectralMeasurePVMConcreteFunctionalCalculusDischargeReceiptTarget ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The concrete bounded-Borel-function interface is ready. -/
theorem spectral_measure_pvm_concrete_bounded_borel_function_interface_target_ready :
    SpectralMeasurePVMConcreteBoundedBorelFunctionInterfaceTarget := by
  exact ⟨
    spectral_measure_pvm_concrete_functional_calculus_zero,
    spectral_measure_pvm_concrete_functional_calculus_one,
    spectral_measure_pvm_concrete_functional_calculus_identity⟩

/-- The concrete indicator-function projection target is ready. -/
theorem spectral_measure_pvm_concrete_indicator_function_projection_target_ready :
    SpectralMeasurePVMConcreteIndicatorFunctionProjectionTarget := by
  exact spectral_measure_pvm_concrete_indicator_function_projection

/-- The concrete simple-function calculus target is ready. -/
theorem spectral_measure_pvm_concrete_simple_function_calculus_target_ready :
    SpectralMeasurePVMConcreteSimpleFunctionCalculusTarget := by
  exact ⟨
    spectral_measure_pvm_concrete_bounded_borel_function_interface_target_ready,
    spectral_measure_pvm_concrete_indicator_function_projection_target_ready⟩

/-- The concrete bounded-limit calculus target is ready. -/
theorem spectral_measure_pvm_concrete_bounded_limit_calculus_target_ready :
    SpectralMeasurePVMConcreteBoundedLimitCalculusTarget := by
  exact spectral_measure_pvm_concrete_simple_function_calculus_target_ready

/-- The concrete operator-integral compatibility target is ready. -/
theorem spectral_measure_pvm_concrete_functional_calculus_operator_integral_compatibility_target_ready :
    SpectralMeasurePVMConcreteFunctionalCalculusOperatorIntegralCompatibilityTarget := by
  exact spectral_measure_pvm_concrete_functional_calculus_operator_integral_compatibility

/-- The concrete identity-function recovery target is ready. -/
theorem spectral_measure_pvm_concrete_functional_calculus_identity_function_recovery_target_ready :
    SpectralMeasurePVMConcreteFunctionalCalculusIdentityFunctionRecoveryTarget := by
  exact spectral_measure_pvm_concrete_functional_calculus_identity_recovers_operator

/-- The concrete spectral-projection membership recovery target is ready. -/
theorem spectral_measure_pvm_concrete_spectral_projection_membership_recovered_target_ready :
    SpectralMeasurePVMConcreteSpectralProjectionMembershipRecoveredTarget := by
  exact spectral_measure_pvm_concrete_indicator_function_projection_target_ready

/-- The concrete functional-calculus-to-final-receipt handoff target is ready. -/
theorem spectral_measure_pvm_concrete_functional_calculus_feeds_final_pvm_receipt_target_ready :
    SpectralMeasurePVMConcreteFunctionalCalculusFeedsFinalPVMReceiptTarget := by
  exact ⟨
    spectral_measure_pvm_concrete_bounded_borel_function_interface_target_ready,
    spectral_measure_pvm_concrete_indicator_function_projection_target_ready,
    spectral_measure_pvm_concrete_functional_calculus_operator_integral_compatibility_target_ready,
    spectral_measure_pvm_operator_valued_concrete_spectral_compatibility_core_ready⟩

/-- The guard against premature final receipt is ready. -/
theorem spectral_measure_pvm_concrete_no_final_receipt_before_functional_calculus_target_ready :
    SpectralMeasurePVMConcreteNoFinalReceiptBeforeFunctionalCalculusTarget := by
  exact ⟨
    spectral_measure_pvm_concrete_functional_calculus_feeds_final_pvm_receipt_target_ready,
    spectral_measure_pvm_operator_valued_concrete_spectral_compatibility_core_ready⟩

/-- The concrete functional-calculus discharge receipt is ready. -/
theorem spectral_measure_pvm_concrete_functional_calculus_discharge_receipt_target_ready :
    SpectralMeasurePVMConcreteFunctionalCalculusDischargeReceiptTarget := by
  exact ⟨
    spectral_measure_pvm_concrete_bounded_borel_function_interface_target_ready,
    spectral_measure_pvm_concrete_indicator_function_projection_target_ready,
    spectral_measure_pvm_concrete_simple_function_calculus_target_ready,
    spectral_measure_pvm_concrete_bounded_limit_calculus_target_ready,
    spectral_measure_pvm_concrete_functional_calculus_operator_integral_compatibility_target_ready,
    spectral_measure_pvm_concrete_functional_calculus_identity_function_recovery_target_ready,
    spectral_measure_pvm_concrete_spectral_projection_membership_recovered_target_ready,
    spectral_measure_pvm_concrete_functional_calculus_feeds_final_pvm_receipt_target_ready,
    spectral_measure_pvm_concrete_no_final_receipt_before_functional_calculus_target_ready,
    spectral_measure_pvm_operator_valued_concrete_spectral_compatibility_core_ready,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The concrete final-PVM-receipt target is ready without closing the genuine full
PVM theorem. -/
theorem spectral_measure_pvm_concrete_final_pvm_receipt_target_ready :
    SpectralMeasurePVMConcreteFinalPVMReceiptTarget := by
  exact ⟨
    spectral_measure_pvm_concrete_functional_calculus_discharge_receipt_target_ready,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Concrete functional-calculus core. -/
def SpectralMeasurePVMOperatorValuedConcreteFunctionalCalculusCoreReady : Prop :=
  SpectralMeasurePVMConcreteBoundedBorelFunctionInterfaceTarget ∧
  SpectralMeasurePVMConcreteIndicatorFunctionProjectionTarget ∧
  SpectralMeasurePVMConcreteSimpleFunctionCalculusTarget ∧
  SpectralMeasurePVMConcreteBoundedLimitCalculusTarget ∧
  SpectralMeasurePVMConcreteFunctionalCalculusOperatorIntegralCompatibilityTarget ∧
  SpectralMeasurePVMConcreteFunctionalCalculusIdentityFunctionRecoveryTarget ∧
  SpectralMeasurePVMConcreteSpectralProjectionMembershipRecoveredTarget ∧
  SpectralMeasurePVMConcreteFunctionalCalculusFeedsFinalPVMReceiptTarget ∧
  SpectralMeasurePVMConcreteNoFinalReceiptBeforeFunctionalCalculusTarget ∧
  SpectralMeasurePVMConcreteFunctionalCalculusDischargeReceiptTarget ∧
  SpectralMeasurePVMConcreteFinalPVMReceiptTarget ∧
  SpectralMeasurePVMOperatorValuedConcreteSpectralCompatibilityCoreReady ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The concrete functional-calculus core is ready. -/
theorem spectral_measure_pvm_operator_valued_concrete_functional_calculus_core_ready :
    SpectralMeasurePVMOperatorValuedConcreteFunctionalCalculusCoreReady := by
  exact ⟨
    spectral_measure_pvm_concrete_bounded_borel_function_interface_target_ready,
    spectral_measure_pvm_concrete_indicator_function_projection_target_ready,
    spectral_measure_pvm_concrete_simple_function_calculus_target_ready,
    spectral_measure_pvm_concrete_bounded_limit_calculus_target_ready,
    spectral_measure_pvm_concrete_functional_calculus_operator_integral_compatibility_target_ready,
    spectral_measure_pvm_concrete_functional_calculus_identity_function_recovery_target_ready,
    spectral_measure_pvm_concrete_spectral_projection_membership_recovered_target_ready,
    spectral_measure_pvm_concrete_functional_calculus_feeds_final_pvm_receipt_target_ready,
    spectral_measure_pvm_concrete_no_final_receipt_before_functional_calculus_target_ready,
    spectral_measure_pvm_concrete_functional_calculus_discharge_receipt_target_ready,
    spectral_measure_pvm_concrete_final_pvm_receipt_target_ready,
    spectral_measure_pvm_operator_valued_concrete_spectral_compatibility_core_ready,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
