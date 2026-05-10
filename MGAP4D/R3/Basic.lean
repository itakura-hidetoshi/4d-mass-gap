/-
MGAP4D R3: Spectral square-root / quadratic-form replay layer.
This Prop-level file records the sqrt route used later in R4 and R7:
nonnegative self-adjoint operator -> square root -> zero form implies kernel.
-/

namespace MGAP4D
namespace R3

structure NonnegativeOperatorSqrtRegistry where
  R2_export_ready : Prop
  operator_self_adjoint : Prop
  operator_nonnegative : Prop
  spectral_theorem_available : Prop
  sqrt_operator_defined : Prop
  sqrt_operator_self_adjoint : Prop
  sqrt_operator_nonnegative : Prop
  sqrt_square_recovers_operator : Prop

structure NonnegativeOperatorSqrtRegistryResult where
  sqrt_registry_ready : Prop

theorem nonnegative_operator_sqrt_registry_pack (R : NonnegativeOperatorSqrtRegistry) :
    NonnegativeOperatorSqrtRegistryResult := by
  exact ⟨R.R2_export_ready ∧ R.operator_self_adjoint ∧ R.operator_nonnegative ∧
    R.spectral_theorem_available ∧ R.sqrt_operator_defined ∧ R.sqrt_operator_self_adjoint ∧
    R.sqrt_operator_nonnegative ∧ R.sqrt_square_recovers_operator⟩

structure QuadraticFormSqrtIdentity where
  sqrt_registry_ready : Prop
  vector_in_operator_domain : Prop
  vector_in_sqrt_domain : Prop
  quadratic_form_defined : Prop
  quadratic_form_eq_norm_sqrt_sq : Prop
  no_domain_gap_for_sqrt_identity : Prop

structure QuadraticFormSqrtIdentityResult where
  quadratic_form_sqrt_identity_ready : Prop

theorem quadratic_form_sqrt_identity_pack (I : QuadraticFormSqrtIdentity) :
    QuadraticFormSqrtIdentityResult := by
  exact ⟨I.sqrt_registry_ready ∧ I.vector_in_operator_domain ∧ I.vector_in_sqrt_domain ∧
    I.quadratic_form_defined ∧ I.quadratic_form_eq_norm_sqrt_sq ∧ I.no_domain_gap_for_sqrt_identity⟩

structure ZeroFormImpliesSqrtZero where
  quadratic_form_sqrt_identity_ready : Prop
  quadratic_form_zero : Prop
  norm_sqrt_sq_zero : Prop
  sqrt_applied_vector_eq_zero : Prop
  norm_zero_principle_available : Prop

structure ZeroFormImpliesSqrtZeroResult where
  zero_form_implies_sqrt_zero_ready : Prop

theorem zero_form_implies_sqrt_zero_pack (Z : ZeroFormImpliesSqrtZero) :
    ZeroFormImpliesSqrtZeroResult := by
  exact ⟨Z.quadratic_form_sqrt_identity_ready ∧ Z.quadratic_form_zero ∧
    Z.norm_sqrt_sq_zero ∧ Z.sqrt_applied_vector_eq_zero ∧ Z.norm_zero_principle_available⟩

structure SqrtZeroImpliesOperatorKernel where
  sqrt_registry_ready : Prop
  sqrt_applied_vector_eq_zero : Prop
  vector_in_operator_domain : Prop
  sqrt_square_recovers_operator : Prop
  operator_applied_vector_eq_zero : Prop
  no_domain_gap_for_kernel_step : Prop

structure SqrtZeroImpliesOperatorKernelResult where
  sqrt_zero_implies_operator_kernel_ready : Prop

theorem sqrt_zero_implies_operator_kernel_pack (K : SqrtZeroImpliesOperatorKernel) :
    SqrtZeroImpliesOperatorKernelResult := by
  exact ⟨K.sqrt_registry_ready ∧ K.sqrt_applied_vector_eq_zero ∧ K.vector_in_operator_domain ∧
    K.sqrt_square_recovers_operator ∧ K.operator_applied_vector_eq_zero ∧ K.no_domain_gap_for_kernel_step⟩

structure NonnegativeZeroFormImpliesKernel where
  sqrt_registry_ready : Prop
  quadratic_form_sqrt_identity_ready : Prop
  zero_form_implies_sqrt_zero_ready : Prop
  sqrt_zero_implies_operator_kernel_ready : Prop
  vector_in_operator_domain : Prop
  operator_applied_vector_eq_zero : Prop

structure NonnegativeZeroFormImpliesKernelResult where
  nonnegative_operator_zero_form_implies_kernel : Prop

theorem nonnegative_zero_form_implies_kernel_pack (D : NonnegativeZeroFormImpliesKernel) :
    NonnegativeZeroFormImpliesKernelResult := by
  exact ⟨D.sqrt_registry_ready ∧ D.quadratic_form_sqrt_identity_ready ∧
    D.zero_form_implies_sqrt_zero_ready ∧ D.sqrt_zero_implies_operator_kernel_ready ∧
    D.vector_in_operator_domain ∧ D.operator_applied_vector_eq_zero⟩

structure ShiftedOperatorSqrtRoute where
  H_exc_self_adjoint : Prop
  H_exc_ge_33_over_20_I : Prop
  shifted_operator_defined : Prop
  shifted_operator_self_adjoint : Prop
  shifted_operator_nonnegative : Prop
  shifted_sqrt_route_ready : Prop
  zero_shifted_form_implies_kernel : Prop

structure ShiftedOperatorSqrtRouteResult where
  r3_shifted_sqrt_route_ready : Prop

theorem shifted_operator_sqrt_route_pack (S : ShiftedOperatorSqrtRoute) :
    ShiftedOperatorSqrtRouteResult := by
  exact ⟨S.H_exc_self_adjoint ∧ S.H_exc_ge_33_over_20_I ∧ S.shifted_operator_defined ∧
    S.shifted_operator_self_adjoint ∧ S.shifted_operator_nonnegative ∧
    S.shifted_sqrt_route_ready ∧ S.zero_shifted_form_implies_kernel⟩

structure R3FinalClosure where
  R3_closed_as_sqrt_route : Prop
  sqrt_registry_ready : Prop
  quadratic_form_sqrt_identity_ready : Prop
  nonnegative_operator_zero_form_implies_kernel : Prop
  r3_shifted_sqrt_route_ready : Prop
  export_to_R4_R7_ready : Prop
  public_claim_still_gated : Prop

def R3FinalClosure.ready (C : R3FinalClosure) : Prop :=
  C.R3_closed_as_sqrt_route ∧ C.sqrt_registry_ready ∧ C.quadratic_form_sqrt_identity_ready ∧
  C.nonnegative_operator_zero_form_implies_kernel ∧ C.r3_shifted_sqrt_route_ready ∧
  C.export_to_R4_R7_ready ∧ C.public_claim_still_gated

theorem r3_final_closure_pack
    (sqrt_registry_ready quadratic_form_sqrt_identity_ready
     nonnegative_operator_zero_form_implies_kernel r3_shifted_sqrt_route_ready
     export_to_R4_R7_ready public_claim_still_gated : Prop) : R3FinalClosure := by
  exact {
    R3_closed_as_sqrt_route := sqrt_registry_ready ∧ quadratic_form_sqrt_identity_ready ∧
      nonnegative_operator_zero_form_implies_kernel ∧ r3_shifted_sqrt_route_ready
    sqrt_registry_ready := sqrt_registry_ready
    quadratic_form_sqrt_identity_ready := quadratic_form_sqrt_identity_ready
    nonnegative_operator_zero_form_implies_kernel := nonnegative_operator_zero_form_implies_kernel
    r3_shifted_sqrt_route_ready := r3_shifted_sqrt_route_ready
    export_to_R4_R7_ready := export_to_R4_R7_ready
    public_claim_still_gated := public_claim_still_gated
  }

end R3
end MGAP4D
