/- MGAP4D R5: Spectrum set construction skeleton. -/
namespace MGAP4D
namespace R5

structure HilbertVacuumExcitedDirectSumData where
  vacuum_vector_normalized : Prop
  vacuum_line_defined : Prop
  excited_sector_defined_as_orthogonal_complement : Prop
  vacuum_projection_defined : Prop
  excited_projection_defined : Prop
  projection_sum_identity : Prop
  projection_orthogonality : Prop
  direct_sum_decomposition : Prop

structure HilbertVacuumExcitedDirectSumResult where
  vacuum_excited_direct_sum_ready : Prop

theorem hilbert_vacuum_excited_direct_sum_pack
    (D : HilbertVacuumExcitedDirectSumData) :
    HilbertVacuumExcitedDirectSumResult := by
  exact ⟨D.vacuum_vector_normalized ∧ D.vacuum_line_defined ∧
    D.excited_sector_defined_as_orthogonal_complement ∧ D.vacuum_projection_defined ∧
    D.excited_projection_defined ∧ D.projection_sum_identity ∧
    D.projection_orthogonality ∧ D.direct_sum_decomposition⟩

structure OperatorBlockDecompositionData where
  H_self_adjoint : Prop
  vacuum_excited_direct_sum_ready : Prop
  vacuum_projection_commutes_with_H : Prop
  excited_projection_commutes_with_H : Prop
  vacuum_restricted_operator_defined : Prop
  excited_restricted_operator_defined : Prop
  block_decomposition_theorem_available : Prop

structure OperatorBlockDecompositionResult where
  H_block_decomposition_ready : Prop

theorem operator_block_decomposition_pack
    (D : OperatorBlockDecompositionData) : OperatorBlockDecompositionResult := by
  exact ⟨D.H_self_adjoint ∧ D.vacuum_excited_direct_sum_ready ∧
    D.vacuum_projection_commutes_with_H ∧ D.excited_projection_commutes_with_H ∧
    D.vacuum_restricted_operator_defined ∧ D.excited_restricted_operator_defined ∧
    D.block_decomposition_theorem_available⟩

structure ExcitedSpectrumData where
  H_exc_self_adjoint : Prop
  H_exc_nonnegative : Prop
  spectrum_defined : Prop
  spectrum_nonempty : Prop
  spectrum_closed : Prop
  spectrum_subset_nonnegative_real : Prop

structure ExcitedSpectrumResult where
  excited_spectrum_ready : Prop

theorem excited_spectrum_pack (D : ExcitedSpectrumData) : ExcitedSpectrumResult := by
  exact ⟨D.H_exc_self_adjoint ∧ D.H_exc_nonnegative ∧ D.spectrum_defined ∧
    D.spectrum_nonempty ∧ D.spectrum_closed ∧ D.spectrum_subset_nonnegative_real⟩

structure InfimumData where
  H_exc_spectrum_defined : Prop
  H_exc_spectrum_nonempty : Prop
  H_exc_spectrum_bounded_below : Prop
  m_exc_defined : Prop
  m_exc_is_lower_bound_of_spectrum : Prop
  m_exc_is_greatest_lower_bound : Prop
  m_exc_in_H_exc_spectrum : Prop

structure InfimumResult where
  infimum_ready : Prop

theorem infimum_pack (D : InfimumData) : InfimumResult := by
  exact ⟨D.H_exc_spectrum_defined ∧ D.H_exc_spectrum_nonempty ∧
    D.H_exc_spectrum_bounded_below ∧ D.m_exc_defined ∧
    D.m_exc_is_lower_bound_of_spectrum ∧ D.m_exc_is_greatest_lower_bound ∧
    D.m_exc_in_H_exc_spectrum⟩

structure LowerBoundBridgeData where
  H_exc_self_adjoint : Prop
  c_defined : Prop
  operator_lower_bound_H_exc_ge_cI : Prop
  spectral_order_theorem_available : Prop
  sigma_H_exc_subset_c_infty : Prop
  m_exc_ge_c : Prop

structure LowerBoundBridgeResult where
  lower_bound_bridge_ready : Prop

theorem lower_bound_bridge_pack (D : LowerBoundBridgeData) : LowerBoundBridgeResult := by
  exact ⟨D.H_exc_self_adjoint ∧ D.c_defined ∧ D.operator_lower_bound_H_exc_ge_cI ∧
    D.spectral_order_theorem_available ∧ D.sigma_H_exc_subset_c_infty ∧ D.m_exc_ge_c⟩

structure VacuumRestrictedSpectrumData where
  vacuum_restricted_operator_defined : Prop
  vacuum_eigenvalue_zero : Prop
  vacuum_line_one_dimensional : Prop
  vacuum_operator_zero : Prop
  spectrum_of_zero_operator_theorem_available : Prop

structure VacuumRestrictedSpectrumResult where
  vacuum_spectrum_is_zero_singleton : Prop

theorem vacuum_restricted_spectrum_pack (D : VacuumRestrictedSpectrumData) :
    VacuumRestrictedSpectrumResult := by
  exact ⟨D.vacuum_restricted_operator_defined ∧ D.vacuum_eigenvalue_zero ∧
    D.vacuum_line_one_dimensional ∧ D.vacuum_operator_zero ∧
    D.spectrum_of_zero_operator_theorem_available⟩

structure DirectSumSpectrumData where
  H_block_decomposition_ready : Prop
  vacuum_spectrum_defined : Prop
  excited_spectrum_defined : Prop
  total_spectrum_defined : Prop
  direct_sum_spectrum_theorem_available : Prop

structure DirectSumSpectrumResult where
  total_spectrum_decomposes_as_union : Prop

theorem direct_sum_spectrum_pack (D : DirectSumSpectrumData) : DirectSumSpectrumResult := by
  exact ⟨D.H_block_decomposition_ready ∧ D.vacuum_spectrum_defined ∧
    D.excited_spectrum_defined ∧ D.total_spectrum_defined ∧
    D.direct_sum_spectrum_theorem_available⟩

structure TotalSpectrumDecompositionData where
  total_spectrum_decomposes_as_union : Prop
  vacuum_spectrum_is_zero_singleton : Prop
  H_exc_spectrum_defined : Prop
  set_union_substitution_available : Prop

structure TotalSpectrumDecompositionResult where
  total_spectrum_equals_vacuum_zero_union_excited : Prop

theorem total_spectrum_decomposition_pack (D : TotalSpectrumDecompositionData) :
    TotalSpectrumDecompositionResult := by
  exact ⟨D.total_spectrum_decomposes_as_union ∧ D.vacuum_spectrum_is_zero_singleton ∧
    D.H_exc_spectrum_defined ∧ D.set_union_substitution_available⟩

structure ComponentLedger where
  R5_alpha_track_started : Prop
  R5_beta_excited_reducing_ready : Prop
  H_exc_self_adjoint : Prop
  H_exc_nonnegative : Prop
  R5_gamma_excited_spectrum_ready : Prop
  H_exc_spectrum_defined : Prop
  H_exc_spectrum_nonempty : Prop
  H_exc_spectrum_closed : Prop
  H_exc_spectrum_subset_nonnegative_real : Prop
  R5_delta_infimum_ready : Prop
  m_exc_well_defined : Prop
  m_exc_is_lower_bound_of_spectrum : Prop
  m_exc_is_greatest_lower_bound : Prop
  m_exc_in_H_exc_spectrum : Prop
  R5_epsilon_lower_bound_bridge_ready : Prop
  lower_bound_implies_spectrum_subset : Prop
  lower_bound_implies_m_exc_ge_c : Prop
  R5_zeta_total_spectrum_decomposition_ready : Prop
  total_spectrum_equals_vacuum_zero_union_excited : Prop

structure SpectrumSetConstructionFinalResult where
  R5_closed_as_proof_kernel : Prop
  excited_operator_constructed : Prop
  excited_spectrum_constructed : Prop
  excited_spectral_bottom_constructed : Prop
  lower_bound_bridge_constructed : Prop
  total_spectrum_decomposition_constructed : Prop
  numerical_gap_not_claimed_here : Prop
  public_claim_still_gated : Prop

theorem spectrum_set_construction_final_pack
    (L : ComponentLedger)
    (numerical_gap_not_claimed_here public_claim_still_gated : Prop) :
    SpectrumSetConstructionFinalResult := by
  exact {
    R5_closed_as_proof_kernel :=
      L.R5_alpha_track_started ∧ L.R5_beta_excited_reducing_ready ∧
      L.R5_gamma_excited_spectrum_ready ∧ L.R5_delta_infimum_ready ∧
      L.R5_epsilon_lower_bound_bridge_ready ∧ L.R5_zeta_total_spectrum_decomposition_ready
    excited_operator_constructed := L.H_exc_self_adjoint ∧ L.H_exc_nonnegative
    excited_spectrum_constructed := L.H_exc_spectrum_defined ∧ L.H_exc_spectrum_nonempty ∧
      L.H_exc_spectrum_closed ∧ L.H_exc_spectrum_subset_nonnegative_real
    excited_spectral_bottom_constructed := L.m_exc_well_defined ∧
      L.m_exc_is_lower_bound_of_spectrum ∧ L.m_exc_is_greatest_lower_bound ∧
      L.m_exc_in_H_exc_spectrum
    lower_bound_bridge_constructed := L.lower_bound_implies_spectrum_subset ∧
      L.lower_bound_implies_m_exc_ge_c
    total_spectrum_decomposition_constructed := L.total_spectrum_equals_vacuum_zero_union_excited
    numerical_gap_not_claimed_here := numerical_gap_not_claimed_here
    public_claim_still_gated := public_claim_still_gated
  }

end R5
end MGAP4D
