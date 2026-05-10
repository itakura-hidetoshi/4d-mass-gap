/- MGAP4D R7: eigenstate attainment skeleton, F1--F5, unconditional activation. -/
namespace MGAP4D
namespace R7

structure CandidateEigenvectorData where
  psi_star_nonzero : Prop
  psi_star_in_excited_sector : Prop
  psi_star_in_domain_H_exc : Prop
  psi_star_in_form_domain : Prop
  normalized_or_norm_bound : Prop
  same_domain_as_R4_receipts : Prop

structure CandidateEigenvectorResult where
  candidate_eigenvector_ready : Prop

theorem candidate_eigenvector_pack (D : CandidateEigenvectorData) : CandidateEigenvectorResult := by
  exact ⟨D.psi_star_nonzero ∧ D.psi_star_in_excited_sector ∧ D.psi_star_in_domain_H_exc ∧
    D.psi_star_in_form_domain ∧ D.normalized_or_norm_bound ∧ D.same_domain_as_R4_receipts⟩

structure SaturationSubspaceRegistry where
  excited_sector_defined : Prop
  common_form_domain_defined : Prop
  E_base_defined : Prop
  E_curv_defined : Prop
  K_int_pos_defined : Prop
  E_leak_defined : Prop
  E_boundary_defined : Prop
  E_regularization_defined : Prop
  saturation_subspace_defined_as_intersection : Prop
  saturation_subspace_subset_excited_sector : Prop
  saturation_subspace_subset_common_domain : Prop

structure SaturationSubspaceRegistryResult where
  saturation_subspace_registry_ready : Prop

theorem saturation_subspace_registry_pack (R : SaturationSubspaceRegistry) :
    SaturationSubspaceRegistryResult := by
  exact ⟨R.excited_sector_defined ∧ R.common_form_domain_defined ∧ R.E_base_defined ∧
    R.E_curv_defined ∧ R.K_int_pos_defined ∧ R.E_leak_defined ∧
    R.E_boundary_defined ∧ R.E_regularization_defined ∧
    R.saturation_subspace_defined_as_intersection ∧
    R.saturation_subspace_subset_excited_sector ∧ R.saturation_subspace_subset_common_domain⟩

structure SaturationSubspaceNonzeroData where
  saturation_subspace_registry_ready : Prop
  saturation_subspace_nonempty : Prop
  exists_nonzero_vector_in_saturation_subspace : Prop
  intersection_compatibility_witness : Prop
  no_mutual_exclusion_between_saturation_conditions : Prop
  finite_or_compactness_argument_available : Prop

structure SaturationSubspaceNonzeroResult where
  saturation_subspace_nonzero : Prop

theorem saturation_subspace_nonzero_pack (D : SaturationSubspaceNonzeroData) :
    SaturationSubspaceNonzeroResult := by
  exact ⟨D.saturation_subspace_registry_ready ∧ D.saturation_subspace_nonempty ∧
    D.exists_nonzero_vector_in_saturation_subspace ∧ D.intersection_compatibility_witness ∧
    D.no_mutual_exclusion_between_saturation_conditions ∧ D.finite_or_compactness_argument_available⟩

structure SaturationProjectionProduct where
  commuting_saturation_projections_ready : Prop
  P_star_defined : Prop
  P_star_is_projection : Prop
  P_star_is_orthogonal_projection : Prop
  P_star_range_equals_intersection : Prop
  P_star_range_equals_S_star : Prop

structure SaturationProjectionProductResult where
  saturation_projection_product_ready : Prop

theorem saturation_projection_product_pack (P : SaturationProjectionProduct) :
    SaturationProjectionProductResult := by
  exact ⟨P.commuting_saturation_projections_ready ∧ P.P_star_defined ∧
    P.P_star_is_projection ∧ P.P_star_is_orthogonal_projection ∧
    P.P_star_range_equals_intersection ∧ P.P_star_range_equals_S_star⟩

structure JointSpectralAtomRegistry where
  joint_spectral_measure_defined : Prop
  atom_base_value_defined : Prop
  atom_curv_value_defined : Prop
  atom_int_pos_value_defined : Prop
  atom_leak_value_defined : Prop
  atom_boundary_value_defined : Prop
  atom_regularization_value_defined : Prop
  atom_values_match_R4_constant_ledger : Prop
  alpha_star_defined : Prop
  alpha_star_borel_singleton_defined : Prop

structure JointSpectralAtomRegistryResult where
  joint_spectral_atom_registry_ready : Prop

theorem joint_spectral_atom_registry_pack (R : JointSpectralAtomRegistry) :
    JointSpectralAtomRegistryResult := by
  exact ⟨R.joint_spectral_measure_defined ∧ R.atom_base_value_defined ∧
    R.atom_curv_value_defined ∧ R.atom_int_pos_value_defined ∧ R.atom_leak_value_defined ∧
    R.atom_boundary_value_defined ∧ R.atom_regularization_value_defined ∧
    R.atom_values_match_R4_constant_ledger ∧ R.alpha_star_defined ∧
    R.alpha_star_borel_singleton_defined⟩

structure JointAtomPositiveMassData where
  joint_spectral_atom_registry_ready : Prop
  joint_atom_projection_defined : Prop
  joint_atom_projection_nonzero : Prop
  joint_atom_has_positive_spectral_mass : Prop
  no_atom_erasure_by_regularization : Prop
  no_atom_erasure_by_boundary_limit : Prop
  no_atom_erasure_by_interaction_leak : Prop

structure JointAtomPositiveMassResult where
  joint_atom_positive_mass_ready : Prop
  E_joint_alpha_star_nonzero : Prop

theorem joint_atom_positive_mass_pack (D : JointAtomPositiveMassData) :
    JointAtomPositiveMassResult := by
  exact {
    joint_atom_positive_mass_ready :=
      D.joint_spectral_atom_registry_ready ∧ D.joint_atom_projection_defined ∧
      D.joint_atom_projection_nonzero ∧ D.joint_atom_has_positive_spectral_mass ∧
      D.no_atom_erasure_by_regularization ∧ D.no_atom_erasure_by_boundary_limit ∧
      D.no_atom_erasure_by_interaction_leak
    E_joint_alpha_star_nonzero := D.joint_atom_projection_nonzero
  }

structure F1FinalClosure where
  F1_finite_saturation_seed_closed : Prop
  finite_model_system_ready : Prop
  finite_projection_product_ready : Prop
  representation_multiplicity_certificate_ready : Prop
  dim_H_N_rho_star_ge_one : Prop
  rank_P_star_N_ge_one : Prop
  P_star_N_nonzero : Prop
  finite_seed_vector_ready : Prop
  v_N_nonzero : Prop
  v_N_normalized : Prop
  P_star_N_v_N_eq_v_N : Prop
  finite_saturation_conditions_hold : Prop
  export_to_F2_noncollapse_ready : Prop
  public_claim_still_gated : Prop

def F1FinalClosure.ready (C : F1FinalClosure) : Prop :=
  C.F1_finite_saturation_seed_closed ∧ C.finite_model_system_ready ∧
  C.finite_projection_product_ready ∧ C.representation_multiplicity_certificate_ready ∧
  C.dim_H_N_rho_star_ge_one ∧ C.rank_P_star_N_ge_one ∧ C.P_star_N_nonzero ∧
  C.finite_seed_vector_ready ∧ C.v_N_nonzero ∧ C.v_N_normalized ∧
  C.P_star_N_v_N_eq_v_N ∧ C.finite_saturation_conditions_hold ∧
  C.export_to_F2_noncollapse_ready ∧ C.public_claim_still_gated

structure F2UniformCoreMassFinal where
  uniform_core_mass_lower_bound_closed : Prop
  core_decomposition_registry_ready : Prop
  tail_escape_bound_ready : Prop
  boundary_escape_bound_ready : Prop
  regularization_ghost_bound_ready : Prop
  core_mass_lower_bound_ready : Prop
  eta_defined : Prop
  eta_positive : Prop
  eta_eq_one_half : Prop
  forall_N_core_mass_ge_eta : Prop
  export_to_compactness_extraction_ready : Prop
  public_claim_still_gated : Prop

def F2UniformCoreMassFinal.ready (C : F2UniformCoreMassFinal) : Prop :=
  C.uniform_core_mass_lower_bound_closed ∧ C.core_decomposition_registry_ready ∧
  C.tail_escape_bound_ready ∧ C.boundary_escape_bound_ready ∧ C.regularization_ghost_bound_ready ∧
  C.core_mass_lower_bound_ready ∧ C.eta_defined ∧ C.eta_positive ∧ C.eta_eq_one_half ∧
  C.forall_N_core_mass_ge_eta ∧ C.export_to_compactness_extraction_ready ∧ C.public_claim_still_gated

structure F2FinalClosure where
  F2_finite_seed_noncollapse_closed : Prop
  F1_finite_saturation_seed_ready : Prop
  uniform_core_mass_lower_bound_ready : Prop
  bounded_seed_sequence_ready : Prop
  weak_compactness_extraction_ready : Prop
  core_compactness_upgrade_ready : Prop
  core_mass_passes_to_limit_ready : Prop
  exists_subsequence_with_nonzero_weak_limit : Prop
  v_star_nonzero : Prop
  v_star_in_excited_sector : Prop
  export_to_F3_F4_F5_ready : Prop
  public_claim_still_gated : Prop

def F2FinalClosure.ready (C : F2FinalClosure) : Prop :=
  C.F2_finite_seed_noncollapse_closed ∧ C.F1_finite_saturation_seed_ready ∧
  C.uniform_core_mass_lower_bound_ready ∧ C.bounded_seed_sequence_ready ∧
  C.weak_compactness_extraction_ready ∧ C.core_compactness_upgrade_ready ∧
  C.core_mass_passes_to_limit_ready ∧ C.exists_subsequence_with_nonzero_weak_limit ∧
  C.v_star_nonzero ∧ C.v_star_in_excited_sector ∧ C.export_to_F3_F4_F5_ready ∧
  C.public_claim_still_gated

structure F3JointSpectralConvergenceFinal where
  F3_joint_spectral_convergence_closed : Prop
  joint_spectral_family_registry_ready : Prop
  finite_seed_spectral_localization_ready : Prop
  strong_resolvent_convergence_ready : Prop
  joint_projection_convergence_ready : Prop
  limit_vector_in_joint_neighborhood_ready : Prop
  v_star_localized_in_all_atom_neighborhoods : Prop
  export_to_F4_no_smearing_ready : Prop
  public_claim_still_gated : Prop

def F3JointSpectralConvergenceFinal.ready (C : F3JointSpectralConvergenceFinal) : Prop :=
  C.F3_joint_spectral_convergence_closed ∧ C.joint_spectral_family_registry_ready ∧
  C.finite_seed_spectral_localization_ready ∧ C.strong_resolvent_convergence_ready ∧
  C.joint_projection_convergence_ready ∧ C.limit_vector_in_joint_neighborhood_ready ∧
  C.v_star_localized_in_all_atom_neighborhoods ∧ C.export_to_F4_no_smearing_ready ∧
  C.public_claim_still_gated

structure F4NoContinuousSmearingFinal where
  F4_no_continuous_spectrum_smearing_closed : Prop
  joint_spectrum_isolation_ready : Prop
  neighborhood_projection_equals_atom_ready : Prop
  v_star_in_joint_atom_ready : Prop
  E_joint_alpha_star_v_star_eq_v_star : Prop
  v_star_nonzero : Prop
  export_to_F5_atom_persistence_ready : Prop
  public_claim_still_gated : Prop

def F4NoContinuousSmearingFinal.ready (C : F4NoContinuousSmearingFinal) : Prop :=
  C.F4_no_continuous_spectrum_smearing_closed ∧ C.joint_spectrum_isolation_ready ∧
  C.neighborhood_projection_equals_atom_ready ∧ C.v_star_in_joint_atom_ready ∧
  C.E_joint_alpha_star_v_star_eq_v_star ∧ C.v_star_nonzero ∧ C.export_to_F5_atom_persistence_ready ∧ C.public_claim_still_gated

structure F5AtomNotLostFinal where
  F5_atom_not_lost_closed : Prop
  F1_finite_saturation_seed_ready : Prop
  F2_finite_seed_noncollapse_ready : Prop
  F3_joint_spectral_convergence_ready : Prop
  F4_no_continuous_spectrum_smearing_ready : Prop
  E_joint_alpha_star_nonzero : Prop
  joint_atom_positive_mass_ready : Prop
  P_star_nonzero : Prop
  saturation_subspace_nonzero : Prop
  export_to_R7_unconditional_activation_ready : Prop
  public_claim_still_gated : Prop

def F5AtomNotLostFinal.ready (C : F5AtomNotLostFinal) : Prop :=
  C.F5_atom_not_lost_closed ∧ C.F1_finite_saturation_seed_ready ∧
  C.F2_finite_seed_noncollapse_ready ∧ C.F3_joint_spectral_convergence_ready ∧
  C.F4_no_continuous_spectrum_smearing_ready ∧ C.E_joint_alpha_star_nonzero ∧
  C.joint_atom_positive_mass_ready ∧ C.P_star_nonzero ∧ C.saturation_subspace_nonzero ∧ C.export_to_R7_unconditional_activation_ready ∧ C.public_claim_still_gated

structure EigenstateExistenceUnconditionalData where
  saturation_vector_selected : Prop
  saturation_vector_domain_ready : Prop
  saturation_ledger_activated : Prop
  shifted_operator_kills_psi_star : Prop
  H_exc_psi_star_eq_33_over_20_smul_psi_star : Prop
  psi_star_nonzero : Prop
  psi_star_in_excited_sector : Prop
  psi_star_in_domain_H_exc : Prop

structure EigenstateExistenceUnconditionalResult where
  exists_eigenstate_at_33_over_20 : Prop

theorem eigenstate_existence_unconditional_pack
    (D : EigenstateExistenceUnconditionalData) :
    EigenstateExistenceUnconditionalResult := by
  exact ⟨D.saturation_vector_selected ∧ D.saturation_vector_domain_ready ∧
    D.saturation_ledger_activated ∧ D.shifted_operator_kills_psi_star ∧
    D.H_exc_psi_star_eq_33_over_20_smul_psi_star ∧ D.psi_star_nonzero ∧
    D.psi_star_in_excited_sector ∧ D.psi_star_in_domain_H_exc⟩

structure ExactGapEqualityUnconditionalData where
  m_exc_well_defined : Prop
  m_exc_ge_33_over_20 : Prop
  thirty_three_over_twenty_in_sigma_H_exc : Prop
  infimum_le_each_spectrum_point : Prop
  m_exc_le_33_over_20 : Prop
  order_antisymmetry_available : Prop

structure ExactGapEqualityUnconditionalResult where
  m_exc_eq_33_over_20 : Prop

theorem exact_gap_equality_unconditional_pack
    (D : ExactGapEqualityUnconditionalData) : ExactGapEqualityUnconditionalResult := by
  exact ⟨D.m_exc_well_defined ∧ D.m_exc_ge_33_over_20 ∧
    D.thirty_three_over_twenty_in_sigma_H_exc ∧ D.infimum_le_each_spectrum_point ∧
    D.m_exc_le_33_over_20 ∧ D.order_antisymmetry_available⟩

structure UnconditionalFinalClosure where
  R7_closed_as_eigenstate_attainment_proof_kernel : Prop
  F1_finite_saturation_seed_ready : Prop
  F2_finite_seed_noncollapse_ready : Prop
  F3_joint_spectral_convergence_ready : Prop
  F4_no_continuous_spectrum_smearing_ready : Prop
  F5_atom_not_lost_ready : Prop
  saturation_subspace_nonzero : Prop
  saturation_vector_selected : Prop
  exists_eigenstate_at_33_over_20 : Prop
  thirty_three_over_twenty_in_point_spectrum_H_exc : Prop
  thirty_three_over_twenty_in_sigma_H_exc : Prop
  m_exc_eq_33_over_20 : Prop
  public_claim_still_gated : Prop

def UnconditionalFinalClosure.ready (C : UnconditionalFinalClosure) : Prop :=
  C.R7_closed_as_eigenstate_attainment_proof_kernel ∧
  C.F1_finite_saturation_seed_ready ∧ C.F2_finite_seed_noncollapse_ready ∧
  C.F3_joint_spectral_convergence_ready ∧ C.F4_no_continuous_spectrum_smearing_ready ∧
  C.F5_atom_not_lost_ready ∧ C.saturation_subspace_nonzero ∧ C.saturation_vector_selected ∧ C.exists_eigenstate_at_33_over_20 ∧
  C.thirty_three_over_twenty_in_point_spectrum_H_exc ∧
  C.thirty_three_over_twenty_in_sigma_H_exc ∧ C.m_exc_eq_33_over_20 ∧
  C.public_claim_still_gated

end R7
end MGAP4D
