/-
MGAP4D R1: Physical / OS reconstruction input layer.
This Prop-level file records the front-end assumptions that construct the
Hilbert-space, vacuum, Hamiltonian and excited-sector context used later by R2--R7.
-/

namespace MGAP4D
namespace R1

structure PhysicalInputLedger where
  model_id_declared : Prop
  four_dimensional_sector_declared : Prop
  gauge_or_connection_data_declared : Prop
  observable_algebra_declared : Prop
  vacuum_candidate_declared : Prop
  dynamics_generator_declared : Prop
  no_hidden_external_axiom : Prop

structure PhysicalInputLedgerResult where
  physical_input_ready : Prop

theorem physical_input_ledger_pack (L : PhysicalInputLedger) : PhysicalInputLedgerResult := by
  exact ⟨L.model_id_declared ∧ L.four_dimensional_sector_declared ∧
    L.gauge_or_connection_data_declared ∧ L.observable_algebra_declared ∧
    L.vacuum_candidate_declared ∧ L.dynamics_generator_declared ∧
    L.no_hidden_external_axiom⟩

structure HilbertSpaceConstruction where
  physical_input_ready : Prop
  pre_hilbert_space_defined : Prop
  inner_product_defined : Prop
  positivity_of_inner_product : Prop
  null_space_quotient_defined : Prop
  completion_defined : Prop
  Hilbert_space_ready : Prop

structure HilbertSpaceConstructionResult where
  hilbert_space_construction_ready : Prop

theorem hilbert_space_construction_pack (H : HilbertSpaceConstruction) :
    HilbertSpaceConstructionResult := by
  exact ⟨H.physical_input_ready ∧ H.pre_hilbert_space_defined ∧ H.inner_product_defined ∧
    H.positivity_of_inner_product ∧ H.null_space_quotient_defined ∧ H.completion_defined ∧
    H.Hilbert_space_ready⟩

structure VacuumSectorConstruction where
  hilbert_space_construction_ready : Prop
  vacuum_vector_defined : Prop
  vacuum_vector_nonzero : Prop
  vacuum_vector_normalized : Prop
  vacuum_projection_defined : Prop
  vacuum_projection_orthogonal : Prop
  vacuum_sector_closed : Prop

structure VacuumSectorConstructionResult where
  vacuum_sector_ready : Prop

theorem vacuum_sector_construction_pack (V : VacuumSectorConstruction) :
    VacuumSectorConstructionResult := by
  exact ⟨V.hilbert_space_construction_ready ∧ V.vacuum_vector_defined ∧
    V.vacuum_vector_nonzero ∧ V.vacuum_vector_normalized ∧ V.vacuum_projection_defined ∧
    V.vacuum_projection_orthogonal ∧ V.vacuum_sector_closed⟩

structure HamiltonianSeedConstruction where
  hilbert_space_construction_ready : Prop
  dynamics_generator_declared : Prop
  quadratic_form_seed_defined : Prop
  quadratic_form_symmetric : Prop
  quadratic_form_semibounded : Prop
  form_closability_available : Prop
  Hamiltonian_seed_ready : Prop

structure HamiltonianSeedConstructionResult where
  hamiltonian_seed_ready : Prop

theorem hamiltonian_seed_construction_pack (H : HamiltonianSeedConstruction) :
    HamiltonianSeedConstructionResult := by
  exact ⟨H.hilbert_space_construction_ready ∧ H.dynamics_generator_declared ∧
    H.quadratic_form_seed_defined ∧ H.quadratic_form_symmetric ∧
    H.quadratic_form_semibounded ∧ H.form_closability_available ∧ H.Hamiltonian_seed_ready⟩

structure ExcitedSectorScaffold where
  vacuum_sector_ready : Prop
  hamiltonian_seed_ready : Prop
  excited_sector_defined_as_orthogonal_complement : Prop
  excited_sector_closed : Prop
  excited_projection_defined : Prop
  vacuum_and_excited_projections_sum_to_identity : Prop
  no_overlap_between_vacuum_and_excited : Prop

structure ExcitedSectorScaffoldResult where
  excited_sector_scaffold_ready : Prop

theorem excited_sector_scaffold_pack (E : ExcitedSectorScaffold) :
    ExcitedSectorScaffoldResult := by
  exact ⟨E.vacuum_sector_ready ∧ E.hamiltonian_seed_ready ∧
    E.excited_sector_defined_as_orthogonal_complement ∧ E.excited_sector_closed ∧
    E.excited_projection_defined ∧ E.vacuum_and_excited_projections_sum_to_identity ∧
    E.no_overlap_between_vacuum_and_excited⟩

structure R1FinalClosure where
  R1_closed_as_scaffold : Prop
  physical_input_ready : Prop
  hilbert_space_construction_ready : Prop
  vacuum_sector_ready : Prop
  hamiltonian_seed_ready : Prop
  excited_sector_scaffold_ready : Prop
  export_to_R2_ready : Prop
  public_claim_still_gated : Prop

def R1FinalClosure.ready (C : R1FinalClosure) : Prop :=
  C.R1_closed_as_scaffold ∧ C.physical_input_ready ∧ C.hilbert_space_construction_ready ∧
  C.vacuum_sector_ready ∧ C.hamiltonian_seed_ready ∧ C.excited_sector_scaffold_ready ∧
  C.export_to_R2_ready ∧ C.public_claim_still_gated

theorem r1_final_closure_pack
    (physical_input_ready hilbert_space_construction_ready vacuum_sector_ready
     hamiltonian_seed_ready excited_sector_scaffold_ready export_to_R2_ready
     public_claim_still_gated : Prop) : R1FinalClosure := by
  exact {
    R1_closed_as_scaffold := physical_input_ready ∧ hilbert_space_construction_ready ∧
      vacuum_sector_ready ∧ hamiltonian_seed_ready ∧ excited_sector_scaffold_ready
    physical_input_ready := physical_input_ready
    hilbert_space_construction_ready := hilbert_space_construction_ready
    vacuum_sector_ready := vacuum_sector_ready
    hamiltonian_seed_ready := hamiltonian_seed_ready
    excited_sector_scaffold_ready := excited_sector_scaffold_ready
    export_to_R2_ready := export_to_R2_ready
    public_claim_still_gated := public_claim_still_gated
  }

end R1
end MGAP4D
