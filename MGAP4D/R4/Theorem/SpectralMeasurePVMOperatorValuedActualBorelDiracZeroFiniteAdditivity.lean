import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroProjectionKernel

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Pointwise binary finite additivity on disjoint actual-Borel carrier sets. -/
def SpectralMeasurePVMActualBorelProjectionKernelDisjointUnionPointwiseAdditive
    (K : SpectralMeasurePVMActualBorelProjectionKernel) : Prop :=
  ∀ s t : SpectralMeasurePVMActualBorelCarrierSet,
    s.1 ∩ t.1 = (∅ : Set ℝ) →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        K.map (spectralMeasurePVMActualBorelCarrierSetUnion s t) x =
          K.map s x + K.map t x

/-- The Dirac-zero map is pointwise additive over disjoint binary unions. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_projection_map_disjoint_union_pointwise_additive
    (s t : SpectralMeasurePVMActualBorelCarrierSet)
    (hdis : s.1 ∩ t.1 = (∅ : Set ℝ))
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMActualBorelDiracZeroProjectionMap
        (spectralMeasurePVMActualBorelCarrierSetUnion s t) x =
      spectralMeasurePVMActualBorelDiracZeroProjectionMap s x +
        spectralMeasurePVMActualBorelDiracZeroProjectionMap t x := by
  classical
  by_cases hs : (0 : ℝ) ∈ s.1
  · by_cases ht : (0 : ℝ) ∈ t.1
    · have hboth : (0 : ℝ) ∈ s.1 ∩ t.1 := ⟨hs, ht⟩
      have hempty : (0 : ℝ) ∈ (∅ : Set ℝ) := by
        simpa [hdis] using hboth
      cases hempty
    · have hunion : (0 : ℝ) ∈ (spectralMeasurePVMActualBorelCarrierSetUnion s t).1 := by
        exact Or.inl hs
      simp [spectralMeasurePVMActualBorelDiracZeroProjectionMap, hs, ht, hunion]
  · by_cases ht : (0 : ℝ) ∈ t.1
    · have hunion : (0 : ℝ) ∈ (spectralMeasurePVMActualBorelCarrierSetUnion s t).1 := by
        exact Or.inr ht
      simp [spectralMeasurePVMActualBorelDiracZeroProjectionMap, hs, ht, hunion]
    · have hunion : (0 : ℝ) ∉ (spectralMeasurePVMActualBorelCarrierSetUnion s t).1 := by
        intro h
        rcases h with hs0 | ht0
        · exact hs hs0
        · exact ht ht0
      simp [spectralMeasurePVMActualBorelDiracZeroProjectionMap, hs, ht, hunion]

/-- The Dirac-zero projection kernel satisfies pointwise disjoint binary finite
additivity. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_projection_kernel_disjoint_union_pointwise_additive :
    SpectralMeasurePVMActualBorelProjectionKernelDisjointUnionPointwiseAdditive
      spectralMeasurePVMActualBorelDiracZeroProjectionKernel := by
  intro s t hdis x
  exact spectral_measure_pvm_actual_borel_dirac_zero_projection_map_disjoint_union_pointwise_additive
    s t hdis x

/-- Dirac-zero finite-additivity law target. -/
def SpectralMeasurePVMActualBorelDiracZeroFiniteAdditivityLawTarget : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroProjectionKernelLawTarget ∧
  SpectralMeasurePVMActualBorelProjectionKernelDisjointUnionPointwiseAdditive
    spectralMeasurePVMActualBorelDiracZeroProjectionKernel

/-- The Dirac-zero finite-additivity law target is ready. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_finite_additivity_law_target_ready :
    SpectralMeasurePVMActualBorelDiracZeroFiniteAdditivityLawTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_projection_kernel_law_target_ready,
    spectral_measure_pvm_actual_borel_dirac_zero_projection_kernel_disjoint_union_pointwise_additive⟩

/-- Dirac-zero finite-additivity bridge.

This advances the residual beyond projection-kernel algebra: the Dirac-zero
actual-Borel kernel now has endpoint laws, pointwise idempotence, intersection
multiplicativity, and pointwise disjoint binary finite additivity.  Countable
additivity remains a separate residual. -/
def SpectralMeasurePVMActualBorelDiracZeroFiniteAdditivityBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroProjectionKernelPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelDiracZeroFiniteAdditivityLawTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The Dirac-zero finite-additivity bridge is ready. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_finite_additivity_bridge_ready :
    SpectralMeasurePVMActualBorelDiracZeroFiniteAdditivityBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_projection_kernel_public_boundary_held,
    spectral_measure_pvm_actual_borel_dirac_zero_finite_additivity_law_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after Dirac-zero finite additivity. -/
def SpectralMeasurePVMActualBorelDiracZeroFiniteAdditivityPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroFiniteAdditivityBridgeReady ∧
  SpectralMeasurePVMActualBorelDiracZeroFiniteAdditivityLawTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after Dirac-zero finite additivity is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_finite_additivity_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroFiniteAdditivityPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_finite_additivity_bridge_ready,
    spectral_measure_pvm_actual_borel_dirac_zero_finite_additivity_law_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
