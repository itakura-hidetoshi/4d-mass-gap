import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelProjectionKernel

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Dirac-zero actual-Borel projection map.

A Borel set receives the identity projection precisely when it contains the
base point `0 : ℝ`; otherwise it receives the zero projection.  Unlike the
endpoint-seeded shell map, this is compatible with intersection in the PVM
sense, pointwise. -/
def spectralMeasurePVMActualBorelDiracZeroProjectionMap
    (s : SpectralMeasurePVMActualBorelCarrierSet) :
    SpectralMeasurePVMActualBorelProjectionOperator := by
  classical
  exact
    if (0 : ℝ) ∈ s.1 then
      ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier
    else
      0

/-- The Dirac-zero map sends the empty Borel set to zero. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_projection_map_empty :
    spectralMeasurePVMActualBorelDiracZeroProjectionMap
      spectralMeasurePVMActualBorelEmptySet = 0 := by
  classical
  simp [spectralMeasurePVMActualBorelDiracZeroProjectionMap,
    spectralMeasurePVMActualBorelEmptySet]

/-- The Dirac-zero map sends the universal Borel set to the identity. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_projection_map_univ :
    spectralMeasurePVMActualBorelDiracZeroProjectionMap
      spectralMeasurePVMActualBorelUnivSet =
        ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier := by
  classical
  simp [spectralMeasurePVMActualBorelDiracZeroProjectionMap,
    spectralMeasurePVMActualBorelUnivSet]

/-- The Dirac-zero actual-Borel projection map takes only the values zero and
identity. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_projection_map_zero_or_identity
    (s : SpectralMeasurePVMActualBorelCarrierSet) :
    spectralMeasurePVMActualBorelDiracZeroProjectionMap s = 0 ∨
      spectralMeasurePVMActualBorelDiracZeroProjectionMap s =
        ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier := by
  classical
  by_cases hs : (0 : ℝ) ∈ s.1
  · right
    simp [spectralMeasurePVMActualBorelDiracZeroProjectionMap, hs]
  · left
    simp [spectralMeasurePVMActualBorelDiracZeroProjectionMap, hs]

/-- Every value of the Dirac-zero actual-Borel projection map is pointwise
idempotent. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_projection_map_pointwise_idempotent
    (s : SpectralMeasurePVMActualBorelCarrierSet) :
    SpectralMeasurePVMActualBorelProjectionOperatorPointwiseIdempotent
      (spectralMeasurePVMActualBorelDiracZeroProjectionMap s) := by
  classical
  intro x
  by_cases hs : (0 : ℝ) ∈ s.1
  · simp [spectralMeasurePVMActualBorelDiracZeroProjectionMap, hs]
  · simp [spectralMeasurePVMActualBorelDiracZeroProjectionMap, hs]

/-- The Dirac-zero map is multiplicative over intersections, pointwise.

This is the first concrete PVM-style algebra law for arbitrary actual-Borel
carrier sets: `E(S ∩ T) = E(S) E(T)` is stated pointwise to avoid depending on
extra operator-composition API names. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_projection_map_inter_pointwise_multiplicative
    (s t : SpectralMeasurePVMActualBorelCarrierSet)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMActualBorelDiracZeroProjectionMap
        (spectralMeasurePVMActualBorelCarrierSetInter s t) x =
      spectralMeasurePVMActualBorelDiracZeroProjectionMap s
        (spectralMeasurePVMActualBorelDiracZeroProjectionMap t x) := by
  classical
  by_cases hs : (0 : ℝ) ∈ s.1
  · by_cases ht : (0 : ℝ) ∈ t.1
    · simp [spectralMeasurePVMActualBorelDiracZeroProjectionMap,
        spectralMeasurePVMActualBorelCarrierSetInter, hs, ht]
    · simp [spectralMeasurePVMActualBorelDiracZeroProjectionMap,
        spectralMeasurePVMActualBorelCarrierSetInter, hs, ht]
  · by_cases ht : (0 : ℝ) ∈ t.1
    · simp [spectralMeasurePVMActualBorelDiracZeroProjectionMap,
        spectralMeasurePVMActualBorelCarrierSetInter, hs, ht]
    · simp [spectralMeasurePVMActualBorelDiracZeroProjectionMap,
        spectralMeasurePVMActualBorelCarrierSetInter, hs, ht]

/-- Concrete Dirac-zero projection kernel. -/
def spectralMeasurePVMActualBorelDiracZeroProjectionKernel :
    SpectralMeasurePVMActualBorelProjectionKernel where
  map := spectralMeasurePVMActualBorelDiracZeroProjectionMap
  empty_maps_to_zero :=
    spectral_measure_pvm_actual_borel_dirac_zero_projection_map_empty
  univ_maps_to_identity :=
    spectral_measure_pvm_actual_borel_dirac_zero_projection_map_univ
  pointwise_idempotent :=
    spectral_measure_pvm_actual_borel_dirac_zero_projection_map_pointwise_idempotent

/-- Pointwise PVM-style intersection law for a concrete actual-Borel projection
kernel. -/
def SpectralMeasurePVMActualBorelProjectionKernelInterPointwiseMultiplicative
    (K : SpectralMeasurePVMActualBorelProjectionKernel) : Prop :=
  ∀ s t : SpectralMeasurePVMActualBorelCarrierSet,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      K.map (spectralMeasurePVMActualBorelCarrierSetInter s t) x =
        K.map s (K.map t x)

/-- The Dirac-zero kernel satisfies the pointwise intersection multiplicativity
law. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_projection_kernel_inter_pointwise_multiplicative :
    SpectralMeasurePVMActualBorelProjectionKernelInterPointwiseMultiplicative
      spectralMeasurePVMActualBorelDiracZeroProjectionKernel := by
  intro s t x
  exact spectral_measure_pvm_actual_borel_dirac_zero_projection_map_inter_pointwise_multiplicative s t x

/-- Dirac-zero actual-Borel projection-kernel law target. -/
def SpectralMeasurePVMActualBorelDiracZeroProjectionKernelLawTarget : Prop :=
  spectralMeasurePVMActualBorelDiracZeroProjectionKernel.map
      spectralMeasurePVMActualBorelEmptySet = 0 ∧
  spectralMeasurePVMActualBorelDiracZeroProjectionKernel.map
      spectralMeasurePVMActualBorelUnivSet =
        ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier ∧
  (∀ s : SpectralMeasurePVMActualBorelCarrierSet,
    SpectralMeasurePVMActualBorelProjectionOperatorPointwiseIdempotent
      (spectralMeasurePVMActualBorelDiracZeroProjectionKernel.map s)) ∧
  SpectralMeasurePVMActualBorelProjectionKernelInterPointwiseMultiplicative
    spectralMeasurePVMActualBorelDiracZeroProjectionKernel

/-- The Dirac-zero kernel laws are ready. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_projection_kernel_law_target_ready :
    SpectralMeasurePVMActualBorelDiracZeroProjectionKernelLawTarget := by
  exact ⟨
    spectralMeasurePVMActualBorelDiracZeroProjectionKernel.empty_maps_to_zero,
    spectralMeasurePVMActualBorelDiracZeroProjectionKernel.univ_maps_to_identity,
    spectralMeasurePVMActualBorelDiracZeroProjectionKernel.pointwise_idempotent,
    spectral_measure_pvm_actual_borel_dirac_zero_projection_kernel_inter_pointwise_multiplicative⟩

/-- Actual-Borel Dirac-zero projection-kernel bridge.

This advances residual 1 beyond a mere projection-valued interface: it gives a
concrete Dirac PVM-style kernel on the actual Borel carrier, with endpoint laws,
pointwise idempotence, and pointwise intersection multiplicativity. Countable
additivity is still a separate residual and remains explicitly open. -/
def SpectralMeasurePVMActualBorelDiracZeroProjectionKernelBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelProjectionKernelPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelDiracZeroProjectionKernelLawTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual-Borel Dirac-zero projection-kernel bridge is ready. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_projection_kernel_bridge_ready :
    SpectralMeasurePVMActualBorelDiracZeroProjectionKernelBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_projection_kernel_public_boundary_held,
    spectral_measure_pvm_actual_borel_dirac_zero_projection_kernel_law_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the Dirac-zero projection-kernel bridge. -/
def SpectralMeasurePVMActualBorelDiracZeroProjectionKernelPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroProjectionKernelBridgeReady ∧
  SpectralMeasurePVMActualBorelDiracZeroProjectionKernelLawTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the Dirac-zero projection-kernel bridge is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_projection_kernel_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroProjectionKernelPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_projection_kernel_bridge_ready,
    spectral_measure_pvm_actual_borel_dirac_zero_projection_kernel_law_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
