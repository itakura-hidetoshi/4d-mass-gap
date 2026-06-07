import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroFiniteAdditivity
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelCountableUnionClosure

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Pairwise disjointness for an actual-Borel countable family, stated after
forgetting to `Set ℝ`. -/
def SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint
    (F : ℕ → SpectralMeasurePVMActualBorelCarrierSet) : Prop :=
  ∀ m n : ℕ, m ≠ n → (F m).1 ∩ (F n).1 = (∅ : Set ℝ)

/-- In a pairwise-disjoint actual-Borel family, the Dirac base point `0` can
belong to at most one member. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_pairwise_disjoint_hit_unique
    (F : ℕ → SpectralMeasurePVMActualBorelCarrierSet)
    (hdis : SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F)
    {m n : ℕ}
    (hm : (0 : ℝ) ∈ (F m).1)
    (hn : (0 : ℝ) ∈ (F n).1) :
    m = n := by
  by_contra hne
  have hboth : (0 : ℝ) ∈ (F m).1 ∩ (F n).1 := ⟨hm, hn⟩
  have hempty : (0 : ℝ) ∈ (∅ : Set ℝ) := by
    simpa [hdis m n hne] using hboth
  cases hempty

/-- The actual-Borel countable union contains the Dirac base point exactly when
one member contains it. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_iUnion_mem_zero_iff_exists
    (F : ℕ → SpectralMeasurePVMActualBorelCarrierSet) :
    (0 : ℝ) ∈ (spectralMeasurePVMActualBorelCarrierSetIUnion F).1 ↔
      ∃ n : ℕ, (0 : ℝ) ∈ (F n).1 := by
  simp [spectralMeasurePVMActualBorelCarrierSetIUnion]

/-- If no member of a countable actual-Borel family contains `0`, then its
Dirac-zero projection over the countable union is zero. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_iUnion_projection_zero_of_no_hit
    (F : ℕ → SpectralMeasurePVMActualBorelCarrierSet)
    (hno : ¬ ∃ n : ℕ, (0 : ℝ) ∈ (F n).1) :
    spectralMeasurePVMActualBorelDiracZeroProjectionMap
      (spectralMeasurePVMActualBorelCarrierSetIUnion F) = 0 := by
  classical
  have hnot : (0 : ℝ) ∉ (spectralMeasurePVMActualBorelCarrierSetIUnion F).1 := by
    intro hmem
    exact hno ((spectral_measure_pvm_actual_borel_dirac_zero_iUnion_mem_zero_iff_exists F).1 hmem)
  simp [spectralMeasurePVMActualBorelDiracZeroProjectionMap, hnot]

/-- If some member of a countable actual-Borel family contains `0`, then its
Dirac-zero projection over the countable union is the identity. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_iUnion_projection_id_of_hit
    (F : ℕ → SpectralMeasurePVMActualBorelCarrierSet)
    (hhit : ∃ n : ℕ, (0 : ℝ) ∈ (F n).1) :
    spectralMeasurePVMActualBorelDiracZeroProjectionMap
      (spectralMeasurePVMActualBorelCarrierSetIUnion F) =
        ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier := by
  classical
  have hmem : (0 : ℝ) ∈ (spectralMeasurePVMActualBorelCarrierSetIUnion F).1 :=
    (spectral_measure_pvm_actual_borel_dirac_zero_iUnion_mem_zero_iff_exists F).2 hhit
  simp [spectralMeasurePVMActualBorelDiracZeroProjectionMap, hmem]

/-- For a pairwise-disjoint family with a hit at `k`, every other member has zero
Dirac-zero projection. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_pairwise_disjoint_other_projection_zero
    (F : ℕ → SpectralMeasurePVMActualBorelCarrierSet)
    (hdis : SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F)
    {k n : ℕ}
    (hk : (0 : ℝ) ∈ (F k).1)
    (hne : n ≠ k) :
    spectralMeasurePVMActualBorelDiracZeroProjectionMap (F n) = 0 := by
  classical
  have hnot : (0 : ℝ) ∉ (F n).1 := by
    intro hn
    have hnk : n = k :=
      spectral_measure_pvm_actual_borel_dirac_zero_pairwise_disjoint_hit_unique
        F hdis hn hk
    exact hne hnk
  simp [spectralMeasurePVMActualBorelDiracZeroProjectionMap, hnot]

/-- For a pairwise-disjoint family with a hit at `k`, the countable-union
projection agrees with the `k`-th projection. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_iUnion_projection_eq_hit_projection
    (F : ℕ → SpectralMeasurePVMActualBorelCarrierSet)
    (hdis : SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F)
    {k : ℕ}
    (hk : (0 : ℝ) ∈ (F k).1) :
    spectralMeasurePVMActualBorelDiracZeroProjectionMap
      (spectralMeasurePVMActualBorelCarrierSetIUnion F) =
        spectralMeasurePVMActualBorelDiracZeroProjectionMap (F k) := by
  classical
  have hhit : ∃ n : ℕ, (0 : ℝ) ∈ (F n).1 := ⟨k, hk⟩
  have hleft :=
    spectral_measure_pvm_actual_borel_dirac_zero_iUnion_projection_id_of_hit F hhit
  have hright :
      spectralMeasurePVMActualBorelDiracZeroProjectionMap (F k) =
        ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier := by
    simp [spectralMeasurePVMActualBorelDiracZeroProjectionMap, hk]
  exact hleft.trans hright.symm

/-- Countable-support law target for the Dirac-zero kernel. -/
def SpectralMeasurePVMActualBorelDiracZeroCountableSupportLawTarget : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroFiniteAdditivityLawTarget ∧
  (∀ F : ℕ → SpectralMeasurePVMActualBorelCarrierSet,
    SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F →
      ∀ k : ℕ,
        (0 : ℝ) ∈ (F k).1 →
          spectralMeasurePVMActualBorelDiracZeroProjectionMap
            (spectralMeasurePVMActualBorelCarrierSetIUnion F) =
              spectralMeasurePVMActualBorelDiracZeroProjectionMap (F k)) ∧
  (∀ F : ℕ → SpectralMeasurePVMActualBorelCarrierSet,
    (¬ ∃ n : ℕ, (0 : ℝ) ∈ (F n).1) →
      spectralMeasurePVMActualBorelDiracZeroProjectionMap
        (spectralMeasurePVMActualBorelCarrierSetIUnion F) = 0)

/-- The Dirac-zero countable-support law target is ready. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_countable_support_law_target_ready :
    SpectralMeasurePVMActualBorelDiracZeroCountableSupportLawTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_finite_additivity_law_target_ready,
    (by
      intro F hdis k hk
      exact spectral_measure_pvm_actual_borel_dirac_zero_iUnion_projection_eq_hit_projection
        F hdis hk),
    (by
      intro F hno
      exact spectral_measure_pvm_actual_borel_dirac_zero_iUnion_projection_zero_of_no_hit
        F hno)⟩

/-- Dirac-zero countable-support bridge.

This is the countable-support spine for residual 1: in a disjoint countable
family, the Dirac support can hit at most one member, and the projection over the
countable union is either the unique hit projection or zero.  Full
operator-topology countable additivity is still left as the next residual. -/
def SpectralMeasurePVMActualBorelDiracZeroCountableSupportBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroFiniteAdditivityPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelCountableUnionClosurePublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelDiracZeroCountableSupportLawTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The Dirac-zero countable-support bridge is ready. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_countable_support_bridge_ready :
    SpectralMeasurePVMActualBorelDiracZeroCountableSupportBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_finite_additivity_public_boundary_held,
    spectral_measure_pvm_actual_borel_countable_union_closure_public_boundary_held,
    spectral_measure_pvm_actual_borel_dirac_zero_countable_support_law_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the Dirac-zero countable-support bridge. -/
def SpectralMeasurePVMActualBorelDiracZeroCountableSupportPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroCountableSupportBridgeReady ∧
  SpectralMeasurePVMActualBorelDiracZeroCountableSupportLawTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the Dirac-zero countable-support bridge is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_countable_support_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroCountableSupportPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_countable_support_bridge_ready,
    spectral_measure_pvm_actual_borel_dirac_zero_countable_support_law_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
