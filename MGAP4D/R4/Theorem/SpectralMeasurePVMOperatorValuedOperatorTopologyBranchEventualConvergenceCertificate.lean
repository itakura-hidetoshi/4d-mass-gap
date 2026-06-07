import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologyBranchLimitSlotAgreement

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Branch-level eventual-constant convergence certificate.

This is the concrete computational core behind the operator-topology convergence
slot at the current R4 two-branch stage: after a finite cutoff, the finite
partial operator sequence is exactly equal to the branch's countable-union limit
slot. -/
structure SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate
    (s : SpectralMeasurePVMConcreteCountableFamily) where
  cutoff : Nat
  limitSlot : SpectralMeasurePVMConcreteIndex
  eventually_agrees_with_limit_slot :
    ∀ m : Nat,
      spectralMeasurePVMConcreteNormalizationCandidate
          (SpectralMeasurePVMConcreteFinitePartialUnion (cutoff + m) s) =
        spectralMeasurePVMConcreteNormalizationCandidate limitSlot

/-- The all-empty branch yields an eventual-convergence certificate with cutoff
zero and empty limit slot. -/
def spectralMeasurePVMOperatorTopologyAllEmptyEventualConvergenceCertificate
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hs : SpectralMeasurePVMConcreteAllEmptyFamily s) :
    SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s :=
  { cutoff := 0
    limitSlot := SpectralMeasurePVMConcreteCountableUnionAllEmpty s
    eventually_agrees_with_limit_slot := by
      intro m
      calc
        spectralMeasurePVMConcreteNormalizationCandidate
            (SpectralMeasurePVMConcreteFinitePartialUnion (0 + m) s)
            = SpectralMeasurePVMConcreteBoundedOperator.zero := by
              simpa using spectral_measure_pvm_concrete_partial_sum_all_empty_zero s hs m
        _ = spectralMeasurePVMConcreteNormalizationCandidate
            (SpectralMeasurePVMConcreteCountableUnionAllEmpty s) :=
              (spectral_measure_pvm_concrete_countable_all_empty_additivity s hs).symm }

/-- The pinned single-whole branch yields an eventual-convergence certificate
with cutoff the successor of the pinned support and whole limit slot. -/
def spectralMeasurePVMOperatorTopologySingleWholeEventualConvergenceCertificate
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat)
    (hs : SpectralMeasurePVMConcreteSingleWholeAt s k) :
    SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s :=
  { cutoff := Nat.succ k
    limitSlot := SpectralMeasurePVMConcreteCountableUnionSingleWholeAt s k
    eventually_agrees_with_limit_slot := by
      intro m
      calc
        spectralMeasurePVMConcreteNormalizationCandidate
            (SpectralMeasurePVMConcreteFinitePartialUnion (Nat.succ k + m) s)
            = SpectralMeasurePVMConcreteBoundedOperator.identity :=
              spectral_measure_pvm_operator_topology_single_whole_eventually_constant_identity_sequence_ready s k hs m
        _ = spectralMeasurePVMConcreteNormalizationCandidate
            (SpectralMeasurePVMConcreteCountableUnionSingleWholeAt s k) :=
              (spectral_measure_pvm_concrete_countable_single_whole_additivity s k hs).symm }

/-- Every realized concrete branch supplies an eventual-convergence certificate. -/
theorem spectral_measure_pvm_operator_topology_branch_realization_case_eventual_convergence_certificate
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    ∃ c : SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s,
      True := by
  cases hcase with
  | allEmpty hs =>
      exact ⟨spectralMeasurePVMOperatorTopologyAllEmptyEventualConvergenceCertificate s hs, trivial⟩
  | singleWholeAt k hs =>
      exact ⟨spectralMeasurePVMOperatorTopologySingleWholeEventualConvergenceCertificate s k hs, trivial⟩

/-- Eventual-convergence certificate packaged with the concrete operator-topology
convergence target and the branch limit-slot agreement bridge. -/
def SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificateBridgeReady
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  (∃ c : SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s,
    True) ∧
  SpectralMeasurePVMConcreteOperatorTopologyConvergenceTarget ∧
  SpectralMeasurePVMOperatorTopologyBranchLimitSlotAgreementBridgeReady s

/-- A realized branch supplies an eventual-convergence certificate, the concrete
operator-topology convergence target, and the limit-slot agreement bridge. -/
theorem spectral_measure_pvm_operator_topology_branch_eventual_convergence_certificate_bridge_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificateBridgeReady s := by
  exact ⟨
    spectral_measure_pvm_operator_topology_branch_realization_case_eventual_convergence_certificate s hcase,
    spectral_measure_pvm_concrete_operator_topology_convergence_target_ready,
    spectral_measure_pvm_operator_topology_branch_limit_slot_agreement_bridge_ready s hcase⟩

/-- The canonical empty countable family has an eventual-convergence certificate
bridge. -/
theorem spectral_measure_pvm_operator_topology_canonical_empty_family_eventual_convergence_certificate_bridge_ready :
    SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificateBridgeReady
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  exact spectral_measure_pvm_operator_topology_branch_eventual_convergence_certificate_bridge_ready
    spectralMeasurePVMConcreteEmptyCountableFamily
    spectral_measure_pvm_operator_topology_canonical_empty_family_branch_realization_case

/-- The canonical pinned single-whole family has an eventual-convergence
certificate bridge at any pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_eventual_convergence_certificate_bridge_ready
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificateBridgeReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  exact spectral_measure_pvm_operator_topology_branch_eventual_convergence_certificate_bridge_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k)
    (spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_realization_case k)

end

end Theorem
end R4
end MGAP4D
