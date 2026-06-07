import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologyBranchEventualConvergenceCertificate

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Tail pairwise agreement extracted from an eventual-convergence certificate.

Once the finite partial operator sequence agrees with the same countable-union
limit slot after a cutoff, any two tail terms agree with each other.  This is the
pure equality/Cauchy core of the current concrete operator-topology convergence
surface. -/
def SpectralMeasurePVMOperatorTopologyBranchTailPairwiseAgreement
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (c : SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s) : Prop :=
  ∀ m n : Nat,
    spectralMeasurePVMConcreteNormalizationCandidate
        (SpectralMeasurePVMConcreteFinitePartialUnion (c.cutoff + m) s) =
      spectralMeasurePVMConcreteNormalizationCandidate
        (SpectralMeasurePVMConcreteFinitePartialUnion (c.cutoff + n) s)

/-- An eventual-convergence certificate gives tail pairwise agreement. -/
theorem spectral_measure_pvm_operator_topology_branch_tail_pairwise_agreement_from_certificate
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (c : SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s) :
    SpectralMeasurePVMOperatorTopologyBranchTailPairwiseAgreement s c := by
  intro m n
  calc
    spectralMeasurePVMConcreteNormalizationCandidate
        (SpectralMeasurePVMConcreteFinitePartialUnion (c.cutoff + m) s)
        = spectralMeasurePVMConcreteNormalizationCandidate c.limitSlot :=
          c.eventually_agrees_with_limit_slot m
    _ = spectralMeasurePVMConcreteNormalizationCandidate
        (SpectralMeasurePVMConcreteFinitePartialUnion (c.cutoff + n) s) :=
          (c.eventually_agrees_with_limit_slot n).symm

/-- A realized branch supplies a certificate whose tail is pairwise constant. -/
theorem spectral_measure_pvm_operator_topology_branch_realization_case_tail_pairwise_agreement
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    ∃ c : SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s,
      SpectralMeasurePVMOperatorTopologyBranchTailPairwiseAgreement s c := by
  rcases spectral_measure_pvm_operator_topology_branch_realization_case_eventual_convergence_certificate s hcase with
    ⟨c, _⟩
  exact ⟨c, spectral_measure_pvm_operator_topology_branch_tail_pairwise_agreement_from_certificate s c⟩

/-- Tail pairwise agreement packaged with the branch eventual-convergence bridge.
This is the concrete Cauchy-style surface available before replacing the current
symbolic operator-topology target by a genuine strong/weak operator topology
limit. -/
def SpectralMeasurePVMOperatorTopologyBranchTailPairwiseAgreementBridgeReady
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  (∃ c : SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificate s,
    SpectralMeasurePVMOperatorTopologyBranchTailPairwiseAgreement s c) ∧
  SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificateBridgeReady s

/-- A realized branch supplies tail pairwise agreement and the eventual-convergence
certificate bridge. -/
theorem spectral_measure_pvm_operator_topology_branch_tail_pairwise_agreement_bridge_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    SpectralMeasurePVMOperatorTopologyBranchTailPairwiseAgreementBridgeReady s := by
  exact ⟨
    spectral_measure_pvm_operator_topology_branch_realization_case_tail_pairwise_agreement s hcase,
    spectral_measure_pvm_operator_topology_branch_eventual_convergence_certificate_bridge_ready s hcase⟩

/-- The canonical empty countable family has tail pairwise agreement. -/
theorem spectral_measure_pvm_operator_topology_canonical_empty_family_tail_pairwise_agreement_bridge_ready :
    SpectralMeasurePVMOperatorTopologyBranchTailPairwiseAgreementBridgeReady
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  exact spectral_measure_pvm_operator_topology_branch_tail_pairwise_agreement_bridge_ready
    spectralMeasurePVMConcreteEmptyCountableFamily
    spectral_measure_pvm_operator_topology_canonical_empty_family_branch_realization_case

/-- The canonical pinned single-whole family has tail pairwise agreement at any
pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_tail_pairwise_agreement_bridge_ready
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyBranchTailPairwiseAgreementBridgeReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  exact spectral_measure_pvm_operator_topology_branch_tail_pairwise_agreement_bridge_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k)
    (spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_realization_case k)

end

end Theorem
end R4
end MGAP4D
