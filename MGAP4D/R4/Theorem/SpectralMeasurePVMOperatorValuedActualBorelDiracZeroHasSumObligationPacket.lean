import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroAbstractTsumCandidate

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Zero-series analytic obligation for the eventual concrete `HasSum` / `tsum`
instantiation.

A concrete Mathlib `tsum` candidate must send every Dirac-zero zero-series input
to the zero projection. -/
def SpectralMeasurePVMActualBorelDiracZeroHasSumZeroSeriesObligation
    (TsumCandidate : SpectralMeasurePVMActualBorelDiracZeroAbstractTsumCandidate) : Prop :=
  ∀ F : SpectralMeasurePVMActualBorelCountableFamily,
    SpectralMeasurePVMActualBorelDiracZeroTsumZeroSeriesInput F →
      TsumCandidate (spectralMeasurePVMActualBorelDiracZeroSummandFamily F) = 0

/-- One-hit-series analytic obligation for the eventual concrete `HasSum` /
`tsum` instantiation.

A concrete Mathlib `tsum` candidate must send every one-hit input to its unique
nonzero projection. -/
def SpectralMeasurePVMActualBorelDiracZeroHasSumOneHitSeriesObligation
    (TsumCandidate : SpectralMeasurePVMActualBorelDiracZeroAbstractTsumCandidate) : Prop :=
  ∀ (F : SpectralMeasurePVMActualBorelCountableFamily) (k : ℕ),
    SpectralMeasurePVMActualBorelDiracZeroTsumOneHitSeriesInput F k →
      TsumCandidate (spectralMeasurePVMActualBorelDiracZeroSummandFamily F) =
        spectralMeasurePVMActualBorelDiracZeroProjectionMap (F k)

/-- The two concrete analytic obligations are exactly the compatibility condition
used by the abstract `tsum` candidate bridge. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_hassum_obligations_iff_compatible
    (TsumCandidate : SpectralMeasurePVMActualBorelDiracZeroAbstractTsumCandidate) :
    (SpectralMeasurePVMActualBorelDiracZeroHasSumZeroSeriesObligation TsumCandidate ∧
      SpectralMeasurePVMActualBorelDiracZeroHasSumOneHitSeriesObligation TsumCandidate) ↔
      SpectralMeasurePVMActualBorelDiracZeroAbstractTsumCandidateCompatible TsumCandidate := by
  constructor
  · intro h
    exact {
      zeroSeries := h.1
      oneHitSeries := h.2 }
  · intro h
    exact ⟨h.zeroSeries, h.oneHitSeries⟩

/-- If the two HasSum obligations are supplied, the abstract candidate realizes
countable additivity on pairwise-disjoint Dirac-zero actual-Borel families. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_hassum_obligations_realize_countable_additivity
    (TsumCandidate : SpectralMeasurePVMActualBorelDiracZeroAbstractTsumCandidate)
    (hzero : SpectralMeasurePVMActualBorelDiracZeroHasSumZeroSeriesObligation TsumCandidate)
    (hone : SpectralMeasurePVMActualBorelDiracZeroHasSumOneHitSeriesObligation TsumCandidate)
    (F : SpectralMeasurePVMActualBorelCountableFamily)
    (hdis : SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F) :
    TsumCandidate (spectralMeasurePVMActualBorelDiracZeroSummandFamily F) =
      spectralMeasurePVMActualBorelDiracZeroUnionProjection F := by
  have hcompat : SpectralMeasurePVMActualBorelDiracZeroAbstractTsumCandidateCompatible TsumCandidate :=
    (spectral_measure_pvm_actual_borel_dirac_zero_hassum_obligations_iff_compatible TsumCandidate).1
      ⟨hzero, hone⟩
  exact spectral_measure_pvm_actual_borel_dirac_zero_abstract_tsum_candidate_realizes_pairwise_disjoint_family
    TsumCandidate hcompat F hdis

/-- Final obligation packet for the Dirac-zero HasSum step.

The remaining analytic task is no longer entangled with Borel-set algebra or
projection-kernel reasoning: instantiate a concrete `TsumCandidate` and discharge
exactly the zero-series and one-hit-series obligations. -/
def SpectralMeasurePVMActualBorelDiracZeroHasSumObligationPacketReady : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroAbstractTsumCandidatePublicBoundaryHeld ∧
  (∀ TsumCandidate : SpectralMeasurePVMActualBorelDiracZeroAbstractTsumCandidate,
    SpectralMeasurePVMActualBorelDiracZeroHasSumZeroSeriesObligation TsumCandidate →
    SpectralMeasurePVMActualBorelDiracZeroHasSumOneHitSeriesObligation TsumCandidate →
      ∀ F : SpectralMeasurePVMActualBorelCountableFamily,
        SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F →
          TsumCandidate (spectralMeasurePVMActualBorelDiracZeroSummandFamily F) =
            spectralMeasurePVMActualBorelDiracZeroUnionProjection F) ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The final obligation packet for the Dirac-zero HasSum step is ready. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_hassum_obligation_packet_ready :
    SpectralMeasurePVMActualBorelDiracZeroHasSumObligationPacketReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_abstract_tsum_candidate_public_boundary_held,
    spectral_measure_pvm_actual_borel_dirac_zero_hassum_obligations_realize_countable_additivity,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the Dirac-zero HasSum obligation packet. -/
def SpectralMeasurePVMActualBorelDiracZeroHasSumObligationPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroHasSumObligationPacketReady ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the Dirac-zero HasSum obligation packet is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_hassum_obligation_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroHasSumObligationPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_hassum_obligation_packet_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
