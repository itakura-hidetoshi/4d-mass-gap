import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroHasSumObligationPacket

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Concrete `tsum` candidate for Dirac-zero actual-Borel projection families. -/
def spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate :
    SpectralMeasurePVMActualBorelDiracZeroAbstractTsumCandidate :=
  fun f => ∑' n : ℕ, f n

/-- The concrete `tsum` candidate reads zero-series inputs as zero. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_concrete_tsum_zero_series_obligation :
    SpectralMeasurePVMActualBorelDiracZeroHasSumZeroSeriesObligation
      spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate := by
  intro F hzero
  dsimp [spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate,
    spectralMeasurePVMActualBorelDiracZeroSummandFamily]
  have hseries :
      (fun n : ℕ => spectralMeasurePVMActualBorelDiracZeroProjectionMap (F n)) =
        fun _ : ℕ => (0 : SpectralMeasurePVMActualBorelProjectionOperator) := by
    funext n
    exact hzero.2 n
  rw [hseries]
  exact tsum_zero

/-- The concrete `tsum` candidate reads one-hit-series inputs as the unique
nonzero summand. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_concrete_tsum_one_hit_series_obligation :
    SpectralMeasurePVMActualBorelDiracZeroHasSumOneHitSeriesObligation
      spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate := by
  intro F k hone
  dsimp [spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate,
    spectralMeasurePVMActualBorelDiracZeroSummandFamily]
  exact tsum_eq_single k hone.2

/-- The concrete `tsum` candidate is compatible with the Dirac-zero reduced
inputs. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_concrete_tsum_candidate_compatible :
    SpectralMeasurePVMActualBorelDiracZeroAbstractTsumCandidateCompatible
      spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate := by
  exact {
    zeroSeries :=
      spectral_measure_pvm_actual_borel_dirac_zero_concrete_tsum_zero_series_obligation
    oneHitSeries :=
      spectral_measure_pvm_actual_borel_dirac_zero_concrete_tsum_one_hit_series_obligation }

/-- Concrete `tsum` realizes countable additivity for pairwise-disjoint
Dirac-zero actual-Borel families. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_concrete_tsum_realizes_countable_additivity
    (F : SpectralMeasurePVMActualBorelCountableFamily)
    (hdis : SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F) :
    spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate
        (spectralMeasurePVMActualBorelDiracZeroSummandFamily F) =
      spectralMeasurePVMActualBorelDiracZeroUnionProjection F := by
  exact spectral_measure_pvm_actual_borel_dirac_zero_hassum_obligations_realize_countable_additivity
    spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate
    spectral_measure_pvm_actual_borel_dirac_zero_concrete_tsum_zero_series_obligation
    spectral_measure_pvm_actual_borel_dirac_zero_concrete_tsum_one_hit_series_obligation
    F hdis

/-- Concrete Dirac-zero countable additivity is closed at the `tsum` level.

This closes the residual for the Dirac-zero actual-Borel kernel: the concrete
`tsum` of the summand projection family equals the projection of the countable
union for every pairwise-disjoint actual-Borel countable family. -/
def SpectralMeasurePVMActualBorelDiracZeroConcreteTsumCountableAdditivityClosed : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroHasSumObligationPacketReady ∧
  SpectralMeasurePVMActualBorelDiracZeroHasSumZeroSeriesObligation
    spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate ∧
  SpectralMeasurePVMActualBorelDiracZeroHasSumOneHitSeriesObligation
    spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate ∧
  (∀ F : SpectralMeasurePVMActualBorelCountableFamily,
    SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint F →
      spectralMeasurePVMActualBorelDiracZeroConcreteTsumCandidate
          (spectralMeasurePVMActualBorelDiracZeroSummandFamily F) =
        spectralMeasurePVMActualBorelDiracZeroUnionProjection F) ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Concrete Dirac-zero countable additivity is closed at the `tsum` level. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_concrete_tsum_countable_additivity_closed :
    SpectralMeasurePVMActualBorelDiracZeroConcreteTsumCountableAdditivityClosed := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_hassum_obligation_packet_ready,
    spectral_measure_pvm_actual_borel_dirac_zero_concrete_tsum_zero_series_obligation,
    spectral_measure_pvm_actual_borel_dirac_zero_concrete_tsum_one_hit_series_obligation,
    spectral_measure_pvm_actual_borel_dirac_zero_concrete_tsum_realizes_countable_additivity,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after closing the Dirac-zero concrete `tsum` countable
additivity residual. -/
def SpectralMeasurePVMActualBorelDiracZeroConcreteTsumCountableAdditivityPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroConcreteTsumCountableAdditivityClosed ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after closing the Dirac-zero concrete `tsum` countable
additivity residual is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_concrete_tsum_countable_additivity_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroConcreteTsumCountableAdditivityPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_concrete_tsum_countable_additivity_closed,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
