import MGAP4D.Constructive.FinalTheorem
import MGAP4D.Plaquette.ObservableSpectralWeight
import MGAP4D.Spectral.SectorSeparationCoreBridge

namespace MGAP4D
namespace Constructive

/-- A pre-Mathlib bridge from the observable spectral-weight certificate into
the constructive final-theorem packet.

This records that the final theorem packet's plaquette witness is the same
`A_{p,g}` positive spectral-weight witness at the normalized `33/20` value, and
that the witness remains attached to the orthogonal sector. -/
structure ObservableSpectralWeightFinalBridge where
  finalPacket : FinalTheoremPacket
  finalPacketIs3320 : finalPacket = finalTheoremPacket3320
  spectralWeight : Plaquette.ObservableSpectralWeightCertificate
  spectralWeightReady : spectralWeight.ready
  finalPlaquetteMatchesWeight : finalPacket.plaquette.observableWitness = spectralWeight.massWitness
  finalGapMatchesWeightValue : finalPacket.plaquette.gapRecord.value = spectralWeight.value
  finalMassValueIs3320 : finalPacket.massGap.value = 33 / 20
  finalEigenvalueIs3320 : finalPacket.eigenvector.eigenvalue = 33 / 20
  finalPlaquettePositive : finalPacket.plaquette.observableWitness.positiveMass = true
  witnessSectorOrthogonal : spectralWeight.sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal
  witnessNotVacuum : spectralWeight.sectorSeparation.witnessSector ≠ Spectral.SpectralSector.vacuum
  sectorCoreBridge : Spectral.SectorSeparationCoreBridge
  sectorCoreBridgeReady : sectorCoreBridge.ready
  finalBridgeVisible : Prop
  theoremBoundaryHeld : Prop

def ObservableSpectralWeightFinalBridge.ready
    (B : ObservableSpectralWeightFinalBridge) : Prop :=
  B.finalPacketIs3320 ∧ B.spectralWeightReady ∧ B.finalPlaquetteMatchesWeight ∧
  B.finalGapMatchesWeightValue ∧ B.finalMassValueIs3320 ∧ B.finalEigenvalueIs3320 ∧
  B.finalPlaquettePositive ∧ B.witnessSectorOrthogonal ∧ B.witnessNotVacuum ∧
  B.sectorCoreBridgeReady ∧ B.finalBridgeVisible ∧ B.theoremBoundaryHeld

def observableSpectralWeight3320FinalBridge : ObservableSpectralWeightFinalBridge :=
  { finalPacket := finalTheoremPacket3320
    finalPacketIs3320 := by rfl
    spectralWeight := Plaquette.observableSpectralWeight3320Certificate
    spectralWeightReady := Plaquette.observable_spectral_weight_3320_certificate_ready
    finalPlaquetteMatchesWeight := by rfl
    finalGapMatchesWeightValue := by rfl
    finalMassValueIs3320 := by rfl
    finalEigenvalueIs3320 := by rfl
    finalPlaquettePositive := by rfl
    witnessSectorOrthogonal := by rfl
    witnessNotVacuum := by decide
    sectorCoreBridge := Spectral.spectral3320SectorSeparationCoreBridge
    sectorCoreBridgeReady := Spectral.spectral3320_sector_separation_core_bridge_ready
    finalBridgeVisible := True
    theoremBoundaryHeld := True }

theorem observable_spectral_weight_final_bridge_pack
    (B : ObservableSpectralWeightFinalBridge) :
    B.ready ↔ B.finalPacketIs3320 ∧ B.spectralWeightReady ∧
      B.finalPlaquetteMatchesWeight ∧ B.finalGapMatchesWeightValue ∧
      B.finalMassValueIs3320 ∧ B.finalEigenvalueIs3320 ∧ B.finalPlaquettePositive ∧
      B.witnessSectorOrthogonal ∧ B.witnessNotVacuum ∧ B.sectorCoreBridgeReady ∧
      B.finalBridgeVisible ∧ B.theoremBoundaryHeld := by
  rfl

theorem observable_spectral_weight_3320_final_bridge_ready :
    observableSpectralWeight3320FinalBridge.ready := by
  exact And.intro rfl <|
    And.intro Plaquette.observable_spectral_weight_3320_certificate_ready <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro (by decide) <|
    And.intro Spectral.spectral3320_sector_separation_core_bridge_ready <|
    And.intro True.intro True.intro

theorem observable_spectral_weight_3320_final_bridge_mass_value :
    observableSpectralWeight3320FinalBridge.finalPacket.massGap.value = 33 / 20 := by
  rfl

theorem observable_spectral_weight_3320_final_bridge_eigenvalue :
    observableSpectralWeight3320FinalBridge.finalPacket.eigenvector.eigenvalue = 33 / 20 := by
  rfl

theorem observable_spectral_weight_3320_final_bridge_positive_mass :
    observableSpectralWeight3320FinalBridge.finalPacket.plaquette.observableWitness.positiveMass = true := by
  rfl

theorem observable_spectral_weight_3320_final_bridge_weight_value :
    observableSpectralWeight3320FinalBridge.spectralWeight.massWitness.value = 33 / 20 := by
  rfl

theorem observable_spectral_weight_3320_final_bridge_witness_orthogonal :
    observableSpectralWeight3320FinalBridge.spectralWeight.sectorSeparation.witnessSector =
      Spectral.SpectralSector.orthogonal := by
  rfl

theorem observable_spectral_weight_3320_final_bridge_witness_not_vacuum :
    observableSpectralWeight3320FinalBridge.spectralWeight.sectorSeparation.witnessSector ≠
      Spectral.SpectralSector.vacuum := by
  decide

end Constructive
end MGAP4D
