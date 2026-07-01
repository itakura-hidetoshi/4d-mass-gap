import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryContinuumLawNondegeneracy
import MGAP4D.MathlibAnalytic.PhysicalYangMillsProkhorovLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Because the canonical binary carrier is compact, every family of embedded
periodic `Z₂` plaquette laws is automatically tight. -/
theorem Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.embeddedMeasure_isTight
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    D.toPhysicalEmbedding.toLatticeEmbedding.IsTight := by
  letI : CompactSpace
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration := by
    change CompactSpace Bool
    infer_instance
  exact MeasureTheory.IsTightMeasureSet.of_compactSpace

/-- Prokhorov compactness therefore extracts a weakly convergent subsequence of
the canonical binary plaquette laws without any separately supplied tightness
or weak-convergence hypothesis. -/
theorem Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovSubsequence_exists
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    Nonempty
      (PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
        D.toPhysicalEmbedding.toLatticeEmbedding) :=
  physical_yang_mills_prokhorov_subsequence_exists
    D.toPhysicalEmbedding.toLatticeEmbedding D.embeddedMeasure_isTight

/-- A canonical noncomputable choice of a convergent binary-law subsequence. -/
noncomputable def
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovSubsequenceLimit
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      D.toPhysicalEmbedding.toLatticeEmbedding :=
  D.prokhorovSubsequence_exists.some

/-- The chosen extraction indices are strictly increasing. -/
theorem Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovSubsequence_strictMono
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    StrictMono D.prokhorovSubsequenceLimit.subsequence :=
  D.prokhorovSubsequenceLimit.subsequence_strictMono

/-- The embedded binary plaquette laws converge weakly along the chosen
Prokhorov subsequence. -/
theorem Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovSubsequence_weakConvergence
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure
        (D.prokhorovSubsequenceLimit.subsequence n))
      atTop
      (nhds D.prokhorovSubsequenceLimit.continuumMeasure) :=
  D.prokhorovSubsequenceLimit.weakConvergence

/-- The compact binary extraction supplies an actual physical weak-limit
carrier along the selected scaling subsequence. -/
noncomputable def
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovWeakLimit
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  D.prokhorovSubsequenceLimit.toWeakLimit

end

end MathlibAnalytic
end MGAP4D
