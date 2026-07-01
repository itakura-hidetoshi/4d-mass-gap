import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryPlaquetteEmbedding
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Sequences

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- The exact binary probability law of the selected plaquette energy at one
scale. -/
noncomputable def
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.binaryLaw
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (k : ℕ) : ProbabilityMeasure Bool :=
  D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure k

/-- A convergent subsequence of the canonical binary plaquette-energy laws. -/
structure Z2PeriodicHypercubicBinaryPlaquetteSubsequenceLimit
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  continuumMeasure : ProbabilityMeasure Bool
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  weakConvergence :
    Tendsto (fun k => D.binaryLaw (subsequence k)) atTop
      (nhds continuumMeasure)

/-- Repackage a convergent binary-law subsequence as a physical weak-limit
carrier.  Its lattice spacing and physical volume are reindexed by the same
strictly increasing subsequence. -/
noncomputable def
    Z2PeriodicHypercubicBinaryPlaquetteSubsequenceLimit.toWeakLimit
    {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}
    (L : Z2PeriodicHypercubicBinaryPlaquetteSubsequenceLimit D) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  { Configuration := Bool
    approximatingMeasure := fun k => D.binaryLaw (L.subsequence k)
    continuumMeasure := L.continuumMeasure
    weakConvergence := L.weakConvergence
    latticeSpacing := fun k => D.latticeSpacing (L.subsequence k)
    latticeSpacing_pos := fun k => D.latticeSpacing_pos (L.subsequence k)
    latticeSpacing_tendsto_zero :=
      D.latticeSpacing_tendsto_zero.comp
        L.subsequence_strictMono.tendsto_atTop
    physicalVolume := fun k => D.physicalVolume (L.subsequence k)
    physicalVolume_tendsto_atTop :=
      D.physicalVolume_tendsto_atTop.comp
        L.subsequence_strictMono.tendsto_atTop }

/-- The approximating variance on a binary-law subsequence is the original
finite periodic plaquette Gibbs variance at the selected scale. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteSubsequenceLimit.approximating_variance_eq
    {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}
    (L : Z2PeriodicHypercubicBinaryPlaquetteSubsequenceLimit D)
    (k : ℕ) :
    L.toWeakLimit.approximatingObservableVariance k
        z2BinaryPlaquetteObservable =
      D.trajectory.gibbsVariance (L.subsequence k) := by
  unfold Z2PeriodicHypercubicBinaryPlaquetteSubsequenceLimit.toWeakLimit
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.binaryLaw
    PhysicalFourDimensionalYangMillsWeakLimit.approximatingObservableVariance
  change
    (∫ b, (z2BinaryPlaquetteObservable * z2BinaryPlaquetteObservable) b
        ∂(D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure
          (L.subsequence k) : Measure Bool)) -
        (∫ b, z2BinaryPlaquetteObservable b
          ∂(D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure
            (L.subsequence k) : Measure Bool)) ^ 2 =
      D.trajectory.gibbsVariance (L.subsequence k)
  rw [physical_yang_mills_latticeEmbedding_embeddedMeasure_variance_eq_pullback]
  exact D.toPhysicalEmbedding.latticePullbackVariance_eq (L.subsequence k)

/-- Every convergent subsequence of the bounded-coupling binary plaquette laws
carries the same explicit positive observable-variance certificate. -/
noncomputable def
    Z2PeriodicHypercubicBinaryPlaquetteSubsequenceLimit.toObservableNontrivialityCertificate
    {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}
    (L : Z2PeriodicHypercubicBinaryPlaquetteSubsequenceLimit D) :
    L.toWeakLimit.ObservableNontrivialityCertificate :=
  { observable := z2BinaryPlaquetteObservable
    lowerBound := Real.exp (-(6 * D.betaUpper)) / 8
    lowerBound_pos :=
      z2PeriodicHypercubic_boundedCoupling_varianceLower_pos D.betaUpper
    approximating_variance_ge := by
      intro k
      rw [L.approximating_variance_eq k]
      exact D.trajectory.uniform_gibbsVariance_lower_of_beta_le
        D.betaUpper D.beta_le (L.subsequence k) }

/-- A convergent binary-law subsequence has strictly positive limiting
plaquette-observable variance. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteSubsequenceLimit.continuum_variance_pos
    {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}
    (L : Z2PeriodicHypercubicBinaryPlaquetteSubsequenceLimit D) :
    0 < L.toWeakLimit.continuumObservableVariance
      z2BinaryPlaquetteObservable :=
  L.toObservableNontrivialityCertificate.continuum_variance_pos

/-- Compactness of probability measures on the finite binary carrier produces
a convergent subsequence of every binary plaquette-energy law sequence. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.exists_subsequenceLimit
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    Nonempty (Z2PeriodicHypercubicBinaryPlaquetteSubsequenceLimit D) := by
  obtain ⟨μ, φ, hφ, hWeak⟩ := CompactSpace.tendsto_subseq D.binaryLaw
  exact ⟨{
    continuumMeasure := μ
    subsequence := φ
    subsequence_strictMono := hφ
    weakConvergence := hWeak }⟩

/-- Therefore every bounded-coupling periodic `Z₂` trajectory has at least one
subsequential binary plaquette-energy limit with strictly positive variance. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.exists_subsequence_continuum_variance_pos
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    ∃ L : Z2PeriodicHypercubicBinaryPlaquetteSubsequenceLimit D,
      0 < L.toWeakLimit.continuumObservableVariance
        z2BinaryPlaquetteObservable := by
  rcases D.exists_subsequenceLimit with ⟨L⟩
  exact ⟨L, L.continuum_variance_pos⟩

end

end MathlibAnalytic
end MGAP4D
