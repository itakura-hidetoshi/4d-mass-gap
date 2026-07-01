import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeEmbedding

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

noncomputable def PhysicalFourDimensionalYangMillsLatticeEmbedding.reindex
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (subsequence : ℕ → ℕ)
    (hSubsequence : StrictMono subsequence) :
    PhysicalFourDimensionalYangMillsLatticeEmbedding :=
  { PhysicalConfiguration := E.PhysicalConfiguration
    LatticeConfiguration := fun n => E.LatticeConfiguration (subsequence n)
    latticeMeasure := fun n => E.latticeMeasure (subsequence n)
    interpolate := fun n => E.interpolate (subsequence n)
    interpolate_measurable := fun n => E.interpolate_measurable (subsequence n)
    latticeSpacing := fun n => E.latticeSpacing (subsequence n)
    latticeSpacing_pos := fun n => E.latticeSpacing_pos (subsequence n)
    latticeSpacing_tendsto_zero :=
      E.latticeSpacing_tendsto_zero.comp hSubsequence.tendsto_atTop
    physicalVolume := fun n => E.physicalVolume (subsequence n)
    physicalVolume_tendsto_atTop :=
      E.physicalVolume_tendsto_atTop.comp hSubsequence.tendsto_atTop }

@[simp] theorem PhysicalFourDimensionalYangMillsLatticeEmbedding.reindex_latticeMeasure
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (subsequence : ℕ → ℕ)
    (hSubsequence : StrictMono subsequence)
    (n : ℕ) :
    (E.reindex subsequence hSubsequence).latticeMeasure n =
      E.latticeMeasure (subsequence n) := rfl

@[simp] theorem PhysicalFourDimensionalYangMillsLatticeEmbedding.reindex_interpolate
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (subsequence : ℕ → ℕ)
    (hSubsequence : StrictMono subsequence)
    (n : ℕ) :
    (E.reindex subsequence hSubsequence).interpolate n =
      E.interpolate (subsequence n) := rfl

@[simp] theorem PhysicalFourDimensionalYangMillsLatticeEmbedding.reindex_embeddedMeasure
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (subsequence : ℕ → ℕ)
    (hSubsequence : StrictMono subsequence)
    (n : ℕ) :
    (E.reindex subsequence hSubsequence).embeddedMeasure n =
      E.embeddedMeasure (subsequence n) := rfl

@[simp] theorem PhysicalFourDimensionalYangMillsLatticeEmbedding.reindex_latticeSpacing
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (subsequence : ℕ → ℕ)
    (hSubsequence : StrictMono subsequence)
    (n : ℕ) :
    (E.reindex subsequence hSubsequence).latticeSpacing n =
      E.latticeSpacing (subsequence n) := rfl

@[simp] theorem PhysicalFourDimensionalYangMillsLatticeEmbedding.reindex_physicalVolume
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (subsequence : ℕ → ℕ)
    (hSubsequence : StrictMono subsequence)
    (n : ℕ) :
    (E.reindex subsequence hSubsequence).physicalVolume n =
      E.physicalVolume (subsequence n) := rfl

end

end MathlibAnalytic
end MGAP4D
