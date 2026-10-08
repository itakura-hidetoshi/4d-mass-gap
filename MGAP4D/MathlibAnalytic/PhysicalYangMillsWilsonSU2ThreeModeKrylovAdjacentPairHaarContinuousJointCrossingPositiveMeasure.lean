import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarContinuousJointCrossingWitness
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-!
# P4: the genuine continuous Wilson-joint crossing obstruction has positive Haar measure

PR #5296 establishes that the ORIGINAL normalized positive-beta SU(2)
Wilson joint density has a canonical continuous representative
W_{beta,c}, equal to the original L2-based normalized density
pair-Haar almost everywhere. At explicit physical boundaries
A,B from PR #5295 its full two-by-two minor is strictly positive.

This file formally upgrades the finite point witness to a
NONEMPTY OPEN set of FOUR independent physical boundary
configurations on which the original continuous-version crossing
minor remains strictly positive.

Full-support normalized Haar on SU(2) and the pinned mathlib
IsOpenPosMeasure instances for finite dependent Haar products
and their ordinary binary products then prove that this strict-minor
open set has STRICTLY POSITIVE FOURFOLD SPATIAL HAAR MEASURE at
EVERY beta>0 and EVERY finite even spatial extent H.

This resolves the risk that the explicitly chosen strict crossing
witness is an isolated measure-zero anomaly of a representative:
the SAME strictly positive minor persists on a positive-measure
set for the authentic continuous Haar-a.e. version of the physical
Wilson joint density.

It does not yet prove that the original L2 quotient representative
has these values pointwise, nor convert the fourfold strict-minor
event into posterior retained-sigma-algebra nonmeasurability or a
positive-beta volume-uniform estimate. Those require an explicit
a.e. fourfold lifting/Fubini theorem and right-link descent.
No Dobrushin, alternate posterior law or continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4CrossPosMeasureTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4CrossPosMeasureCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4CrossPosMeasureSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4CrossPosMeasureMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4CrossPosMeasureBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4CrossPosMeasureSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p4CrossPosMeasureGroupHaarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance p4CrossPosMeasureSpatialHaarProbability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance p4CrossPosMeasureSpatialHaarOpenPos (H : ℕ) :
    Measure.IsOpenPosMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

/-- The original positive-beta physical Wilson JOINT normalized
density has a canonical continuous representative on the TRUE
product of the two spatial boundary spaces. -/
theorem originalWilsonContinuousPhysicalJointWeight_continuous
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Continuous (originalWilsonContinuousPhysicalJointWeight H beta hbeta) := by
  let ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H 2 (by norm_num) beta hbeta
  have hω : Continuous ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H 2 (by norm_num) beta hbeta
  have hK :
      Continuous (fun z :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H 2 beta z.1 z.2) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous H 2 beta
  change Continuous (fun z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖⁻¹ *
      ω z.1 *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 beta z.1 z.2 *
      ω z.2)
  exact (((continuous_const.mul (hω.comp continuous_fst)).mul hK).mul
    (hω.comp continuous_snd))

/-- Type of four INDEPENDENT physical boundary configurations,
organized as (A1,A2) and (B1,B2). -/
abbrev originalWilsonFourSpatialBoundaries (H : ℕ) : Type :=
  (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) ×
  (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)

/-- Every entry of the actual continuous-version Wilson joint
2x2 minor is continuous, hence so is their signed determinant
on the fourfold product of the same genuine boundary carrier. -/
theorem originalWilsonContinuousPhysicalJointTwoByTwoMinor_continuous
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Continuous (fun z : originalWilsonFourSpatialBoundaries H =>
      originalWilsonContinuousPhysicalJointTwoByTwoMinor
        H beta hbeta z.1.1 z.1.2 z.2.1 z.2.2) := by
  let W := originalWilsonContinuousPhysicalJointWeight H beta hbeta
  have hW : Continuous W :=
    originalWilsonContinuousPhysicalJointWeight_continuous H beta hbeta
  have hA1 :
      Continuous (fun z : originalWilsonFourSpatialBoundaries H => z.1.1) :=
    continuous_fst.comp continuous_fst
  have hA2 :
      Continuous (fun z : originalWilsonFourSpatialBoundaries H => z.1.2) :=
    continuous_snd.comp continuous_fst
  have hB1 :
      Continuous (fun z : originalWilsonFourSpatialBoundaries H => z.2.1) :=
    continuous_fst.comp continuous_snd
  have hB2 :
      Continuous (fun z : originalWilsonFourSpatialBoundaries H => z.2.2) :=
    continuous_snd.comp continuous_snd
  have h11 :
      Continuous (fun z : originalWilsonFourSpatialBoundaries H => W (z.1.1, z.2.1)) :=
    hW.comp (hA1.prodMk hB1)
  have h22 :
      Continuous (fun z : originalWilsonFourSpatialBoundaries H => W (z.1.2, z.2.2)) :=
    hW.comp (hA2.prodMk hB2)
  have h12 :
      Continuous (fun z : originalWilsonFourSpatialBoundaries H => W (z.1.1, z.2.2)) :=
    hW.comp (hA1.prodMk hB2)
  have h21 :
      Continuous (fun z : originalWilsonFourSpatialBoundaries H => W (z.1.2, z.2.1)) :=
    hW.comp (hA2.prodMk hB1)
  change Continuous (fun z : originalWilsonFourSpatialBoundaries H =>
    W (z.1.1,z.2.1) * W (z.1.2,z.2.2) -
    W (z.1.1,z.2.2) * W (z.1.2,z.2.1))
  exact (h11.mul h22).sub (h12.mul h21)

/-- The strictly positive original continuous-Wilson minor locus. -/
def originalWilsonContinuousPhysicalJointStrictMinorSet
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Set (originalWilsonFourSpatialBoundaries H) :=
  {z | 0 < originalWilsonContinuousPhysicalJointTwoByTwoMinor
    H beta hbeta z.1.1 z.1.2 z.2.1 z.2.2}

/-- The genuine continuous Wilson strict-minor locus is OPEN,
with no assumptions on the positive-coupling minor witness. -/
theorem originalWilsonContinuousPhysicalJointStrictMinorSet_isOpen
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsOpen (originalWilsonContinuousPhysicalJointStrictMinorSet H beta hbeta) := by
  exact isOpen_lt continuous_const
    (originalWilsonContinuousPhysicalJointTwoByTwoMinor_continuous H beta hbeta)

/-- Every beta>0 has a specific element of the strictly positive
continuous-Wilson minor locus, built from the actual SU(2) one-link
pi-rotation witness of PR #5295 and positive canonical vacuum of #5296. -/
theorem originalWilsonContinuousPhysicalJointStrictMinorSet_nonempty
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    (originalWilsonContinuousPhysicalJointStrictMinorSet
      H beta (le_of_lt hbeta)).Nonempty := by
  let A := originalWilsonExplicitIdentityBoundary H
  let B := originalWilsonExplicitRotatedBoundary H
  refine ⟨((A, B), (A, B)), ?_⟩
  exact originalWilsonContinuousPhysicalJoint_explicitMinor_pos H beta hbeta

/-- Actual fourfold normalized spatial Haar is full-support: every
nonempty open set of FOUR independent physical boundary configurations
has strictly positive measure. Inherited directly from mathlib's
IsOpenPosMeasure for normalized Haar, finite Pi and ordinary products. -/
theorem originalWilsonContinuousPhysicalJointStrictMinorSet_positiveHaarMeasure
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    0 <
      (((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).prod
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)).prod
        ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).prod
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)))
          (originalWilsonContinuousPhysicalJointStrictMinorSet
            H beta (le_of_lt hbeta)) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  haveI hQuad : Measure.IsOpenPosMeasure ((μ.prod μ).prod (μ.prod μ)) := by
    dsimp [μ]
    infer_instance
  exact
    (originalWilsonContinuousPhysicalJointStrictMinorSet_isOpen
      H beta (le_of_lt hbeta)).measure_pos
        ((μ.prod μ).prod (μ.prod μ))
        (originalWilsonContinuousPhysicalJointStrictMinorSet_nonempty H beta hbeta)

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
