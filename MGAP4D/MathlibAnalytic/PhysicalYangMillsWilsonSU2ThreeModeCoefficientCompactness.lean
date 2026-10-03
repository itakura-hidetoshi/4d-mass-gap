import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeExactNonTopExcitation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Compactness of the exact SU(2) three-mode coefficient sequence

The previous theorem file constructs, at every finite scale, at least one unit
coefficient in EuclideanSpace R (Fin 3) whose synthesized physical pair is
simultaneously orthogonal to the actual finite OS vacuum and to the physical
pair-top direction.

This file makes one such coefficient choice at each scale and then applies
finite-dimensional compactness to obtain a strictly increasing subsequence
converging to a unit coefficient vector.

The chosen synthesized excitation keeps all of the exact finite-scale
properties from the existence theorem: unit norm, physical-pair membership,
exact vacuum centering, exact pair-non-top membership, and the existing
uniform q0^m transfer estimate.

No H1-D5 compatibility, vacuum/top alignment, or top-direction convergence is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open Filter
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2ThreeModeCompactnessTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2ThreeModeCompactnessCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2ThreeModeCompactnessSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2ThreeModeCompactnessMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2ThreeModeCompactnessBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2ThreeModeCompactnessSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2ThreeModeCompactnessSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance su2ThreeModeCompactnessNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Bolzano--Weierstrass on the unit sphere of R^3, stated in the exact form
needed for the three-mode coefficient sequence. -/
theorem euclideanFinThree_unit_sequence_exists_strictMono_tendsto
    (c : ℕ → EuclideanSpace ℝ (Fin 3))
    (hc : ∀ n, ‖c n‖ = 1) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ cInf : EuclideanSpace ℝ (Fin 3),
        ‖cInf‖ = 1 ∧
        Tendsto (c ∘ phi) atTop (𝓝 cInf) := by
  letI : ProperSpace (EuclideanSpace ℝ (Fin 3)) :=
    FiniteDimensional.proper ℝ (EuclideanSpace ℝ (Fin 3))
  have hmem :
      ∀ n, c n ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro n
    rw [Metric.mem_sphere, dist_zero_right, hc n]
  obtain ⟨cInf, hcInfSphere, phi, hphi, hTendsto⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).isSeqCompact hmem
  refine ⟨phi, hphi, cInf, ?_, hTendsto⟩
  simpa only [Metric.mem_sphere, dist_zero_right] using hcInfSphere

section FiniteScale

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {h2 : 0 < (2 : ℕ)}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 h2 beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))

/-- A fixed theorem-generated unit coefficient at every finite scale. -/
noncomputable def
    physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
    (n : ℕ) :
    EuclideanSpace ℝ (Fin 3) :=
  Classical.choose
    (physicalYangMillsVacuumNormalizedSU2_exists_unit_threeModeExactPhysicalNonTopExcitation
      Q hInvariant n)

/-- The complete finite-scale specification of the chosen coefficient. -/
theorem physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice_spec
    (n : ℕ) :
    ‖physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
        Q hInvariant n‖ = 1 ∧
    ‖periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
        (halfExtent n)
        (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
          Q hInvariant n)‖ = 1 ∧
    inner ℝ
        (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := 2) (hN := h2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
          (halfExtent n)
          (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
            Q hInvariant n)) = 0 ∧
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
          (halfExtent n) 2 h2 (beta n) (hbeta n))
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
          (halfExtent n)
          (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
            Q hInvariant n)) = 0 ∧
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
        (halfExtent n)
        (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
          Q hInvariant n) ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) 2 ∧
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
        (halfExtent n)
        (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
          Q hInvariant n) ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure
        (halfExtent n) 2 h2 (beta n) (hbeta n) ∧
    finiteVacuumCentered
        (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := 2) (hN := h2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
          (halfExtent n)
          (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
            Q hInvariant n)) =
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
        (halfExtent n)
        (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
          Q hInvariant n) := by
  exact
    Classical.choose_spec
      (physicalYangMillsVacuumNormalizedSU2_exists_unit_threeModeExactPhysicalNonTopExcitation
        Q hInvariant n)

@[simp]
theorem physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice_norm
    (n : ℕ) :
    ‖physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
        Q hInvariant n‖ = 1 :=
  (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice_spec
    Q hInvariant n).1

/-- The selected finite excitation itself. -/
noncomputable def
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) 2 :=
  periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
    (halfExtent n)
    (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
      Q hInvariant n)

@[simp]
theorem physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_norm
    (n : ℕ) :
    ‖physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
        Q hInvariant n‖ = 1 := by
  exact
    (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice_spec
      Q hInvariant n).2.1

theorem physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_vacuum_orthogonal
    (n : ℕ) :
    inner ℝ
        (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := 2) (hN := h2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
        (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
          Q hInvariant n) = 0 := by
  exact
    (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice_spec
      Q hInvariant n).2.2.1

theorem physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_pairTop_orthogonal
    (n : ℕ) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
          (halfExtent n) 2 h2 (beta n) (hbeta n))
        (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
          Q hInvariant n) = 0 := by
  exact
    (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice_spec
      Q hInvariant n).2.2.2.1

theorem physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_mem_physicalPairCarrier
    (n : ℕ) :
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
        Q hInvariant n ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) 2 := by
  exact
    (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice_spec
      Q hInvariant n).2.2.2.2.1

theorem physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_mem_nonTop
    (n : ℕ) :
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
        Q hInvariant n ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure
        (halfExtent n) 2 h2 (beta n) (hbeta n) := by
  exact
    (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice_spec
      Q hInvariant n).2.2.2.2.2.1

theorem physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_centered
    (n : ℕ) :
    finiteVacuumCentered
        (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := 2) (hN := h2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
        (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
          Q hInvariant n) =
      physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
        Q hInvariant n := by
  exact
    (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice_spec
      Q hInvariant n).2.2.2.2.2.2

/-- The chosen coefficient sequence has a strictly increasing subsequence
converging strongly in R^3 to another unit coefficient. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice_exists_strictMono_tendsto
    :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ cInf : EuclideanSpace ℝ (Fin 3),
        ‖cInf‖ = 1 ∧
        Tendsto
          (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
            Q hInvariant ∘ phi)
          atTop
          (𝓝 cInf) := by
  exact
    euclideanFinThree_unit_sequence_exists_strictMono_tendsto
      (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
        Q hInvariant)
      (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice_norm
        Q hInvariant)

/-- The selected exact finite excitation keeps the already-proved uniform
full-pair non-top contraction estimate. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_pow_norm_le_uniform_q0
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n m : ℕ) :
    ‖(periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) 2 h2 (beta n) (hbeta n) ^ m)
        (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
          Q hInvariant n)‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  have hdecay :=
    periodicHypercubicEvenSpecialUnitary_uniformPhysicalPairNonTopBlockClosure_normalizedTransfer_pow_norm_le
      halfExtent 2 h2 beta hbeta s hs hcut n m
      (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
        Q hInvariant n)
      (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_mem_nonTop
        Q hInvariant n)
  simpa only [
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_norm,
    mul_one
  ] using hdecay

end FiniteScale

end

end MathlibAnalytic
end MGAP4D
