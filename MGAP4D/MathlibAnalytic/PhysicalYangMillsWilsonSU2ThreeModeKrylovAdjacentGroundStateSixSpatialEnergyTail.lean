import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGroundStateJointConditionalTail
import Mathlib.Tactic

/-!
# Reduce the adjacent SU(2) raw joint tail to six-spatial residual energy

PR #5137 moves the raw adjacent-Krylov reconstruction tail to the genuine
fine ground-state joint L² carrier, but still permits an arbitrary bounded
joint operator as the candidate.

The genuine Wilson joint law already carries six concrete spatial conditional
expectations.  This file selects one of those six operators at every scale and
dominates its squared residual by six times the normalized six-color residual
energy.  The factor six is exact finite-family bookkeeping:

  ||x - P_c x||² ≤ Σ_d ||x - P_d x||²
                 = 6 * E₆(x).

Thus the raw analytic input is reduced from an arbitrary operator-valued tail
to a single nonnegative scalar six-spatial residual-energy tail on the genuine
ground-state joint law.

The common-marginal physicality defect is deliberately unchanged.  No
conditional expectation is identified with the physical transfer operator,
and no H1-D5 exact descent is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentSixSpatialEnergyTailTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentSixSpatialEnergyTailCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentSixSpatialEnergyTailSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentSixSpatialEnergyTailMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentSixSpatialEnergyTailBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentSixSpatialEnergyTailSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentSixSpatialEnergyTailNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private theorem su2AdjacentSixSpatialEnergyTail_two_pos : 0 < (2 : ℕ) := by
  norm_num

/-- One member of a six-operator family has squared residual no larger than
six times the normalized residual energy of the whole family. -/
theorem finSix_single_residual_sq_le_six_mul_normalizedResidualEnergy
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : Fin 6 → E →L[ℝ] E)
    (x : E)
    (c : Fin 6) :
    ‖x - P c x‖ ^ 2 ≤
      6 * groundStateJointColorNormalizedResidualEnergy P x := by
  have hterm :
      ‖x - P c x‖ ^ 2 ≤
        ∑ d : Fin 6, ‖x - P d x‖ ^ 2 := by
    exact
      Finset.single_le_sum
        (fun d _hd => sq_nonneg ‖x - P d x‖)
        (Finset.mem_univ c)
  calc
    ‖x - P c x‖ ^ 2 ≤
        ∑ d : Fin 6, ‖x - P d x‖ ^ 2 := hterm
    _ = 6 * groundStateJointColorNormalizedResidualEnergy P x := by
      unfold groundStateJointColorNormalizedResidualEnergy
      have hcard : (Fintype.card (Fin 6) : ℝ) = 6 := by
        norm_num
      rw [hcard]
      ring

section GroundStateSixSpatialEnergyTail

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)

/-- Select one of the six genuine fine-scale ground-state spatial conditional
expectations at every scale. -/
noncomputable def physicalYangMillsSU2AdjacentFineGroundStateSixSpatialCandidate
    (selectedColor : ℕ → Fin 6)
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        (halfExtent (n + 1)) 2 su2AdjacentSixSpatialEnergyTail_two_pos
        (beta n) (hbeta n) →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        (halfExtent (n + 1)) 2 su2AdjacentSixSpatialEnergyTail_two_pos
        (beta n) (hbeta n) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
    (halfExtent (n + 1)) 2 su2AdjacentSixSpatialEnergyTail_two_pos
    (beta n) (hbeta n) (selectedColor n)

/-- The normalized six-spatial residual energy of the actual fine frozen
Krylov vector on the genuine ground-state joint carrier. -/
noncomputable def physicalYangMillsSU2AdjacentFineGroundStateSixSpatialResidualEnergy
    (n r : ℕ)
    (k : Fin 3) : ℝ :=
  groundStateJointColorNormalizedResidualEnergy
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
      (halfExtent (n + 1)) 2 su2AdjacentSixSpatialEnergyTail_two_pos
      (beta n) (hbeta n))
    (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k)

/-- The selected concrete six-spatial conditional-expectation residual is
bounded by six times the normalized six-spatial residual energy. -/
theorem physicalYangMillsSU2AdjacentFineGroundStateSixSpatialCandidate_residual_sq_le
    (selectedColor : ℕ → Fin 6)
    (n r : ℕ)
    (k : Fin 3) :
    ‖physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k -
        physicalYangMillsSU2AdjacentFineGroundStateSixSpatialCandidate
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          selectedColor n
          (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k)‖ ^ 2 ≤
      6 *
        physicalYangMillsSU2AdjacentFineGroundStateSixSpatialResidualEnergy
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k := by
  exact
    finSix_single_residual_sq_le_six_mul_normalizedResidualEnergy
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
        (halfExtent (n + 1)) 2 su2AdjacentSixSpatialEnergyTail_two_pos
        (beta n) (hbeta n))
      (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k)
      (selectedColor n)

/-- The selected six-spatial joint candidate transported exactly to the
ordered pair-Haar carrier used by the adjacent reconstruction receiver. -/
noncomputable def physicalYangMillsSU2AdjacentFineGroundStateSixSpatialCandidatePairHaar
    (selectedColor : ℕ → Fin 6)
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent (n + 1)) 2 →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent (n + 1)) 2 :=
  physicalYangMillsSU2AdjacentFineGroundStateJointCandidatePairHaar
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n
    (physicalYangMillsSU2AdjacentFineGroundStateSixSpatialCandidate
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      selectedColor n)

/-- Model-facing adjacent tail input with the raw term reduced to the scalar
normalized six-spatial residual energy.

The physicality term is still the genuine cross-scale distance of the
transported selected-color candidate from the coarse completed physical-pair
range. -/
structure PhysicalYangMillsSU2AdjacentGroundStateSixSpatialEnergyPhysicalityTailInput where
  selectedColor : ℕ → Fin 6
  splitEnergyPhysicality_tail :
    ∀ (r : ℕ) (k : Fin 3),
      ∃ (Cenergy Cphys rho : ℝ) (distance : ℕ → ℕ),
        0 ≤ Cenergy ∧
        0 ≤ Cphys ∧
        0 ≤ rho ∧
        rho < 1 ∧
        (∀ n, n ≤ distance n) ∧
        (∀ n,
          physicalYangMillsSU2AdjacentFineGroundStateSixSpatialResidualEnergy
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r k ≤
            Cenergy * (rho ^ distance n / (1 - rho))) ∧
        ∀ n,
          let pairCandidate :=
            physicalYangMillsSU2AdjacentFineGroundStateSixSpatialCandidatePairHaar
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              selectedColor n
          let Cn :=
            physicalYangMillsSU2AdjacentCommonPairHaarCandidate
              Q R n pairCandidate
          let Y :=
            physicalYangMillsSU2AdjacentCommonFineFrozenStepVector
              Q R n r k
          ‖Cn Y -
              physicalYangMillsSU2AdjacentCommonLeftPhysicalRangeProjection
                Q R n (Cn Y)‖ ^ 2 ≤
            Cphys * (rho ^ distance n / (1 - rho))

namespace PhysicalYangMillsSU2AdjacentGroundStateSixSpatialEnergyPhysicalityTailInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentGroundStateSixSpatialEnergyPhysicalityTailInput
        (Q := Q) (R := R))

include G

/-- A geometric tail for the normalized six-spatial energy yields the #5137
joint-operator tail with raw constant multiplied only by the exact color count
six. -/
noncomputable def toGroundStateJointConditionalPhysicalityTailInput :
    PhysicalYangMillsSU2AdjacentGroundStateJointConditionalPhysicalityTailInput
      (Q := Q) (R := R) where
  candidate := fun n =>
    physicalYangMillsSU2AdjacentFineGroundStateSixSpatialCandidate
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      G.selectedColor n
  splitResidual_tail := by
    intro r k
    rcases G.splitEnergyPhysicality_tail r k with
      ⟨Cenergy, Cphys, rho, distance,
        hCenergy, hCphys, hrho0, hrho1, hDistance, hEnergy, hPhys⟩
    refine
      ⟨6 * Cenergy, Cphys, rho, distance,
        by positivity, hCphys, hrho0, hrho1, hDistance, ?_, ?_⟩
    · intro n
      calc
        ‖physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r k -
            physicalYangMillsSU2AdjacentFineGroundStateSixSpatialCandidate
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              G.selectedColor n
              (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n r k)‖ ^ 2 ≤
            6 *
              physicalYangMillsSU2AdjacentFineGroundStateSixSpatialResidualEnergy
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n r k :=
          physicalYangMillsSU2AdjacentFineGroundStateSixSpatialCandidate_residual_sq_le
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            G.selectedColor n r k
        _ ≤ 6 * (Cenergy * (rho ^ distance n / (1 - rho))) := by
          exact mul_le_mul_of_nonneg_left (hEnergy n) (by norm_num)
        _ = (6 * Cenergy) * (rho ^ distance n / (1 - rho)) := by
          ring
    · intro n
      simpa [
        physicalYangMillsSU2AdjacentFineGroundStateSixSpatialCandidatePairHaar
      ] using hPhys n

/-- The six-spatial energy formulation inherits the total reconstruction
variance geometric tail. -/
theorem totalVariance_tail
    (r : ℕ)
    (k : Fin 3) :
    ∃ (C rho : ℝ) (distance : ℕ → ℕ),
      0 ≤ C ∧
      0 ≤ rho ∧
      rho < 1 ∧
      (∀ n, n ≤ distance n) ∧
      ∀ n,
        physicalYangMillsSU2AdjacentFiniteTotalReconstructionVarianceDefect
            Q R n r k ≤
          C * (rho ^ distance n / (1 - rho)) := by
  exact
    PhysicalYangMillsSU2AdjacentGroundStateJointConditionalPhysicalityTailInput.totalVariance_tail
      Q R
      (toGroundStateJointConditionalPhysicalityTailInput Q R G)
      r k

/-- The six-spatial energy formulation inherits adjacent orbit-mismatch
summability once the still-separate physical-commutation and coupling-majorant
geometric tails are supplied. -/
theorem orbitMismatch_summable
    (physicalCommutation_geometric :
      ∀ (r : ℕ) (k : Fin 3),
        ∃ C q : ℝ,
          0 ≤ q ∧ q < 1 ∧
            ∀ n : ℕ,
              physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
                  Q R n r k ≤
                C * q ^ n)
    (betaMajorant_geometric :
      ∃ C q : ℝ,
        0 ≤ q ∧ q < 1 ∧
          ∀ n : ℕ,
            physicalYangMillsSU2AdjacentCouplingBetaMajorant
                halfExtent beta n ≤
              C * q ^ n)
    (r : ℕ)
    (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
          Q R n r k) := by
  exact
    PhysicalYangMillsSU2AdjacentGroundStateJointConditionalPhysicalityTailInput.orbitMismatch_summable
      Q R
      (toGroundStateJointConditionalPhysicalityTailInput Q R G)
      physicalCommutation_geometric betaMajorant_geometric r k

end PhysicalYangMillsSU2AdjacentGroundStateSixSpatialEnergyPhysicalityTailInput

end GroundStateSixSpatialEnergyTail

end

end MathlibAnalytic
end MGAP4D
