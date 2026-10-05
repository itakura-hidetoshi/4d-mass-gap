import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGroundStateSweepStageProfileCoreMajorantTail
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageProfileBoundedContinuousCoreClosure
import Mathlib.Tactic

/-!
# Adjacent SU(2) sweep-stage tail from bounded-continuous oscillation majorants

PR #5147 puts the native Dobrushin/Feller carrier directly on the genuine
ground-state joint L2 space: bounded-continuous joint observables have dense
canonical representatives, and a continuous scalar majorant proved for every
such representative extends to every joint-L2 vector.

This file installs that closure at the actual adjacent SU(2) frozen-Krylov
scale.  The pointwise oscillation profile remains entirely on bounded
continuous observables.  No L2-continuity of the oscillation profile and no
bounded-concrete representative of the actual frozen vector are required.

Thus the remaining locality input can be stated in the form naturally
delivered by the existing finite-volume Wilson Dobrushin/Feller machinery:

* for every bounded-continuous joint observable, construct stagewise
  nonnegative target-link oscillation bounds;
* bound their normalized squared energy by one continuous scalar majorant;
* prove the scalar majorant has the desired geometric support-distance tail at
  the actual frozen Krylov vector.

The common-marginal physicality defect, physical-commutation tail, and
beta-majorant tail remain separate.  Heat-bath update count is not identified
with Euclidean time, no transfer/conditional-expectation identification is
introduced, and no H1-D5 exact descent is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentBCFOscillationMajorantTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentBCFOscillationMajorantCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentBCFOscillationMajorantSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentBCFOscillationMajorantMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentBCFOscillationMajorantBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentBCFOscillationMajorantSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentBCFOscillationMajorantNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private theorem su2AdjacentBCFOscillationMajorant_two_pos : 0 < (2 : ℕ) := by
  norm_num

section AdjacentBCFOscillationMajorant

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

/-- Model-facing adjacent input whose locality proof stays on the native
bounded-continuous joint-observable carrier and is closed to the actual frozen
joint-L2 vector only through PR #5147. -/
structure PhysicalYangMillsSU2AdjacentGroundStateSweepStageBCFOscillationEnergyMajorantPhysicalityTailInput where
  selectedColor : ℕ → Fin 6
  s : ℝ
  hs : 8 < s
  eta : ℝ
  eta_nonneg : 0 ≤ eta
  eta_lt_one : eta < 1
  beta_le_cutoff :
    ∀ n,
      beta n ≤
        GroundStateSourceFixedPairEnergy.jointLeakageLossContractionCutoff s hs
  lossRatio_le_eta :
    ∀ n,
      GroundStateSourceFixedPairEnergy.jointLeakageLossRatio s (beta n) ≤ eta
  majorant :
    ∀ n,
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          (halfExtent (n + 1)) 2 su2AdjacentBCFOscillationMajorant_two_pos
          (beta n) (hbeta n) → ℝ
  majorant_continuous :
    ∀ n, Continuous (majorant n)
  boundedContinuous_oscillationEnergy_le_majorant :
    ∀ n
      (O :
        PeriodicHypercubicEvenSpecialUnitaryGroundStateJointBCF
          (halfExtent (n + 1)) 2),
      ∃ delta :
          PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)) → ℝ,
        (∀ e, 0 ≤ delta e) ∧
        PeriodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageConcreteOscillationProfileBoundedBy
          (halfExtent (n + 1)) 2
          su2AdjacentBCFOscillationMajorant_two_pos
          (beta n) (hbeta n)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
            (halfExtent (n + 1)) 2
            su2AdjacentBCFOscillationMajorant_two_pos
            (beta n) (hbeta n) O)
          delta ∧
        periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy
            (halfExtent (n + 1)) delta ≤
          majorant n
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
              (halfExtent (n + 1)) 2
              su2AdjacentBCFOscillationMajorant_two_pos
              (beta n) (hbeta n) O)
  splitMajorantPhysicality_tail :
    ∀ (r : ℕ) (k : Fin 3),
      ∃ (Cmajor Cphys rho : ℝ) (distance : ℕ → ℕ),
        0 ≤ Cmajor ∧
        0 ≤ Cphys ∧
        0 ≤ rho ∧
        rho < 1 ∧
        (∀ n, n ≤ distance n) ∧
        (∀ n,
          majorant n
              (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n r k) ≤
            Cmajor * (rho ^ distance n / (1 - rho))) ∧
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

namespace PhysicalYangMillsSU2AdjacentGroundStateSweepStageBCFOscillationEnergyMajorantPhysicalityTailInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentGroundStateSweepStageBCFOscillationEnergyMajorantPhysicalityTailInput
        (Q := Q) (R := R))

include G

/-- PR #5147 closes the bounded-continuous stagewise oscillation estimate
directly to the actual frozen joint-L2 vector, producing the #5140 exact
profile-tail receiver without coefficient loss. -/
noncomputable def toGroundStateSweepStageProfilePhysicalityTailInput :
    PhysicalYangMillsSU2AdjacentGroundStateSweepStageProfilePhysicalityTailInput
      (Q := Q) (R := R) where
  selectedColor := G.selectedColor
  s := G.s
  hs := G.hs
  eta := G.eta
  eta_nonneg := G.eta_nonneg
  eta_lt_one := G.eta_lt_one
  beta_le_cutoff := G.beta_le_cutoff
  lossRatio_le_eta := G.lossRatio_le_eta
  splitProfilePhysicality_tail := by
    intro r k
    rcases G.splitMajorantPhysicality_tail r k with
      ⟨Cmajor, Cphys, rho, distance,
        hCmajor, hCphys, hrho0, hrho1, hDistance, hMajorTail, hPhys⟩
    refine
      ⟨Cmajor, Cphys, rho, distance,
        hCmajor, hCphys, hrho0, hrho1, hDistance, ?_, hPhys⟩
    intro n
    rw [
      physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_generalProfileEnergy
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k]
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy_le_of_boundedContinuous_oscillationEnergyMajorant
        (halfExtent (n + 1)) 2
        su2AdjacentBCFOscillationMajorant_two_pos
        (beta n) (hbeta n)
        (G.majorant n)
        (G.majorant_continuous n)
        (G.boundedContinuous_oscillationEnergy_le_majorant n)
        (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k)).trans
        (hMajorTail n)

/-- The BCF-native locality formulation yields the actual adjacent sweep-stage
profile geometric tail. -/
theorem profile_tail
    (r : ℕ)
    (k : Fin 3) :
    ∃ (C rho : ℝ) (distance : ℕ → ℕ),
      0 ≤ C ∧
      0 ≤ rho ∧
      rho < 1 ∧
      (∀ n, n ≤ distance n) ∧
      ∀ n,
        physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k ≤
          C * (rho ^ distance n / (1 - rho)) := by
  have Hprofile :=
    toGroundStateSweepStageProfilePhysicalityTailInput Q R G
  rcases Hprofile.splitProfilePhysicality_tail r k with
    ⟨Cprofile, Cphys, rho, distance,
      hCprofile, hCphys, hrho0, hrho1, hDistance, hProfile, hPhys⟩
  exact
    ⟨Cprofile, rho, distance,
      hCprofile, hrho0, hrho1, hDistance, hProfile⟩

/-- The BCF-native locality formulation inherits the total
reconstruction-variance geometric tail. -/
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
    PhysicalYangMillsSU2AdjacentGroundStateSweepStageProfilePhysicalityTailInput.totalVariance_tail
      Q R
      (toGroundStateSweepStageProfilePhysicalityTailInput Q R G)
      r k

/-- The BCF-native locality formulation inherits adjacent orbit-mismatch
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
    PhysicalYangMillsSU2AdjacentGroundStateSweepStageProfilePhysicalityTailInput.orbitMismatch_summable
      Q R
      (toGroundStateSweepStageProfilePhysicalityTailInput Q R G)
      physicalCommutation_geometric betaMajorant_geometric r k

end PhysicalYangMillsSU2AdjacentGroundStateSweepStageBCFOscillationEnergyMajorantPhysicalityTailInput

end AdjacentBCFOscillationMajorant

end

end MathlibAnalytic
end MGAP4D
