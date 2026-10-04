import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGroundStateSweepStageProfileTail
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageProfileCoreClosure
import Mathlib.Tactic

/-!
# Close adjacent SU(2) sweep-stage profile bounds from the bounded-concrete core

PR #5140 expresses the raw adjacent tail as the normalized squared sweep-stage
profile of the actual fine frozen Krylov vector.  PR #5141 proves that this
profile energy is continuous on the full genuine ground-state joint L2 carrier
and that any continuous upper majorant proved on the dense bounded-concrete
core extends to every joint-L2 vector with no coefficient loss.

This file composes those two statements at the actual adjacent scales.

The important quantifier order is:

* for each scale, choose a continuous majorant on the full joint-L2 carrier;
* prove the profile-energy upper bound only on the bounded-concrete core;
* evaluate that same majorant on the actual frozen Krylov vector.

No bounded representative of the actual frozen vector is asserted.  In
particular, this avoids the false stronger requirement of one scale-wise
constant bounding the profile energy of every core vector, which would be
incompatible with quadratic scaling.

The common-marginal physicality defect, physical-commutation tail and
beta-majorant tail remain separate.  No transfer/conditional-expectation
identification and no H1-D5 exact descent are introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentSweepProfileCoreMajorantTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentSweepProfileCoreMajorantCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentSweepProfileCoreMajorantSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentSweepProfileCoreMajorantMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentSweepProfileCoreMajorantBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentSweepProfileCoreMajorantSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentSweepProfileCoreMajorantNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private theorem su2AdjacentSweepProfileCoreMajorant_two_pos : 0 < (2 : ℕ) := by
  norm_num

section AdjacentSweepProfileCoreMajorant

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

/-- The adjacent profile energy from #5140 is literally the general profile
energy from #5141 evaluated at the actual fine frozen Krylov vector. -/
theorem physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_generalProfileEnergy
    (n r : ℕ)
    (k : Fin 3) :
    physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
        (halfExtent (n + 1)) 2 su2AdjacentSweepProfileCoreMajorant_two_pos
        (beta n) (hbeta n)
        (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k) := by
  rfl

/-- A continuous profile-energy majorant proved only on the bounded-concrete
core applies, with no loss, to the actual fine frozen Krylov vector. -/
theorem physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_le_of_boundedConcreteCore_majorant
    (n r : ℕ)
    (k : Fin 3)
    (majorant :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          (halfExtent (n + 1)) 2 su2AdjacentSweepProfileCoreMajorant_two_pos
          (beta n) (hbeta n) → ℝ)
    (hMajorant : Continuous majorant)
    (hcore :
      ∀ f,
        f ∈
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
              (halfExtent (n + 1)) 2 su2AdjacentSweepProfileCoreMajorant_two_pos
              (beta n) (hbeta n) →
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
              (halfExtent (n + 1)) 2 su2AdjacentSweepProfileCoreMajorant_two_pos
              (beta n) (hbeta n) f ≤
            majorant f) :
    physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k ≤
      majorant
        (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k) := by
  rw [
    physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_generalProfileEnergy
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy_le_of_boundedConcreteCore
      (halfExtent (n + 1)) 2 su2AdjacentSweepProfileCoreMajorant_two_pos
      (beta n) (hbeta n) majorant hMajorant hcore
      (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k)

/-- Model-facing adjacent input whose raw profile tail is proved through
scale-wise continuous majorants on the dense bounded-concrete core. -/
structure PhysicalYangMillsSU2AdjacentGroundStateSweepStageProfileCoreMajorantPhysicalityTailInput where
  selectedColor : ℕ → Fin 6
  s : ℝ
  hs : 8 < s
  eta : ℝ
  eta_nonneg : 0 ≤ eta
  eta_lt_one : eta < 1
  beta_le_cutoff :
    ∀ n, beta n ≤ GroundStateSourceFixedPairEnergy.jointLeakageLossContractionCutoff s hs
  lossRatio_le_eta :
    ∀ n, GroundStateSourceFixedPairEnergy.jointLeakageLossRatio s (beta n) ≤ eta
  splitCoreMajorantPhysicality_tail :
    ∀ (r : ℕ) (k : Fin 3),
      ∃ (Cprofile Cphys rho : ℝ) (distance : ℕ → ℕ),
        0 ≤ Cprofile ∧
        0 ≤ Cphys ∧
        0 ≤ rho ∧
        rho < 1 ∧
        (∀ n, n ≤ distance n) ∧
        (∀ n,
          ∃ majorant :
              PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
                  (halfExtent (n + 1)) 2
                  su2AdjacentSweepProfileCoreMajorant_two_pos
                  (beta n) (hbeta n) → ℝ,
            Continuous majorant ∧
            (∀ f,
              f ∈
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
                    (halfExtent (n + 1)) 2
                    su2AdjacentSweepProfileCoreMajorant_two_pos
                    (beta n) (hbeta n) →
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
                    (halfExtent (n + 1)) 2
                    su2AdjacentSweepProfileCoreMajorant_two_pos
                    (beta n) (hbeta n) f ≤
                  majorant f) ∧
            majorant
                (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
                  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                  n r k) ≤
              Cprofile * (rho ^ distance n / (1 - rho))) ∧
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

namespace PhysicalYangMillsSU2AdjacentGroundStateSweepStageProfileCoreMajorantPhysicalityTailInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentGroundStateSweepStageProfileCoreMajorantPhysicalityTailInput
        (Q := Q) (R := R))

include G

/-- Dense-core closure discharges the raw profile tail and yields the #5140
actual-profile receiver without changing any geometric constant. -/
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
    rcases G.splitCoreMajorantPhysicality_tail r k with
      ⟨Cprofile, Cphys, rho, distance,
        hCprofile, hCphys, hrho0, hrho1, hDistance, hCoreMajorant, hPhys⟩
    refine
      ⟨Cprofile, Cphys, rho, distance,
        hCprofile, hCphys, hrho0, hrho1, hDistance, ?_, hPhys⟩
    intro n
    rcases hCoreMajorant n with
      ⟨majorant, hMajorant, hcore, hActual⟩
    exact
      (physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_le_of_boundedConcreteCore_majorant
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k majorant hMajorant hcore).trans hActual

/-- The core-majorant formulation inherits the total reconstruction-variance
geometric tail. -/
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

/-- The core-majorant formulation inherits adjacent orbit-mismatch summability
once the still-separate physical-commutation and coupling-majorant tails are
supplied. -/
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

end PhysicalYangMillsSU2AdjacentGroundStateSweepStageProfileCoreMajorantPhysicalityTailInput

end AdjacentSweepProfileCoreMajorant

end

end MathlibAnalytic
end MGAP4D
