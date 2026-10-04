import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGroundStateSweepStageProfileCoreMajorantTail
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageProfileOscillationMajorant
import Mathlib.Tactic

/-!
# Adjacent SU(2) raw tail from an L2-continuous oscillation majorant

PR #5144 converts stagewise concrete target-link oscillation bounds into a
normalized quadratic majorant for the genuine six-spatial sweep-stage profile.
When the declared oscillation amplitudes depend continuously on the ambient
joint-L2 vector, that quadratic majorant is itself continuous.

PR #5142 is exactly the model-facing closure interface: a continuous majorant
proved on the bounded-concrete core can be evaluated on the actual fine frozen
Krylov vector, which need not itself be asserted bounded.

This file composes those two layers.  The remaining raw analytic input is now
explicit:

* at each scale n, construct linkwise nonnegative amplitudes delta_n(f,e);
* prove each delta_n(_,e) is continuous in the genuine joint-L2 topology;
* on the bounded-concrete core, realize every canonical sweep stage by a
  concrete representative whose target-link oscillation is <= delta_n(f,e);
* prove the normalized oscillation energy of the actual frozen Krylov vector
  has the required geometric support-distance tail.

No pointwise variation is silently declared L2-continuous.  No conditional
expectation is identified with the physical transfer operator, Markov update
time is not identified with Euclidean time, and no H1-D5 exact descent is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentOscillationMajorantTailTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentOscillationMajorantTailCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentOscillationMajorantTailSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentOscillationMajorantTailMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentOscillationMajorantTailBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentOscillationMajorantTailSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentOscillationMajorantTailNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private theorem su2AdjacentOscillationMajorantTail_two_pos : 0 < (2 : ℕ) := by
  norm_num

section AdjacentOscillationMajorantTail

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

/-- The normalized oscillation-energy majorant at one adjacent scale, evaluated
on an arbitrary genuine joint-L2 vector. -/
noncomputable def physicalYangMillsSU2AdjacentFineGroundStateSweepStageOscillationMajorant
    (n : ℕ)
    (oscillationProfile :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          (halfExtent (n + 1)) 2 su2AdjacentOscillationMajorantTail_two_pos
          (beta n) (hbeta n) →
        PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)) → ℝ)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        (halfExtent (n + 1)) 2 su2AdjacentOscillationMajorantTail_two_pos
        (beta n) (hbeta n)) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationMajorant
    (halfExtent (n + 1)) 2 su2AdjacentOscillationMajorantTail_two_pos
    (beta n) (hbeta n) oscillationProfile f

/-- Model-facing adjacent input whose raw tail is supplied by an L2-continuous
linkwise oscillation profile. -/
structure PhysicalYangMillsSU2AdjacentGroundStateSweepStageOscillationMajorantPhysicalityTailInput where
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
  oscillationProfile :
    ∀ n,
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          (halfExtent (n + 1)) 2 su2AdjacentOscillationMajorantTail_two_pos
          (beta n) (hbeta n) →
        PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)) → ℝ
  oscillationProfile_nonneg :
    ∀ n f e, 0 ≤ oscillationProfile n f e
  oscillationProfile_continuous :
    ∀ n e, Continuous (fun f => oscillationProfile n f e)
  boundedCore_stageOscillation :
    ∀ n f,
      f ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
            (halfExtent (n + 1)) 2
            su2AdjacentOscillationMajorantTail_two_pos
            (beta n) (hbeta n) →
        PeriodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageConcreteOscillationProfileBoundedBy
          (halfExtent (n + 1)) 2
          su2AdjacentOscillationMajorantTail_two_pos
          (beta n) (hbeta n) f (oscillationProfile n f)
  splitOscillationPhysicality_tail :
    ∀ (r : ℕ) (k : Fin 3),
      ∃ (Cosc Cphys rho : ℝ) (distance : ℕ → ℕ),
        0 ≤ Cosc ∧
        0 ≤ Cphys ∧
        0 ≤ rho ∧
        rho < 1 ∧
        (∀ n, n ≤ distance n) ∧
        (∀ n,
          physicalYangMillsSU2AdjacentFineGroundStateSweepStageOscillationMajorant
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n (oscillationProfile n)
              (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n r k) ≤
            Cosc * (rho ^ distance n / (1 - rho))) ∧
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

namespace PhysicalYangMillsSU2AdjacentGroundStateSweepStageOscillationMajorantPhysicalityTailInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentGroundStateSweepStageOscillationMajorantPhysicalityTailInput
        (Q := Q) (R := R))

include G

/-- The oscillation-energy formulation supplies the continuous core majorants
required by PR #5142 with no coefficient loss. -/
noncomputable def toGroundStateSweepStageProfileCoreMajorantPhysicalityTailInput :
    PhysicalYangMillsSU2AdjacentGroundStateSweepStageProfileCoreMajorantPhysicalityTailInput
      (Q := Q) (R := R) where
  selectedColor := G.selectedColor
  s := G.s
  hs := G.hs
  eta := G.eta
  eta_nonneg := G.eta_nonneg
  eta_lt_one := G.eta_lt_one
  beta_le_cutoff := G.beta_le_cutoff
  lossRatio_le_eta := G.lossRatio_le_eta
  splitCoreMajorantPhysicality_tail := by
    intro r k
    rcases G.splitOscillationPhysicality_tail r k with
      ⟨Cosc, Cphys, rho, distance,
        hCosc, hCphys, hrho0, hrho1, hDistance, hOscTail, hPhys⟩
    refine
      ⟨Cosc, Cphys, rho, distance,
        hCosc, hCphys, hrho0, hrho1, hDistance, ?_, hPhys⟩
    intro n
    let majorant :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            (halfExtent (n + 1)) 2
            su2AdjacentOscillationMajorantTail_two_pos
            (beta n) (hbeta n) → ℝ :=
      periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationMajorant
        (halfExtent (n + 1)) 2
        su2AdjacentOscillationMajorantTail_two_pos
        (beta n) (hbeta n) (G.oscillationProfile n)
    have hMajorant : Continuous majorant := by
      dsimp [majorant]
      exact
        continuous_periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationMajorant
          (halfExtent (n + 1)) 2
          su2AdjacentOscillationMajorantTail_two_pos
          (beta n) (hbeta n)
          (G.oscillationProfile n)
          (G.oscillationProfile_continuous n)
    refine ⟨majorant, hMajorant, ?_, ?_⟩
    · intro f hf
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy_le_oscillationEnergy
          (halfExtent (n + 1)) 2
          su2AdjacentOscillationMajorantTail_two_pos
          (beta n) (hbeta n)
          f (G.oscillationProfile n f)
          (G.oscillationProfile_nonneg n f)
          (G.boundedCore_stageOscillation n f hf)
    · simpa [
        majorant,
        physicalYangMillsSU2AdjacentFineGroundStateSweepStageOscillationMajorant
      ] using hOscTail n

/-- The L2-continuous oscillation formulation inherits the actual adjacent
sweep-stage profile geometric tail. -/
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
  have Hcore :=
    toGroundStateSweepStageProfileCoreMajorantPhysicalityTailInput Q R G
  rcases Hcore.splitCoreMajorantPhysicality_tail r k with
    ⟨Cprofile, Cphys, rho, distance,
      hCprofile, hCphys, hrho0, hrho1, hDistance, hMajorant, hPhys⟩
  refine
    ⟨Cprofile, rho, distance,
      hCprofile, hrho0, hrho1, hDistance, ?_⟩
  intro n
  rcases hMajorant n with
    ⟨majorant, hContinuous, hCore, hActual⟩
  exact
    (physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_le_of_boundedConcreteCore_majorant
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k majorant hContinuous hCore).trans hActual

/-- The oscillation-majorant formulation inherits the total reconstruction
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
    PhysicalYangMillsSU2AdjacentGroundStateSweepStageProfileCoreMajorantPhysicalityTailInput.totalVariance_tail
      Q R
      (toGroundStateSweepStageProfileCoreMajorantPhysicalityTailInput Q R G)
      r k

/-- The oscillation-majorant formulation inherits adjacent orbit-mismatch
summability once the still-separate physical-commutation and coupling-majorant
tails are supplied. -/
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
    PhysicalYangMillsSU2AdjacentGroundStateSweepStageProfileCoreMajorantPhysicalityTailInput.orbitMismatch_summable
      Q R
      (toGroundStateSweepStageProfileCoreMajorantPhysicalityTailInput Q R G)
      physicalCommutation_geometric betaMajorant_geometric r k

end PhysicalYangMillsSU2AdjacentGroundStateSweepStageOscillationMajorantPhysicalityTailInput

end AdjacentOscillationMajorantTail

end

end MathlibAnalytic
end MGAP4D
