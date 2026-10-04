import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGroundStateSweepStageProfileCoreMajorantTail
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageProfileOscillationMajorant
import Mathlib.Tactic

/-!
# Adjacent SU(2) raw tail from a scalar continuous oscillation-energy majorant

PR #5144 proves on the bounded-concrete core that any stagewise concrete
target-link oscillation profile `delta` gives

  ProfileEnergy(f) <= (1/6) * sum_e delta(e)^2.

PR #5145 packages one model-facing route by requiring each coordinate
`delta_n(f,e)` itself to depend continuously on the ambient joint-L2 vector.
That is sufficient, but stronger than what the Dobrushin/locality layer
naturally supplies: pointwise variation is not an L2-continuous functional on
the whole L2 space.

This file removes that unnecessary requirement.

At each scale we ask only for a scalar function `majorant_n : L2 -> R` that is
continuous in the genuine joint-L2 topology.  On the bounded-concrete core,
for each vector f one may choose an arbitrary nonnegative pointwise
oscillation profile delta_f, with no continuity requirement, provided

  OscillationEnergy(delta_f) <= majorant_n(f).

The #5144 profile-energy inequality and the #5141 dense-core closure then give
the full-L2 bound.  Thus Dobrushin variation may remain pointwise while only
its final scalar energy envelope needs an L2-continuous extension.

The common-marginal physicality defect, physical-commutation tail, and
beta-majorant tail remain separate.  No conditional expectation is identified
with the physical transfer operator, Markov update time is not identified with
Euclidean time, and no H1-D5 exact descent is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentScalarOscillationMajorantTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentScalarOscillationMajorantCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentScalarOscillationMajorantSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentScalarOscillationMajorantMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentScalarOscillationMajorantBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentScalarOscillationMajorantSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentScalarOscillationMajorantNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private theorem su2AdjacentScalarOscillationMajorant_two_pos : 0 < (2 : ℕ) := by
  norm_num

section AdjacentScalarOscillationMajorant

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

/-- Model-facing adjacent input with an L2-continuous scalar majorant, while
the concrete oscillation profile itself is needed only pointwise on the dense
bounded-concrete core. -/
structure PhysicalYangMillsSU2AdjacentGroundStateSweepStageScalarOscillationEnergyMajorantPhysicalityTailInput where
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
          (halfExtent (n + 1)) 2 su2AdjacentScalarOscillationMajorant_two_pos
          (beta n) (hbeta n) → ℝ
  majorant_continuous :
    ∀ n, Continuous (majorant n)
  boundedCore_oscillationEnergy_le_majorant :
    ∀ n f,
      f ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
            (halfExtent (n + 1)) 2
            su2AdjacentScalarOscillationMajorant_two_pos
            (beta n) (hbeta n) →
        ∃ delta :
            PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)) → ℝ,
          (∀ e, 0 ≤ delta e) ∧
          PeriodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageConcreteOscillationProfileBoundedBy
            (halfExtent (n + 1)) 2
            su2AdjacentScalarOscillationMajorant_two_pos
            (beta n) (hbeta n) f delta ∧
          periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy
              (halfExtent (n + 1)) delta ≤
            majorant n f
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

namespace PhysicalYangMillsSU2AdjacentGroundStateSweepStageScalarOscillationEnergyMajorantPhysicalityTailInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentGroundStateSweepStageScalarOscillationEnergyMajorantPhysicalityTailInput
        (Q := Q) (R := R))

include G

/-- Pointwise oscillation witnesses on the bounded-concrete core supply the
core inequality required by the #5142 continuous-majorant receiver. -/
theorem boundedCore_profileEnergy_le_majorant
    (n : ℕ)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        (halfExtent (n + 1)) 2 su2AdjacentScalarOscillationMajorant_two_pos
        (beta n) (hbeta n))
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          (halfExtent (n + 1)) 2 su2AdjacentScalarOscillationMajorant_two_pos
          (beta n) (hbeta n)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
        (halfExtent (n + 1)) 2 su2AdjacentScalarOscillationMajorant_two_pos
        (beta n) (hbeta n) f ≤
      G.majorant n f := by
  rcases G.boundedCore_oscillationEnergy_le_majorant n f hf with
    ⟨delta, hdelta, hOsc, hEnergy⟩
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy_le_oscillationEnergy
      (halfExtent (n + 1)) 2 su2AdjacentScalarOscillationMajorant_two_pos
      (beta n) (hbeta n) f delta hdelta hOsc).trans hEnergy

/-- The scalar-majorant formulation supplies the #5142 continuous core
majorants with no requirement that the underlying pointwise oscillation
profile itself be L2-continuous. -/
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
    rcases G.splitMajorantPhysicality_tail r k with
      ⟨Cmajor, Cphys, rho, distance,
        hCmajor, hCphys, hrho0, hrho1, hDistance, hMajorTail, hPhys⟩
    refine
      ⟨Cmajor, Cphys, rho, distance,
        hCmajor, hCphys, hrho0, hrho1, hDistance, ?_, hPhys⟩
    intro n
    refine ⟨G.majorant n, G.majorant_continuous n, ?_, ?_⟩
    · intro f hf
      exact boundedCore_profileEnergy_le_majorant Q R G n f hf
    · exact hMajorTail n

/-- The scalar oscillation-energy formulation inherits the actual adjacent
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

/-- The scalar oscillation-energy formulation inherits the total
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
    PhysicalYangMillsSU2AdjacentGroundStateSweepStageProfileCoreMajorantPhysicalityTailInput.totalVariance_tail
      Q R
      (toGroundStateSweepStageProfileCoreMajorantPhysicalityTailInput Q R G)
      r k

/-- The scalar oscillation-energy formulation inherits adjacent orbit-mismatch
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

end PhysicalYangMillsSU2AdjacentGroundStateSweepStageScalarOscillationEnergyMajorantPhysicalityTailInput

end AdjacentScalarOscillationMajorant

end

end MathlibAnalytic
end MGAP4D
