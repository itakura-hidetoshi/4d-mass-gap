import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGroundStateSixSpatialEnergyTail
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedDefectMargin
import Mathlib.Tactic

/-!
# Reduce the adjacent SU(2) six-spatial energy tail to one-link sweep path loss

For the genuine positive-beta ground-state joint law, the existing ordered
source-fixed analysis proves

  (1 - eta_beta) * E6(f) <= L6(f),

where E6 is the normalized six-spatial block residual energy,
L6 is the normalized same-color one-link sweep path loss, and
eta_beta = jointLeakageLossRatio s beta is strictly below one in the
volume/rank-independent loss-contraction region.

This file turns that coercive inequality into the explicit upper bound

  E6(f) <= L6(f) / (1 - eta_beta)

and plugs it into the adjacent SU(2) receiver. With any uniform
eta_beta <= eta < 1, a geometric path-loss tail therefore gives the
six-spatial energy tail with only the fixed factor 1 / (1 - eta).

This leaves the raw analytic problem on the actual ordered one-link
conditional-expectation trajectory. The common-marginal physicality defect,
physical-commutation tail, and beta-majorant tail remain separate. No
conditional expectation is identified with the physical transfer operator and
no H1-D5 exact descent is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

namespace GroundStateSourceFixedPairEnergy

/-- In the strict ordered loss-contraction region, the genuine six-spatial
residual energy is bounded above by the normalized one-link sweep path loss
divided by the positive renewal margin. -/
theorem sixSpatial_residualEnergy_le_pathLoss_div_one_sub_lossRatio
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 8 < s)
    (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
        H N hN beta hbeta f ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
          H N hN beta hbeta f /
        (1 - jointLeakageLossRatio s beta) := by
  have hEta :=
    jointLeakageLossRatio_nonneg_lt_one s hs beta hbeta hcut
  have hDen : 0 < 1 - jointLeakageLossRatio s beta :=
    sub_pos.mpr hEta.2
  have hCoercive :=
    sixSpatial_pathLoss_ge_one_sub_lossRatio_mul_residualEnergy
      H N hN beta hbeta s hs hcut f
  apply (le_div_iff₀ hDen).2
  simpa only [mul_comm] using hCoercive

end GroundStateSourceFixedPairEnergy

local instance su2AdjacentPathLossTailTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentPathLossTailCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentPathLossTailSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentPathLossTailMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentPathLossTailBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentPathLossTailSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentPathLossTailNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private theorem su2AdjacentPathLossTail_two_pos : 0 < (2 : ℕ) := by
  norm_num

section AdjacentPathLossTail

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

/-- Normalized six-color same-color one-link sweep path loss of the actual
fine frozen Krylov vector on the genuine ground-state joint carrier. -/
noncomputable def physicalYangMillsSU2AdjacentFineGroundStateSixSpatialOneLinkSweepPathLoss
    (n r : ℕ)
    (k : Fin 3) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
    (halfExtent (n + 1)) 2 su2AdjacentPathLossTail_two_pos
    (beta n) (hbeta n)
    (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k)

/-- At every scale inside the strict ordered loss-contraction region, the
six-spatial energy of the actual frozen Krylov vector is bounded by its
one-link sweep path loss divided by the positive renewal margin. -/
theorem physicalYangMillsSU2AdjacentFineGroundStateSixSpatialResidualEnergy_le_pathLoss_div
    (s : ℝ)
    (hs : 8 < s)
    (n r : ℕ)
    (k : Fin 3)
    (hcut :
      beta n ≤ jointLeakageLossContractionCutoff s hs) :
    physicalYangMillsSU2AdjacentFineGroundStateSixSpatialResidualEnergy
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k ≤
      physicalYangMillsSU2AdjacentFineGroundStateSixSpatialOneLinkSweepPathLoss
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k /
        (1 - jointLeakageLossRatio s (beta n)) := by
  exact
    GroundStateSourceFixedPairEnergy.sixSpatial_residualEnergy_le_pathLoss_div_one_sub_lossRatio
      (halfExtent (n + 1)) 2 su2AdjacentPathLossTail_two_pos
      (beta n) (hbeta n) s hs hcut
      (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k)

/-- Model-facing adjacent input with the raw term reduced to the normalized
same-color one-link sweep path loss.

The single uniform eta < 1 only bounds the already-constructed ordered loss
ratio; it is not a new transfer-operator contraction. -/
structure PhysicalYangMillsSU2AdjacentGroundStateSixSpatialPathLossPhysicalityTailInput where
  selectedColor : ℕ → Fin 6
  s : ℝ
  hs : 8 < s
  eta : ℝ
  eta_nonneg : 0 ≤ eta
  eta_lt_one : eta < 1
  beta_le_cutoff :
    ∀ n, beta n ≤ jointLeakageLossContractionCutoff s hs
  lossRatio_le_eta :
    ∀ n, jointLeakageLossRatio s (beta n) ≤ eta
  splitPathLossPhysicality_tail :
    ∀ (r : ℕ) (k : Fin 3),
      ∃ (Cpath Cphys rho : ℝ) (distance : ℕ → ℕ),
        0 ≤ Cpath ∧
        0 ≤ Cphys ∧
        0 ≤ rho ∧
        rho < 1 ∧
        (∀ n, n ≤ distance n) ∧
        (∀ n,
          physicalYangMillsSU2AdjacentFineGroundStateSixSpatialOneLinkSweepPathLoss
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r k ≤
            Cpath * (rho ^ distance n / (1 - rho))) ∧
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

namespace PhysicalYangMillsSU2AdjacentGroundStateSixSpatialPathLossPhysicalityTailInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentGroundStateSixSpatialPathLossPhysicalityTailInput
        (Q := Q) (R := R))

include G

/-- A geometric path-loss tail plus a uniform strict ordered loss-ratio margin
produces the #5138 six-spatial energy tail. -/
noncomputable def toGroundStateSixSpatialEnergyPhysicalityTailInput :
    PhysicalYangMillsSU2AdjacentGroundStateSixSpatialEnergyPhysicalityTailInput
      (Q := Q) (R := R) where
  selectedColor := G.selectedColor
  splitEnergyPhysicality_tail := by
    intro r k
    rcases G.splitPathLossPhysicality_tail r k with
      ⟨Cpath, Cphys, rho, distance,
        hCpath, hCphys, hrho0, hrho1, hDistance, hPath, hPhys⟩
    have hDen : 0 < 1 - G.eta := sub_pos.mpr G.eta_lt_one
    refine
      ⟨Cpath / (1 - G.eta), Cphys, rho, distance,
        div_nonneg hCpath hDen.le, hCphys, hrho0, hrho1, hDistance, ?_, ?_⟩
    · intro n
      let E :=
        physicalYangMillsSU2AdjacentFineGroundStateSixSpatialResidualEnergy
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k
      let L :=
        physicalYangMillsSU2AdjacentFineGroundStateSixSpatialOneLinkSweepPathLoss
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k
      have hCoercive :=
        GroundStateSourceFixedPairEnergy.sixSpatial_pathLoss_ge_one_sub_lossRatio_mul_residualEnergy
          (halfExtent (n + 1)) 2 su2AdjacentPathLossTail_two_pos
          (beta n) (hbeta n) G.s G.hs (G.beta_le_cutoff n)
          (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k)
      have hE0 : 0 ≤ E := by
        dsimp [E, physicalYangMillsSU2AdjacentFineGroundStateSixSpatialResidualEnergy]
        exact
          groundStateJointColorNormalizedResidualEnergy_nonneg
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
              (halfExtent (n + 1)) 2 su2AdjacentPathLossTail_two_pos
              (beta n) (hbeta n))
            (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r k)
      have hMargin :
          (1 - G.eta) * E ≤ L := by
        have hCoeff :
            1 - G.eta ≤ 1 - jointLeakageLossRatio G.s (beta n) := by
          linarith [G.lossRatio_le_eta n]
        calc
          (1 - G.eta) * E ≤
              (1 - jointLeakageLossRatio G.s (beta n)) * E :=
            mul_le_mul_of_nonneg_right hCoeff hE0
          _ ≤ L := by
            simpa [E, L] using hCoercive
      have hEnergyDiv : E ≤ L / (1 - G.eta) := by
        apply (le_div_iff₀ hDen).2
        simpa only [mul_comm] using hMargin
      calc
        E ≤ L / (1 - G.eta) := hEnergyDiv
        _ ≤
            (Cpath * (rho ^ distance n / (1 - rho))) /
              (1 - G.eta) := by
          exact div_le_div_of_nonneg_right (hPath n) hDen.le
        _ =
            (Cpath / (1 - G.eta)) *
              (rho ^ distance n / (1 - rho)) := by
          ring
    · intro n
      simpa using hPhys n

/-- The path-loss formulation inherits the total reconstruction-variance
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
    PhysicalYangMillsSU2AdjacentGroundStateSixSpatialEnergyPhysicalityTailInput.totalVariance_tail
      Q R
      (toGroundStateSixSpatialEnergyPhysicalityTailInput Q R G)
      r k

/-- The path-loss formulation inherits adjacent orbit-mismatch summability
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
    PhysicalYangMillsSU2AdjacentGroundStateSixSpatialEnergyPhysicalityTailInput.orbitMismatch_summable
      Q R
      (toGroundStateSixSpatialEnergyPhysicalityTailInput Q R G)
      physicalCommutation_geometric betaMajorant_geometric r k

end PhysicalYangMillsSU2AdjacentGroundStateSixSpatialPathLossPhysicalityTailInput

end AdjacentPathLossTail

end

end MathlibAnalytic
end MGAP4D
