import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGroundStateSixSpatialPathLossTail
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepStageLocalProfileExactResidual
import Mathlib.Tactic

/-!
# Expose the adjacent SU(2) path-loss tail as a genuine link-indexed sweep-stage profile

PR #5139 reduces the raw adjacent reconstruction tail to the normalized
same-color one-link sweep path loss on the genuine ground-state joint L2
carrier.

The existing sweep-stage profile theorem identifies that path loss exactly as

  L6(f) = (1/6) * sum_e profile_f(e)^2,

where e runs over genuine spatial links.  Moreover, for the canonical
duplicate-free sweep, profile_f(e) is exactly the norm of the one-link
conditional-expectation residual at the preserved prefix stage.

This file specializes both facts to the actual fine frozen Krylov vector.
Thus the remaining raw tail is expressed on the same link-indexed carrier as
the Wilson/Dobrushin influence matrix, without adding a volume factor or a
comparison constant.

The common-marginal physicality defect, physical-commutation tail and
beta-majorant tail remain separate.  No Markov update time is identified with
Euclidean time and no H1-D5 exact descent is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentSweepStageProfileTailTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentSweepStageProfileTailCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentSweepStageProfileTailSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentSweepStageProfileTailMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentSweepStageProfileTailBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentSweepStageProfileTailSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentSweepStageProfileTailNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private theorem su2AdjacentSweepStageProfileTail_two_pos : 0 < (2 : ℕ) := by
  norm_num

section AdjacentSweepStageProfileTail

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

/-- Genuine spatial-link sweep-stage residual amplitude for the actual fine
frozen Krylov vector. -/
noncomputable def physicalYangMillsSU2AdjacentFineGroundStateSweepStageLocalProfile
    (n r : ℕ)
    (k : Fin 3)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
    (halfExtent (n + 1)) 2 su2AdjacentSweepStageProfileTail_two_pos
    (beta n) (hbeta n)
    (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k)
    e

/-- The actual adjacent sweep-stage profile is pointwise nonnegative. -/
theorem physicalYangMillsSU2AdjacentFineGroundStateSweepStageLocalProfile_nonneg
    (n r : ℕ)
    (k : Fin 3)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) :
    0 ≤
      physicalYangMillsSU2AdjacentFineGroundStateSweepStageLocalProfile
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k e := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_nonneg
      (halfExtent (n + 1)) 2 su2AdjacentSweepStageProfileTail_two_pos
      (beta n) (hbeta n)
      (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k)
      e

/-- Exact normalized local-profile energy of the actual fine frozen Krylov
vector. -/
noncomputable def physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy
    (n r : ℕ)
    (k : Fin 3) : ℝ :=
  (1 / 6 : ℝ) *
    ∑ e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
      physicalYangMillsSU2AdjacentFineGroundStateSweepStageLocalProfile
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k e ^ 2

/-- The link-indexed profile energy is exactly the #5139 one-link sweep path
loss, with no inequality or volume-dependent multiplicity. -/
theorem physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_pathLoss
    (n r : ℕ)
    (k : Fin 3) :
    physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k =
      physicalYangMillsSU2AdjacentFineGroundStateSixSpatialOneLinkSweepPathLoss
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_normalized_sq_sum_eq_sweepPathLoss
      (halfExtent (n + 1)) 2 su2AdjacentSweepStageProfileTail_two_pos
      (beta n) (hbeta n)
      (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k)

/-- Fixed-color link type attached to an ordinary fine spatial link. -/
abbrev PhysicalYangMillsSU2AdjacentFineGroundStateFixedSpatialColorLink
    (n : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : Type :=
  PeriodicHypercubicEvenFixedSpatialColorLink
    (halfExtent (n + 1))
    (periodicHypercubicEvenSpatialSliceLinkColor (halfExtent (n + 1)) e)

/-- The actual frozen Krylov vector after a canonical fixed-color sweep prefix. -/
noncomputable def physicalYangMillsSU2AdjacentFineGroundStateSweepStageVector
    (n r : ℕ) (k : Fin 3)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (pre : List
      (PhysicalYangMillsSU2AdjacentFineGroundStateFixedSpatialColorLink
        (halfExtent := halfExtent) n e)) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      (halfExtent (n + 1)) 2 su2AdjacentSweepStageProfileTail_two_pos
      (beta n) (hbeta n) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
    (halfExtent (n + 1)) 2 su2AdjacentSweepStageProfileTail_two_pos
    (beta n) (hbeta n)
    (periodicHypercubicEvenSpatialSliceLinkColor (halfExtent (n + 1)) e)
    pre
    (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)

/-- The genuine one-link conditional expectation applied at the selected
canonical sweep stage. -/
noncomputable def physicalYangMillsSU2AdjacentFineGroundStateSweepStageCondExp
    (n : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        (halfExtent (n + 1)) 2 su2AdjacentSweepStageProfileTail_two_pos
        (beta n) (hbeta n) →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        (halfExtent (n + 1)) 2 su2AdjacentSweepStageProfileTail_two_pos
        (beta n) (hbeta n) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
    (halfExtent (n + 1)) 2 su2AdjacentSweepStageProfileTail_two_pos
    (beta n) (hbeta n)
    (periodicHypercubicEvenSpatialSliceLinkColor (halfExtent (n + 1)) e)
    (⟨e, rfl⟩ :
      PhysicalYangMillsSU2AdjacentFineGroundStateFixedSpatialColorLink
        (halfExtent := halfExtent) n e)

/-- On a canonical prefix decomposition, the actual adjacent local profile is
literally the norm of the genuine one-link conditional-expectation residual at
that stage. -/
theorem physicalYangMillsSU2AdjacentFineGroundStateSweepStageLocalProfile_eq_stageResidual_norm_of_canonicalPrefix
    (n r : ℕ) (k : Fin 3)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (pre suffix : List
      (PhysicalYangMillsSU2AdjacentFineGroundStateFixedSpatialColorLink
        (halfExtent := halfExtent) n e))
    (hSplit :
      (Finset.univ : Finset
        (PhysicalYangMillsSU2AdjacentFineGroundStateFixedSpatialColorLink
          (halfExtent := halfExtent) n e)).toList =
        pre ++ (⟨e, rfl⟩ : PhysicalYangMillsSU2AdjacentFineGroundStateFixedSpatialColorLink
          (halfExtent := halfExtent) n e) :: suffix)
    (hFresh :
      (⟨e, rfl⟩ : PhysicalYangMillsSU2AdjacentFineGroundStateFixedSpatialColorLink
        (halfExtent := halfExtent) n e) ∉ pre) :
    physicalYangMillsSU2AdjacentFineGroundStateSweepStageLocalProfile
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k e =
      ‖physicalYangMillsSU2AdjacentFineGroundStateSweepStageVector
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k e pre -
        physicalYangMillsSU2AdjacentFineGroundStateSweepStageCondExp
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e
          (physicalYangMillsSU2AdjacentFineGroundStateSweepStageVector
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k e pre)‖ := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_eq_stageResidual_norm_of_canonicalPrefix
      (halfExtent (n + 1)) 2 su2AdjacentSweepStageProfileTail_two_pos
      (beta n) (hbeta n) e pre suffix
      (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)
      hSplit hFresh

/-- Model-facing adjacent input whose raw term is now the exact normalized
sum of squared genuine link-indexed sweep-stage residual amplitudes. -/
structure PhysicalYangMillsSU2AdjacentGroundStateSweepStageProfilePhysicalityTailInput where
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
  splitProfilePhysicality_tail :
    ∀ (r : ℕ) (k : Fin 3),
      ∃ (Cprofile Cphys rho : ℝ) (distance : ℕ → ℕ),
        0 ≤ Cprofile ∧
        0 ≤ Cphys ∧
        0 ≤ rho ∧
        rho < 1 ∧
        (∀ n, n ≤ distance n) ∧
        (∀ n,
          physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r k ≤
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

namespace PhysicalYangMillsSU2AdjacentGroundStateSweepStageProfilePhysicalityTailInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentGroundStateSweepStageProfilePhysicalityTailInput
        (Q := Q) (R := R))

include G

/-- Exact profile-energy identification discharges the carrier reshaping and
produces the #5139 path-loss receiver with unchanged geometric constants. -/
noncomputable def toGroundStateSixSpatialPathLossPhysicalityTailInput :
    PhysicalYangMillsSU2AdjacentGroundStateSixSpatialPathLossPhysicalityTailInput
      (Q := Q) (R := R) where
  selectedColor := G.selectedColor
  s := G.s
  hs := G.hs
  eta := G.eta
  eta_nonneg := G.eta_nonneg
  eta_lt_one := G.eta_lt_one
  beta_le_cutoff := G.beta_le_cutoff
  lossRatio_le_eta := G.lossRatio_le_eta
  splitPathLossPhysicality_tail := by
    intro r k
    rcases G.splitProfilePhysicality_tail r k with
      ⟨Cprofile, Cphys, rho, distance,
        hCprofile, hCphys, hrho0, hrho1, hDistance, hProfile, hPhys⟩
    refine
      ⟨Cprofile, Cphys, rho, distance,
        hCprofile, hCphys, hrho0, hrho1, hDistance, ?_, ?_⟩
    · intro n
      rw [←
        physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_pathLoss
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k]
      exact hProfile n
    · intro n
      exact hPhys n

/-- The link-profile formulation inherits the total reconstruction-variance
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
    PhysicalYangMillsSU2AdjacentGroundStateSixSpatialPathLossPhysicalityTailInput.totalVariance_tail
      Q R
      (toGroundStateSixSpatialPathLossPhysicalityTailInput Q R G)
      r k

/-- The link-profile formulation inherits adjacent orbit-mismatch summability
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
    PhysicalYangMillsSU2AdjacentGroundStateSixSpatialPathLossPhysicalityTailInput.orbitMismatch_summable
      Q R
      (toGroundStateSixSpatialPathLossPhysicalityTailInput Q R G)
      physicalCommutation_geometric betaMajorant_geometric r k

end PhysicalYangMillsSU2AdjacentGroundStateSweepStageProfilePhysicalityTailInput

end AdjacentSweepStageProfileTail

end

end MathlibAnalytic
end MGAP4D
