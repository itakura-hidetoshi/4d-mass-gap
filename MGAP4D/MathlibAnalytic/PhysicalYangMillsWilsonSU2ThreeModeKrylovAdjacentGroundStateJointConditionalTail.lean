import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstructionPairHaarConditionalTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointPairHaarConditionalExpectationTransport
import Mathlib.Tactic

/-!
# Move the adjacent SU(2) raw conditional tail to genuine ground-state joint L²

PR #5133 reduces the raw reconstruction tail to ordered pair-Haar L² at the
fine scale.  PRs #5134--#5136 identify that pair-Haar carrier exactly, through
the positive half-density change of measure, with the genuine finite-volume
ground-state joint L² carrier.

This file plugs that exact equivalence into the adjacent-Krylov receiver.

A bounded operator on the genuine ground-state joint L² space is conjugated
back to pair Haar.  On the actual frozen-coupling Krylov vector, the raw
squared residual is therefore *exactly equal* to the genuine joint-L² residual.
No density comparison constant, no projected-range defect, and no global-Gibbs
carrier identification is introduced.

The second term in the #5133 split is deliberately unchanged: after the
candidate is transported through the projective/common-marginal chain, its
distance from the coarse completed physical-pair range is still the genuine
cross-scale physicality defect.

Thus the raw model-facing analytic problem can now be stated directly on the
actual ground-state joint law, where the existing one-link/six-color sweep and
relative-Poincare machinery lives.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentGroundStateJointTailTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentGroundStateJointTailCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentGroundStateJointTailSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentGroundStateJointTailMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentGroundStateJointTailBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentGroundStateJointTailSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentGroundStateJointTailNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section GroundStateJointConditionalTail

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

private theorem su2AdjacentGroundStateJointTail_two_pos : 0 < (2 : ℕ) := by
  norm_num

/-- Fine-scale frozen-coupling Krylov output after exact half-density transport
from ordered pair Haar to the genuine ground-state joint L² law. -/
noncomputable def physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
    (n r : ℕ) (k : Fin 3) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      (halfExtent (n + 1)) 2 su2AdjacentGroundStateJointTail_two_pos
      (beta n) (hbeta n) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      (halfExtent (n + 1)) 2 su2AdjacentGroundStateJointTail_two_pos
      (beta n) (hbeta n)
    (physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)

/-- Conjugate a genuine fine ground-state joint operator exactly back to the
ordered pair-Haar carrier used by the #5133 receiver. -/
noncomputable def physicalYangMillsSU2AdjacentFineGroundStateJointCandidatePairHaar
    (n : ℕ)
    (candidate :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          (halfExtent (n + 1)) 2 su2AdjacentGroundStateJointTail_two_pos
          (beta n) (hbeta n) →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          (halfExtent (n + 1)) 2 su2AdjacentGroundStateJointTail_two_pos
          (beta n) (hbeta n)) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent (n + 1)) 2 →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent (n + 1)) 2 :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOperatorPairHaarConjugate
    (halfExtent (n + 1)) 2 su2AdjacentGroundStateJointTail_two_pos
    (beta n) (hbeta n) candidate

/-- On every actual frozen Krylov vector, the pair-Haar candidate residual is
exactly the corresponding genuine ground-state joint-L² residual. -/
theorem physicalYangMillsSU2AdjacentFineGroundStateJointCandidatePairHaar_residual_sq_eq
    (n r : ℕ) (k : Fin 3)
    (candidate :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          (halfExtent (n + 1)) 2 su2AdjacentGroundStateJointTail_two_pos
          (beta n) (hbeta n) →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          (halfExtent (n + 1)) 2 su2AdjacentGroundStateJointTail_two_pos
          (beta n) (hbeta n)) :
    ‖physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k -
        physicalYangMillsSU2AdjacentFineGroundStateJointCandidatePairHaar
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n candidate
          (physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k)‖ ^ 2 =
      ‖physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k -
        candidate
          (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k)‖ ^ 2 := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOperatorPairHaarConjugate_residual_sq_eq
      (halfExtent (n + 1)) 2 su2AdjacentGroundStateJointTail_two_pos
      (beta n) (hbeta n) candidate
      (physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)

/-- Model-facing adjacent-Krylov tail input stated on the genuine fine
ground-state joint law.

Only the raw residual has moved carriers.  The second tail remains the exact
common-marginal physicality defect from #5133. -/
structure PhysicalYangMillsSU2AdjacentGroundStateJointConditionalPhysicalityTailInput where
  candidate :
    (n : ℕ) →
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          (halfExtent (n + 1)) 2 su2AdjacentGroundStateJointTail_two_pos
          (beta n) (hbeta n) →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          (halfExtent (n + 1)) 2 su2AdjacentGroundStateJointTail_two_pos
          (beta n) (hbeta n)
  splitResidual_tail :
    ∀ (r : ℕ) (k : Fin 3),
      ∃ (Craw Cphys rho : ℝ) (distance : ℕ → ℕ),
        0 ≤ Craw ∧
        0 ≤ Cphys ∧
        0 ≤ rho ∧
        rho < 1 ∧
        (∀ n, n ≤ distance n) ∧
        (∀ n,
          ‖physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n r k -
              candidate n
                (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
                  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                  n r k)‖ ^ 2 ≤
            Craw * (rho ^ distance n / (1 - rho))) ∧
        ∀ n,
          let pairCandidate :=
            physicalYangMillsSU2AdjacentFineGroundStateJointCandidatePairHaar
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n (candidate n)
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

namespace PhysicalYangMillsSU2AdjacentGroundStateJointConditionalPhysicalityTailInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentGroundStateJointConditionalPhysicalityTailInput
        (Q := Q) (R := R))

include G

/-- Exact half-density conjugation discharges the carrier change and produces
the #5133 pair-Haar receiver with unchanged tail constants. -/
noncomputable def toPairHaarConditionalPhysicalityTailInput :
    PhysicalYangMillsSU2AdjacentPairHaarConditionalPhysicalityTailInput
      (Q := Q) (R := R) where
  candidate := fun n =>
    physicalYangMillsSU2AdjacentFineGroundStateJointCandidatePairHaar
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (G.candidate n)
  splitResidual_tail := by
    intro r k
    rcases G.splitResidual_tail r k with
      ⟨Craw, Cphys, rho, distance,
        hCraw, hCphys, hrho0, hrho1, hDistance, hRaw, hPhys⟩
    refine
      ⟨Craw, Cphys, rho, distance,
        hCraw, hCphys, hrho0, hrho1, hDistance, ?_, ?_⟩
    · intro n
      rw [
        physicalYangMillsSU2AdjacentFineGroundStateJointCandidatePairHaar_residual_sq_eq
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k (G.candidate n)]
      exact hRaw n
    · intro n
      exact hPhys n

/-- The exact joint-L² raw-tail formulation inherits the existing total
reconstruction-variance geometric tail without any density loss. -/
theorem totalVariance_tail
    (r : ℕ) (k : Fin 3) :
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
    PhysicalYangMillsSU2AdjacentPairHaarConditionalPhysicalityTailInput.totalVariance_tail
      Q R
      (toPairHaarConditionalPhysicalityTailInput Q R G)
      r k

/-- The exact joint-L² raw-tail formulation inherits the existing adjacent
orbit-mismatch summability receiver once the separate physical-commutation and
coupling-majorant tails are supplied. -/
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
    (r : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
          Q R n r k) := by
  exact
    PhysicalYangMillsSU2AdjacentPairHaarConditionalPhysicalityTailInput.orbitMismatch_summable
      Q R
      (toPairHaarConditionalPhysicalityTailInput Q R G)
      physicalCommutation_geometric betaMajorant_geometric r k

end PhysicalYangMillsSU2AdjacentGroundStateJointConditionalPhysicalityTailInput

end GroundStateJointConditionalTail

end

end MathlibAnalytic
end MGAP4D
