import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstructionConditionalTail
import MGAP4D.MathlibAnalytic.RealLinearIsometryProjectedCompression
import Mathlib.Tactic

/-!
# Transport fine selected-marginal conditional candidates to the adjacent common marginal

PR #5129 reduces the projective reconstruction variance to two tails on the
adjacent common marginal:

1. a raw conditional/candidate residual;
2. the physicality defect of the candidate output.

The raw Wilson/Dobrushin estimate naturally lives one layer earlier, on the
selected finite projective marginal at the fine scale n+1.  The actual frozen
Krylov vector is already in the range of the canonical transition from that
selected marginal to the adjacent union marginal.

This file transports an arbitrary bounded fine selected-marginal candidate by
canonical projected compression through that transition isometry.  On the
actual fine frozen vector the transport is exact, so the common-marginal raw
residual norm is *identically equal* to the selected-marginal residual norm.
No extra range defect is introduced.

The physicality defect is deliberately left on the adjacent common marginal:
that is the genuinely cross-scale obstruction which still has to be controlled
by the Wilson locality/refinement argument.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentRightSelectedTransportTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentRightSelectedTransportCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentRightSelectedTransportSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentRightSelectedTransportMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentRightSelectedTransportBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentRightSelectedTransportSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentRightSelectedTransportSpatialHaarSFinite (H : ℕ) :
    SFinite
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentRightSelectedTransportNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section RightSelectedConditionalTransport

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

/-- Canonical isometric transition from the fine selected marginal at n+1 to
the adjacent union marginal. -/
noncomputable def physicalYangMillsSU2AdjacentCommonRightSelectedMarginalEmbedding
    (n : ℕ) :
    Lp ℝ 2 (F.finiteMarginal (R.marginalIndex (n + 1))) →ₗᵢ[ℝ]
      Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) :=
  EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
    (F := F)
    (show R.marginalIndex (n + 1) ⊆
        physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
          (Q := Q) R n by
      exact Finset.subset_union_right)

/-- The existing fine pair embedding factors through the fine selected
projective marginal and then the canonical transition to the common marginal. -/
theorem physicalYangMillsSU2AdjacentCommonRightPairEmbedding_eq_selected_comp
    (n : ℕ) :
    physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n =
      (physicalYangMillsSU2AdjacentCommonRightSelectedMarginalEmbedding
        Q R n).comp
        (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R (n + 1)) := by
  rfl

/-- The actual frozen fine Krylov output before the final transition to the
adjacent union marginal. -/
noncomputable def physicalYangMillsSU2AdjacentFineFrozenStepSelectedVector
    (n r : ℕ) (k : Fin 3) :
    Lp ℝ 2 (F.finiteMarginal (R.marginalIndex (n + 1))) :=
  physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R (n + 1)
    (physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k)

/-- The common frozen vector is exactly the transition of its fine selected
representative. -/
@[simp] theorem
    physicalYangMillsSU2AdjacentCommonFineFrozenStepVector_eq_rightSelectedEmbedding
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentCommonFineFrozenStepVector Q R n r k =
      physicalYangMillsSU2AdjacentCommonRightSelectedMarginalEmbedding Q R n
        (physicalYangMillsSU2AdjacentFineFrozenStepSelectedVector Q R n r k) := by
  unfold physicalYangMillsSU2AdjacentCommonFineFrozenStepVector
  unfold physicalYangMillsSU2AdjacentFineFrozenStepSelectedVector
  rw [physicalYangMillsSU2AdjacentCommonRightPairEmbedding_eq_selected_comp
    Q R n]
  rfl

/-- Transport a bounded operator on the fine selected marginal to the adjacent
common marginal by canonical projected compression through the transition
isometry. -/
noncomputable def physicalYangMillsSU2AdjacentCommonRightSelectedCandidate
    (n : ℕ)
    (candidate :
      Lp ℝ 2 (F.finiteMarginal (R.marginalIndex (n + 1))) →L[ℝ]
        Lp ℝ 2 (F.finiteMarginal (R.marginalIndex (n + 1)))) :
    Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) →L[ℝ]
      Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) :=
  realLinearIsometryProjectedCompression
    (physicalYangMillsSU2AdjacentCommonRightSelectedMarginalEmbedding Q R n)
    candidate

/-- The transported candidate acts by exact conjugation on every vector already
in the fine selected-marginal range. -/
@[simp] theorem
    physicalYangMillsSU2AdjacentCommonRightSelectedCandidate_apply_embedding
    (n : ℕ)
    (candidate :
      Lp ℝ 2 (F.finiteMarginal (R.marginalIndex (n + 1))) →L[ℝ]
        Lp ℝ 2 (F.finiteMarginal (R.marginalIndex (n + 1))))
    (x : Lp ℝ 2 (F.finiteMarginal (R.marginalIndex (n + 1)))) :
    physicalYangMillsSU2AdjacentCommonRightSelectedCandidate
        Q R n candidate
        (physicalYangMillsSU2AdjacentCommonRightSelectedMarginalEmbedding
          Q R n x) =
      physicalYangMillsSU2AdjacentCommonRightSelectedMarginalEmbedding
        Q R n (candidate x) := by
  unfold physicalYangMillsSU2AdjacentCommonRightSelectedCandidate
  exact
    realLinearIsometryProjectedCompression_apply_map
      (physicalYangMillsSU2AdjacentCommonRightSelectedMarginalEmbedding Q R n)
      candidate x

/-- On the actual frozen Krylov vector, transporting the candidate to the
common marginal preserves the raw residual norm exactly. -/
theorem
    physicalYangMillsSU2AdjacentCommonRightSelectedCandidateResidual_norm_eq_selected
    (n r : ℕ) (k : Fin 3)
    (candidate :
      Lp ℝ 2 (F.finiteMarginal (R.marginalIndex (n + 1))) →L[ℝ]
        Lp ℝ 2 (F.finiteMarginal (R.marginalIndex (n + 1)))) :
    ‖physicalYangMillsSU2AdjacentCommonFineFrozenStepVector Q R n r k -
        physicalYangMillsSU2AdjacentCommonRightSelectedCandidate
          Q R n candidate
          (physicalYangMillsSU2AdjacentCommonFineFrozenStepVector Q R n r k)‖ =
      ‖physicalYangMillsSU2AdjacentFineFrozenStepSelectedVector Q R n r k -
        candidate
          (physicalYangMillsSU2AdjacentFineFrozenStepSelectedVector
            Q R n r k)‖ := by
  let J :=
    physicalYangMillsSU2AdjacentCommonRightSelectedMarginalEmbedding Q R n
  let x :=
    physicalYangMillsSU2AdjacentFineFrozenStepSelectedVector Q R n r k
  rw [
    physicalYangMillsSU2AdjacentCommonFineFrozenStepVector_eq_rightSelectedEmbedding
      Q R n r k,
    physicalYangMillsSU2AdjacentCommonRightSelectedCandidate_apply_embedding
      Q R n candidate x]
  change ‖J x - J (candidate x)‖ = ‖x - candidate x‖
  rw [← J.map_sub, J.norm_map]

/-- Squared residual form used directly by the #5129 tail receiver. -/
theorem
    physicalYangMillsSU2AdjacentCommonRightSelectedCandidateResidual_sq_eq_selected
    (n r : ℕ) (k : Fin 3)
    (candidate :
      Lp ℝ 2 (F.finiteMarginal (R.marginalIndex (n + 1))) →L[ℝ]
        Lp ℝ 2 (F.finiteMarginal (R.marginalIndex (n + 1)))) :
    ‖physicalYangMillsSU2AdjacentCommonFineFrozenStepVector Q R n r k -
        physicalYangMillsSU2AdjacentCommonRightSelectedCandidate
          Q R n candidate
          (physicalYangMillsSU2AdjacentCommonFineFrozenStepVector Q R n r k)‖ ^ 2 =
      ‖physicalYangMillsSU2AdjacentFineFrozenStepSelectedVector Q R n r k -
        candidate
          (physicalYangMillsSU2AdjacentFineFrozenStepSelectedVector
            Q R n r k)‖ ^ 2 := by
  rw [
    physicalYangMillsSU2AdjacentCommonRightSelectedCandidateResidual_norm_eq_selected
      Q R n r k candidate]

/-- Model-facing split after transporting only the raw conditional candidate.

The raw tail now lives entirely on the fine selected projective marginal, where
a concrete finite Wilson/Dobrushin conditional expectation can be constructed.
The physicality tail remains on the adjacent common marginal and measures the
genuine mismatch between the transported fine conditional output and the coarse
embedded completed physical pair carrier. -/
structure PhysicalYangMillsSU2AdjacentRightSelectedConditionalPhysicalityTailInput where
  candidate :
    (n : ℕ) →
      Lp ℝ 2 (F.finiteMarginal (R.marginalIndex (n + 1))) →L[ℝ]
        Lp ℝ 2 (F.finiteMarginal (R.marginalIndex (n + 1)))
  splitResidual_tail :
    ∀ (r : ℕ) (k : Fin 3),
      ∃ (Craw Cphys rho : ℝ) (distance : ℕ → ℕ),
        0 ≤ Craw ∧
        0 ≤ Cphys ∧
        0 ≤ rho ∧
        rho < 1 ∧
        (∀ n, n ≤ distance n) ∧
        (∀ n,
          ‖physicalYangMillsSU2AdjacentFineFrozenStepSelectedVector
                Q R n r k -
              candidate n
                (physicalYangMillsSU2AdjacentFineFrozenStepSelectedVector
                  Q R n r k)‖ ^ 2 ≤
            Craw * (rho ^ distance n / (1 - rho))) ∧
        ∀ n,
          let Cn :=
            physicalYangMillsSU2AdjacentCommonRightSelectedCandidate
              Q R n (candidate n)
          let Y :=
            physicalYangMillsSU2AdjacentCommonFineFrozenStepVector
              Q R n r k
          ‖Cn Y -
              physicalYangMillsSU2AdjacentCommonLeftPhysicalRangeProjection
                Q R n (Cn Y)‖ ^ 2 ≤
            Cphys * (rho ^ distance n / (1 - rho))

namespace PhysicalYangMillsSU2AdjacentRightSelectedConditionalPhysicalityTailInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentRightSelectedConditionalPhysicalityTailInput
        (Q := Q) (R := R))

include G

/-- Transport the fine selected-marginal candidate into the exact common-
marginal split package from #5129.  The raw tail is transferred with no loss. -/
noncomputable def toCommonConditionalPhysicalityTailInput :
    PhysicalYangMillsSU2AdjacentCommonConditionalPhysicalityTailInput
      (Q := Q) (R := R) where
  candidate := fun n =>
    physicalYangMillsSU2AdjacentCommonRightSelectedCandidate
      Q R n (G.candidate n)
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
        physicalYangMillsSU2AdjacentCommonRightSelectedCandidateResidual_sq_eq_selected
          Q R n r k (G.candidate n)]
      exact hRaw n
    · intro n
      simpa only using hPhys n

/-- The selected-marginal raw conditional tail plus the common physicality tail
already generate the #5123 total reconstruction-variance tail. -/
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
    PhysicalYangMillsSU2AdjacentCommonConditionalPhysicalityTailInput.totalVariance_tail
      Q R (toCommonConditionalPhysicalityTailInput Q R G) r k

/-- Final receiver at the fine selected-marginal layer. -/
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
    PhysicalYangMillsSU2AdjacentCommonConditionalPhysicalityTailInput.orbitMismatch_summable
      Q R
      (toCommonConditionalPhysicalityTailInput Q R G)
      physicalCommutation_geometric betaMajorant_geometric r k

end PhysicalYangMillsSU2AdjacentRightSelectedConditionalPhysicalityTailInput

end RightSelectedConditionalTransport

end

end MathlibAnalytic
end MGAP4D
