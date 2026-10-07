import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentActualFrozenDirichletVacuumSplit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateMarginalGeometry
import Mathlib.Tactic

/-!
# Genuine joint L2 norm of the frozen vacuum posterior-mean carrier

The exact Leibniz/Dirichlet split of PRs #5257--#5258 involves both the
half-density W(C,B) and the frozen normalized-transfer posterior mean M(B).

For every genuine physical slice f, the joint BCF

  (C,B) |-> M_f(B)

is literally the right-boundary pullback of the vacuum-L2 receiver
constructed in PR #5255.  The ACTUAL ground-state joint measure has
right marginal equal to the ACTUAL physical vacuum measure, so this
right-boundary pullback is an isometry:

  ||M_f ∘ snd||_{L2(mu_joint)}
    = ||M_f||_{L2(mu_vac)}
    = ||S f||_{L2(Haar)}
    <= ||f||_{L2(Haar)}.

For the actual frozen adjacent orbit, both the mode-dependent left
factor and the common-right factor have norm at most one for every
finite depth r, retaining beta(n+1) in the orbit and beta(n) in the
frozen joint marginal.

This is genuinely an L2 statement; it does not assert
||M_f||_infty <= 1.  It prepares a later stationarity-weighted
replacement of the supremum coefficient in the Dirichlet Leibniz
estimate, without claiming such a replacement here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3FrozenJointMeanTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3FrozenJointMeanCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3FrozenJointMeanSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3FrozenJointMeanMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3FrozenJointMeanBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3FrozenJointMeanSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p3FrozenJointMeanJointProbability
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
    H N hN beta hbeta

local instance p3FrozenJointMeanVacuumProbability
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_isProbabilityMeasure
    H N hN beta hbeta

namespace GroundStatePosteriorJoint

/-- The genuine joint BCF class is exactly the old right-boundary isometry
applied to the vacuum posterior-mean L2 vector, not a new L2 construction. -/
theorem normalizedPhysicalOneSlabVacuumMeanJointBCF_toLp_eq_rightBoundaryIsometry
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)
        ℝ
        (normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
        H N hN beta hbeta
        (BoundedContinuousFunction.toLp
          2
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
            H N hN beta hbeta)
          ℝ
          (normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f)) := by
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let muJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let muV :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
      H N hN beta hbeta
  let M := normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f
  let MJ := normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f
  let u : Lp ℝ 2 muV := BoundedContinuousFunction.toLp 2 muV ℝ M
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
    H N hN beta hbeta
  let hSnd :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_snd_measurePreserving
      H N hN beta hbeta
  have hu :
      (fun B : X => u B) =ᵐ[muV] fun B => M B := by
    simpa [u] using BoundedContinuousFunction.coeFn_toLp 2 muV ℝ M
  have huComp :
      (fun z : X × X => u z.2) =ᵐ[muJ]
        fun z : X × X => M z.2 := by
    simpa only [Function.comp_apply] using
      hSnd.quasiMeasurePreserving.ae_eq_comp hu
  have hR :
      (fun z : X × X => (R u) z) =ᵐ[muJ]
        fun z : X × X => u z.2 := by
    change
      (fun z : X × X => (Lp.compMeasurePreserving Prod.snd hSnd u) z) =ᵐ[muJ]
        (fun z : X × X => u z.2)
    simpa only [Function.comp_apply] using
      Lp.coeFn_compMeasurePreserving u hSnd
  have hMJ :
      (fun z : X × X => (BoundedContinuousFunction.toLp 2 muJ ℝ MJ) z) =ᵐ[muJ]
        fun z : X × X => MJ z := by
    exact BoundedContinuousFunction.coeFn_toLp 2 muJ ℝ MJ
  change BoundedContinuousFunction.toLp 2 muJ ℝ MJ = R u
  apply Lp.ext
  filter_upwards [hMJ, hR, huComp] with z hzMJ hzR hzU
  rw [hzMJ, hzR, hzU]
  rfl

/-- Exact equality of the joint-L2 norm and the physical vacuum-L2 norm
from the true right-boundary marginal of the joint law. -/
theorem normalizedPhysicalOneSlabVacuumMeanJointBCF_toLp_norm_eq_vacuum
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)
        ℝ
        (normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f)‖ =
      ‖BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta)
        ℝ
        (normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f)‖ := by
  rw [normalizedPhysicalOneSlabVacuumMeanJointBCF_toLp_eq_rightBoundaryIsometry
    H N hN beta hbeta f]
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
      H N hN beta hbeta).norm_map _

/-- Joint-L2 norm equals the true normalized physical transfer image norm. -/
theorem normalizedPhysicalOneSlabVacuumMeanJointBCF_toLp_norm_eq_transfer
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)
        ℝ
        (normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f)‖ =
      ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta f‖ := by
  rw [normalizedPhysicalOneSlabVacuumMeanJointBCF_toLp_norm_eq_vacuum
    H N hN beta hbeta f]
  exact normalizedPhysicalOneSlabVacuumReceiverBCF_toLp_norm_eq
    H N hN beta hbeta f

/-- The true joint-L2 posterior-mean norm is controlled by the physical
input norm with coefficient one and no volume factor. -/
theorem normalizedPhysicalOneSlabVacuumMeanJointBCF_toLp_norm_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)
        ℝ
        (normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f)‖ ≤ ‖f‖ := by
  rw [normalizedPhysicalOneSlabVacuumMeanJointBCF_toLp_norm_eq_vacuum
    H N hN beta hbeta f]
  exact normalizedPhysicalOneSlabVacuumReceiverBCF_toLp_norm_le
    H N hN beta hbeta f

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive

/-- The actual mode-dependent fine left factor has vacuum-mean joint-L2
norm at most one, uniformly in its finite Krylov depth r. -/
theorem fineOrbitLeftFrozenPosteriorMeanJointL2_norm_le_one
    (k : Fin 3) :
    ‖BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          Hn 2 Pos (beta n) (hbeta n))
        ℝ
        (normalizedPhysicalOneSlabVacuumMeanJointBCF
          Hn 2 Pos (beta n) (hbeta n)
          (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k))‖ ≤ 1 := by
  have hBound := normalizedPhysicalOneSlabVacuumMeanJointBCF_toLp_norm_le
    Hn 2 Pos (beta n) (hbeta n)
    (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k)
  exact hBound.trans
    (fineOrbitLeftFactor_norm_le_one
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k)

/-- The actual common right factor obeys the same unit bound in the ORIGINAL
frozen joint law, even though its orbit was formed with beta(n+1). -/
theorem fineOrbitRightFrozenPosteriorMeanJointL2_norm_le_one :
    ‖BoundedContinuousFunction.toLp
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          Hn 2 Pos (beta n) (hbeta n))
        ℝ
        (normalizedPhysicalOneSlabVacuumMeanJointBCF
          Hn 2 Pos (beta n) (hbeta n)
          (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r))‖ ≤ 1 := by
  have hBound := normalizedPhysicalOneSlabVacuumMeanJointBCF_toLp_norm_le
    Hn 2 Pos (beta n) (hbeta n)
    (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r)
  exact hBound.trans
    (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor_norm_le_one
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r)

end ActualAdjacentOrbit
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
