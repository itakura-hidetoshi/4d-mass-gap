import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFrozenOrbitVacuumReceiverL2
import Mathlib.Tactic

/-!
# Exact half-density return from frozen vacuum receiver to joint Dirichlet input

PR #5255 constructs for any physical Haar-L2 slice f a bounded-continuous
frozen receiver

  M_f(B) = lambda^(-1) * integral K(A,B) f(A) dHaar(A) / Omega(B).

The genuine joint right-output factor still contains the full half-density.
For every physical slice f, this file proves the exact scalar equality

  rightOutput_f(C,B)
    = [lambda^(-1) * Omega(B) * M_f(B)] / sqrt(rho_joint(C,B)).

The inverse transfer norm and the vacuum factor must not be discarded.
The original signed right link defect is the difference of exactly these
half-density-weighted receivers before and after one coordinate update.
No output drift or source response is removed.

The actual adjacent orbit uses the frozen beta(n) receiver while its
physical input factors were evolved at beta(n+1). Both the mode-dependent
seed-right receiver and the common-right receiver are given the exact
half-density formula. This is an algebraic Dirichlet interface only:
vacuum-L2 control from PR #5255 is not asserted to bound its link variation
without the remaining half-density/variation estimates.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3FrozenHalfDensityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3FrozenHalfDensityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3FrozenHalfDensitySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3FrozenHalfDensityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3FrozenHalfDensityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3FrozenHalfDensitySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The joint half-density carrier of the general frozen vacuum receiver.
This is a literal real-valued function on the original ordered joint space,
not a new probability law or conditional expectation. -/
noncomputable def normalizedPhysicalOneSlabJointHalfDensityReceiver
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta z.2 *
      normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f z.2) /
    continuousJointSqrtDensity H N hN beta hbeta z

/-- Exact factorization of the genuine right-output scalar, keeping
both the physical norm and the joint square-root density. -/
theorem decomposableRightOutputFactor_eq_jointHalfDensityReceiver
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    decomposableRightOutputFactor H N hN beta hbeta f z =
      normalizedPhysicalOneSlabJointHalfDensityReceiver
        H N hN beta hbeta f z := by
  let lambda :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  let omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta z.2
  let integralValue :=
    decomposableOneSliceTransferIntegral H N beta
      (f :
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
      z.2
  have hlambda : lambda ≠ 0 := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta).ne'
  have homega : omega ≠ 0 := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta z.2).ne'
  have hScalar :
      (lambda ^ 2)⁻¹ * integralValue =
        lambda⁻¹ * omega * (lambda⁻¹ * integralValue / omega) := by
    field_simp [hlambda, homega] <;> ring
  change
    ((lambda ^ 2)⁻¹ * integralValue) /
        continuousJointSqrtDensity H N hN beta hbeta z =
      (lambda⁻¹ * omega * (lambda⁻¹ * integralValue / omega)) /
        continuousJointSqrtDensity H N hN beta hbeta z
  exact
    congrArg
      (fun v : ℝ => v / continuousJointSqrtDensity H N hN beta hbeta z)
      hScalar

/-- The already-constructed bounded joint observable has precisely this
half-density value; no new L2 representative is chosen. -/
theorem decomposableRightOutputBCF_apply_eq_jointHalfDensityReceiver
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    decomposableRightOutputBCF H N hN beta hbeta f z =
      normalizedPhysicalOneSlabJointHalfDensityReceiver
        H N hN beta hbeta f z := by
  rw [decomposableRightOutputBCF_apply]
  exact
    decomposableRightOutputFactor_eq_jointHalfDensityReceiver
      H N hN beta hbeta f z

/-- The complete signed right defect is the ordinary difference of the
half-density-corrected receiver at the original and updated output endpoints.
The original output drift and source response remain present. -/
theorem decomposableRightLinkDifferenceFactor_eq_jointHalfDensityReceiver_sub_update
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (u : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    decomposableRightLinkDifferenceFactor H N hN beta hbeta f e z u =
      normalizedPhysicalOneSlabJointHalfDensityReceiver
          H N hN beta hbeta f z -
        normalizedPhysicalOneSlabJointHalfDensityReceiver
          H N hN beta hbeta f (z.1, Function.update z.2 e u) := by
  rw [decomposableRightLinkDifferenceFactor_eq_outputBCF_sub_update]
  rw [
    decomposableRightOutputBCF_apply_eq_jointHalfDensityReceiver
      H N hN beta hbeta f z,
    decomposableRightOutputBCF_apply_eq_jointHalfDensityReceiver
      H N hN beta hbeta f (z.1, Function.update z.2 e u)
  ]

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2

/-- The mode-dependent original seed-right receiver on the unchanged
adjacent orbit is exactly the frozen half-density receiver. -/
theorem physicalYangMillsSU2AdjacentFineSeedRightBCF_apply_eq_jointHalfDensityReceiver
    (k : Fin 3) (z : Cfg × Cfg) :
    physicalYangMillsSU2AdjacentFineSeedRightBCF
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k z =
      normalizedPhysicalOneSlabJointHalfDensityReceiver
        Hn 2 Pos (beta n) (hbeta n)
        (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k) z := by
  change
    decomposableRightOutputBCF Hn 2 Pos (beta n) (hbeta n)
        (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k) z = _
  exact
    decomposableRightOutputBCF_apply_eq_jointHalfDensityReceiver
      Hn 2 Pos (beta n) (hbeta n)
      (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k) z

/-- The distinct mode-independent common-right BCF has the same exact
half-density presentation, using its actual evolved common-right factor. -/
theorem fineOrbitCommonRightBCF_apply_eq_jointHalfDensityReceiver
    (z : Cfg × Cfg) :
    fineOrbitCommonRightBCF
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r z =
      normalizedPhysicalOneSlabJointHalfDensityReceiver
        Hn 2 Pos (beta n) (hbeta n)
        (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) z := by
  change
    decomposableRightOutputBCF Hn 2 Pos (beta n) (hbeta n)
        (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) z = _
  exact
    decomposableRightOutputBCF_apply_eq_jointHalfDensityReceiver
      Hn 2 Pos (beta n) (hbeta n)
      (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) z

end ActualAdjacentOrbit

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
