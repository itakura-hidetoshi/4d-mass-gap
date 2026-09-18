import MGAP4D.MathlibAnalytic.FiniteExponentialShellGeometricBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicL1SpatialCovariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoStepTerminalSpatialShellCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance twoStepTerminalExponentialShellSpecialUnitaryIsTopologicalGroup
    (N : Nat) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance twoStepTerminalExponentialShellSpecialUnitaryCompactSpace
    (N : Nat) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupCompactSpace N

local instance twoStepTerminalExponentialShellSpecialUnitarySecondCountableTopology
    (N : Nat) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupSecondCountableTopology N

local instance twoStepTerminalExponentialShellSpecialUnitaryMeasurableSpace
    (N : Nat) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupMeasurableSpace N

local instance twoStepTerminalExponentialShellSpecialUnitaryBorelSpace
    (N : Nat) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupBorelSpace N

local instance twoStepTerminalExponentialShellSpatialLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance twoStepTerminalExponentialShellSpatialLinkNonempty
    (H : Nat) : Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) :=
  ⟨(⟨(0 : PeriodicHypercubicEvenVertex H), by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
    ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩

/-- Canonical spatial radius for the terminal problem: periodic L1 distance
between the base vertices of the embedded physical spatial links. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
    (H : Nat)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : Nat :=
  periodicHypercubicEdgeBaseL1Distance
    (PeriodicHypercubicEvenSideLength H)
    (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
    (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)

/-- Pure geometry certificate for exponential shell-cardinality growth on the
source-aligned remote set. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteExponentialShellGeometryBound
    (shellPrefactor shellGrowth : Real) : Prop :=
  forall H : Nat,
    forall source : PeriodicHypercubicEvenSpatialSliceLink H,
      exists cutoff : Nat,
        (forall target,
          target ∈
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
                H source source ->
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
                H target source < cutoff) /\
        (forall r, r < cutoff ->
          (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
                H source source).filter
              (fun target =>
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
                  H target source = r)).card : Real) <=
            shellPrefactor * shellGrowth ^ r)

/-- Pure analytic certificate for pointwise terminal decay in the same
canonical spatial base-L1 radius. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalResponseSpatialBaseL1DecayBound
    (N : Nat) (hN : 0 < N) (beta : Real) (hbeta : 0 <= beta)
    (terminalPrefactor terminalRatio : Real) : Prop :=
  forall H : Nat,
    forall B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      forall source target : PeriodicHypercubicEvenSpatialSliceLink H,
        target ∈
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
              H source source ->
          forall g1 g2 h k : Matrix.specialUnitaryGroup (Fin N) Complex,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs
                H N hN beta hbeta B target source g1 g2 h k <=
              terminalPrefactor *
                terminalRatio ^
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
                    H target source

/-- Explicit total terminal mass supplied by exponential shell growth against
faster exponential terminal decay. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellMass
    (shellPrefactor shellGrowth terminalPrefactor terminalRatio : Real) : Real :=
  shellPrefactor * terminalPrefactor /
    (1 - shellGrowth * terminalRatio)

/-- Separate geometric and analytic exponential certificates combine into the
uniform two-step terminal-envelope certificate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShell_to_terminalRemoteUniformBound
    (N : Nat) (hN : 0 < N) (beta : Real) (hbeta : 0 <= beta)
    (shellPrefactor shellGrowth terminalPrefactor terminalRatio : Real)
    (hShellPrefactor : 0 <= shellPrefactor)
    (hShellGrowth : 0 <= shellGrowth)
    (hTerminalPrefactor : 0 <= terminalPrefactor)
    (hTerminalRatio : 0 <= terminalRatio)
    (hProductLtOne : shellGrowth * terminalRatio < 1)
    (hGeometry :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteExponentialShellGeometryBound
        shellPrefactor shellGrowth)
    (hDecay :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalResponseSpatialBaseL1DecayBound
        N hN beta hbeta terminalPrefactor terminalRatio) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteUniformBound
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellMass
        shellPrefactor shellGrowth terminalPrefactor terminalRatio) := by
  intro H B source
  rcases hGeometry H source with ⟨cutoff, hRadius, hShell⟩
  let radius : PeriodicHypercubicEvenSpatialSliceLink H -> Nat :=
    fun target =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
        H target source
  let remote :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
      H source source
  let terminal : PeriodicHypercubicEvenSpatialSliceLink H -> Real :=
    fun target => terminalPrefactor * terminalRatio ^ radius target
  refine ⟨terminal, ?_, ?_, ?_⟩
  · intro target hTarget
    exact mul_nonneg hTerminalPrefactor (pow_nonneg hTerminalRatio _)
  · intro target hTarget g1 g2 h k
    simpa [terminal, radius] using
      hDecay H B source target (by simpa [remote] using hTarget) g1 g2 h k
  · have hShellEq :
        Finset.sum remote terminal =
          Finset.sum (Finset.range cutoff) (fun r =>
            Finset.sum (remote.filter (fun target => radius target = r)) terminal) := by
      exact
        finiteRealSum_eq_sum_radiusShells
          remote radius cutoff terminal
          (by
            intro target hTarget
            exact hRadius target (by simpa [remote] using hTarget))
    rw [hShellEq]
    calc
      Finset.sum (Finset.range cutoff) (fun r =>
          Finset.sum (remote.filter (fun target => radius target = r)) terminal) <=
        Finset.sum (Finset.range cutoff) (fun r =>
          (shellPrefactor * shellGrowth ^ r) *
            (terminalPrefactor * terminalRatio ^ r)) := by
        apply Finset.sum_le_sum
        intro r hr
        have hCard :
            (((remote.filter (fun target => radius target = r)).card : Nat) : Real) <=
              shellPrefactor * shellGrowth ^ r := by
          simpa [remote, radius] using hShell r (Finset.mem_range.mp hr)
        calc
          Finset.sum (remote.filter (fun target => radius target = r)) terminal =
              Finset.sum (remote.filter (fun target => radius target = r))
                (fun _target => terminalPrefactor * terminalRatio ^ r) := by
            apply Finset.sum_congr rfl
            intro target hTarget
            have hEq : radius target = r := (Finset.mem_filter.mp hTarget).2
            simp [terminal, hEq]
          _ =
              (((remote.filter (fun target => radius target = r)).card : Nat) : Real) *
                (terminalPrefactor * terminalRatio ^ r) := by
            simp [nsmul_eq_mul]
          _ <=
              (shellPrefactor * shellGrowth ^ r) *
                (terminalPrefactor * terminalRatio ^ r) :=
            mul_le_mul_of_nonneg_right hCard
              (mul_nonneg hTerminalPrefactor (pow_nonneg hTerminalRatio r))
      _ =
        (shellPrefactor * terminalPrefactor) *
          Finset.sum (Finset.range cutoff) (fun r =>
            (shellGrowth * terminalRatio) ^ r) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _hr
        rw [mul_pow]
        ring
      _ <=
        (shellPrefactor * terminalPrefactor) *
          (1 / (1 - shellGrowth * terminalRatio)) := by
        exact
          mul_le_mul_of_nonneg_left
            (FiniteDistanceShellGeometricSum.sum_range_pow_le_one_div_one_sub
              (shellGrowth * terminalRatio)
              (mul_nonneg hShellGrowth hTerminalRatio)
              hProductLtOne cutoff)
            (mul_nonneg hShellPrefactor hTerminalPrefactor)
      _ =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellMass
          shellPrefactor shellGrowth terminalPrefactor terminalRatio := by
        simp [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellMass,
          div_eq_mul_inv]

/-- The same separated geometry/analysis certificates discharge the current
uniform remote-residual obstruction with an explicit scalar rho. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShell_to_remoteResidualUniformBound
    (N : Nat) (hN : 0 < N) (beta : Real) (hbeta : 0 <= beta)
    (shellPrefactor shellGrowth terminalPrefactor terminalRatio : Real)
    (hShellPrefactor : 0 <= shellPrefactor)
    (hShellGrowth : 0 <= shellGrowth)
    (hTerminalPrefactor : 0 <= terminalPrefactor)
    (hTerminalRatio : 0 <= terminalRatio)
    (hProductLtOne : shellGrowth * terminalRatio < 1)
    (hGeometry :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteExponentialShellGeometryBound
        shellPrefactor shellGrowth)
    (hDecay :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalResponseSpatialBaseL1DecayBound
        N hN beta hbeta terminalPrefactor terminalRatio) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualUniformBound
      N hN beta hbeta
      (Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
            beta +
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellMass
            shellPrefactor shellGrowth terminalPrefactor terminalRatio)) := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteUniformBound_to_remoteResidualUniformBound
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellMass
        shellPrefactor shellGrowth terminalPrefactor terminalRatio)
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShell_to_terminalRemoteUniformBound
      N hN beta hbeta
      shellPrefactor shellGrowth terminalPrefactor terminalRatio
      hShellPrefactor hShellGrowth hTerminalPrefactor hTerminalRatio
      hProductLtOne hGeometry hDecay

end

end MathlibAnalytic
end MGAP4D
