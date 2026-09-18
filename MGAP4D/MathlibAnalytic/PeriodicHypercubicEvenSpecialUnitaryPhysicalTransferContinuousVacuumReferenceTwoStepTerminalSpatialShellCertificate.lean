import MGAP4D.MathlibAnalytic.FiniteSpatialShellSummability
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoStepTerminalResidualCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance twoStepTerminalSpatialShellSpecialUnitaryIsTopologicalGroup
    (N : Nat) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance twoStepTerminalSpatialShellSpecialUnitaryCompactSpace
    (N : Nat) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupCompactSpace N

local instance twoStepTerminalSpatialShellSpecialUnitarySecondCountableTopology
    (N : Nat) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupSecondCountableTopology N

local instance twoStepTerminalSpatialShellSpecialUnitaryMeasurableSpace
    (N : Nat) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupMeasurableSpace N

local instance twoStepTerminalSpatialShellSpecialUnitaryBorelSpace
    (N : Nat) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupBorelSpace N

local instance twoStepTerminalSpatialShellSpatialLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance twoStepTerminalSpatialShellSpatialLinkNonempty
    (H : Nat) : Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) :=
  ⟨(⟨(0 : PeriodicHypercubicEvenVertex H), by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
    ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩

/-- The infinite shell mass associated with pointwise terminal decay
`C * q^radius` and a volume-independent shell-cardinality majorant. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialShellMass
    (C q : Real) (shellCardMajorant : Nat -> Real) : Real :=
  ∑' r : Nat, shellCardMajorant r * (C * q ^ r)

/-- A model-specific interface separating the two remaining ingredients for
uniform two-step terminal summability.

For every finite volume, background and physical source one supplies a radius
function and a finite local cutoff.  Geometry is recorded only by the
volume-independent shell-cardinality majorant; analysis is recorded only by
the pointwise terminal response decay `C * q^radius`. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteSpatialShellDecayBound
    (N : Nat) (hN : 0 < N) (beta : Real) (hbeta : 0 <= beta)
    (C q : Real) (shellCardMajorant : Nat -> Real) : Prop :=
  forall H : Nat,
    forall B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      forall source : PeriodicHypercubicEvenSpatialSliceLink H,
        exists radius : PeriodicHypercubicEvenSpatialSliceLink H -> Nat,
          exists cutoff : Nat,
            (forall target,
              target ∈
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
                    H source source ->
                radius target < cutoff) /\
            (forall r, r < cutoff ->
              (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
                    H source source).filter
                  (fun target => radius target = r)).card : Real) <=
                shellCardMajorant r) /\
            (forall target,
              target ∈
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
                    H source source ->
                forall g1 g2 h k : Matrix.specialUnitaryGroup (Fin N) Complex,
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs
                      H N hN beta hbeta B target source g1 g2 h k <=
                    C * q ^ radius target)

/-- A uniform pointwise spatial terminal decay bound plus a summable shell
cardinality profile produces the exact terminal-envelope certificate required
by the current two-step residual reduction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteSpatialShellDecayBound_to_terminalRemoteUniformBound
    (N : Nat) (hN : 0 < N) (beta : Real) (hbeta : 0 <= beta)
    (C q : Real) (shellCardMajorant : Nat -> Real)
    (hC : 0 <= C)
    (hq : 0 <= q)
    (hShellCardMajorantNonneg : forall r, 0 <= shellCardMajorant r)
    (hSummable :
      Summable (fun r : Nat =>
        shellCardMajorant r * (C * q ^ r)))
    (hSpatial :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteSpatialShellDecayBound
        N hN beta hbeta C q shellCardMajorant) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteUniformBound
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialShellMass
        C q shellCardMajorant) := by
  intro H B source
  rcases hSpatial H B source with
    ⟨radius, cutoff, hRadius, hShellCard, hPointwise⟩
  let terminal : PeriodicHypercubicEvenSpatialSliceLink H -> Real :=
    fun target => C * q ^ radius target
  refine ⟨terminal, ?_, ?_, ?_⟩
  · intro target hTarget
    simp only [terminal]
    exact mul_nonneg hC (pow_nonneg hq _)
  · intro target hTarget g1 g2 h k
    simpa [terminal] using
      hPointwise target hTarget g1 g2 h k
  · have hSum :=
      finiteRealSum_le_tsum_of_pointwiseDecay_shellCardinality
        (s :=
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
            H source source)
        (radius := radius)
        (cutoff := cutoff)
        (f := terminal)
        (C := C)
        (q := q)
        (shellCardMajorant := shellCardMajorant)
        hRadius
        hC
        hq
        hShellCardMajorantNonneg
        (by
          intro target hTarget
          simp [terminal])
        hShellCard
        hSummable
    simpa [
      terminal,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialShellMass] using
      hSum

/-- The spatial-shell certificate therefore discharges the uniform remote
residual certificate with the explicit two-step transport plus shell mass.
No identification with the older dense path-tail machinery is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteSpatialShellDecayBound_to_remoteResidualUniformBound
    (N : Nat) (hN : 0 < N) (beta : Real) (hbeta : 0 <= beta)
    (C q : Real) (shellCardMajorant : Nat -> Real)
    (hC : 0 <= C)
    (hq : 0 <= q)
    (hShellCardMajorantNonneg : forall r, 0 <= shellCardMajorant r)
    (hSummable :
      Summable (fun r : Nat =>
        shellCardMajorant r * (C * q ^ r)))
    (hSpatial :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteSpatialShellDecayBound
        N hN beta hbeta C q shellCardMajorant) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualUniformBound
      N hN beta hbeta
      (Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
            beta +
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialShellMass
            C q shellCardMajorant)) := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteUniformBound_to_remoteResidualUniformBound
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialShellMass
        C q shellCardMajorant)
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteSpatialShellDecayBound_to_terminalRemoteUniformBound
      N hN beta hbeta C q shellCardMajorant
      hC hq hShellCardMajorantNonneg hSummable hSpatial

end

end MathlibAnalytic
end MGAP4D
