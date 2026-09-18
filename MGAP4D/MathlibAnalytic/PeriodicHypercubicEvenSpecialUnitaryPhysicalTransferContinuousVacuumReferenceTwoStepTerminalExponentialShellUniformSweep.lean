import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoStepTerminalExponentialShellCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance twoStepTerminalExponentialShellUniformSweepSpatialLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance twoStepTerminalExponentialShellUniformSweepSpatialLinkNonempty
    (H : Nat) : Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) :=
  ⟨(⟨(0 : PeriodicHypercubicEvenVertex H), by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
    ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩

/-- The explicit two-step represented-source transport coefficient is
nonnegative at nonnegative coupling. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient_nonneg
    (beta : Real) (hbeta : 0 <= beta) :
    0 <=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
        beta := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
  have hExp8 : 1 <= Real.exp (8 * beta) := by
    apply Real.one_le_exp
    nlinarith
  have hSq : 1 <= (Real.exp (8 * beta)) ^ 2 := by
    nlinarith [Real.exp_pos (8 * beta)]
  exact
    mul_nonneg
      (mul_nonneg (by norm_num)
        (div_nonneg (sub_nonneg.mpr hSq) (by positivity)))
      (mul_nonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence_nonneg
          beta hbeta)
        (Real.exp_pos (16 * beta)).le)

/-- The explicit exponential-shell terminal mass is nonnegative whenever the
shell/terminal prefactors are nonnegative and shellGrowth*terminalRatio<1. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellMass_nonneg
    (shellPrefactor shellGrowth terminalPrefactor terminalRatio : Real)
    (hShellPrefactor : 0 <= shellPrefactor)
    (hTerminalPrefactor : 0 <= terminalPrefactor)
    (hProductLtOne : shellGrowth * terminalRatio < 1) :
    0 <=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellMass
        shellPrefactor shellGrowth terminalPrefactor terminalRatio := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellMass
  exact
    div_nonneg
      (mul_nonneg hShellPrefactor hTerminalPrefactor)
      (sub_nonneg.mpr (le_of_lt hProductLtOne))

/-- Explicit residual scalar obtained by composing the two-step transport and
the exponential-shell terminal mass. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellResidualBound
    (beta shellPrefactor shellGrowth terminalPrefactor terminalRatio : Real) : Real :=
  Real.exp (16 * beta) *
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
        beta +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellMass
        shellPrefactor shellGrowth terminalPrefactor terminalRatio)

/-- The explicit exponential-shell residual scalar is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellResidualBound_nonneg
    (beta : Real) (hbeta : 0 <= beta)
    (shellPrefactor shellGrowth terminalPrefactor terminalRatio : Real)
    (hShellPrefactor : 0 <= shellPrefactor)
    (hTerminalPrefactor : 0 <= terminalPrefactor)
    (hProductLtOne : shellGrowth * terminalRatio < 1) :
    0 <=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellResidualBound
        beta shellPrefactor shellGrowth terminalPrefactor terminalRatio := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellResidualBound
  exact
    mul_nonneg
      (Real.exp_pos (16 * beta)).le
      (add_nonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient_nonneg
          beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellMass_nonneg
          shellPrefactor shellGrowth terminalPrefactor terminalRatio
          hShellPrefactor hTerminalPrefactor hProductLtOne))

/-- Exponential shell geometry plus pointwise terminal decay now reaches the
existing volume-uniform physical full-sweep contraction theorem through the
explicit residual scalar.

This remains a finite-volume physical influence-envelope statement with a
volume-independent sweep exponent. It is not a thermodynamic or continuum mass
gap statement. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShell_uniformFullSweepIterate_le_exp
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
        N hN beta hbeta terminalPrefactor terminalRatio)
    (hGate :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
        beta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellResidualBound
          beta shellPrefactor shellGrowth terminalPrefactor terminalRatio) < 1)
    (H : Nat)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H -> Real)
    (hVariationNonneg : forall e, 0 <= variation e)
    (bound : Real) (hBoundNonneg : 0 <= bound)
    (hVariationBound : forall e, variation e <= bound)
    (sweeps : Nat)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelRandomScanVariationIterate
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A)
        variation
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) * sweeps)
        source <=
      Real.exp
          (-(1 -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
                beta
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellResidualBound
                  beta shellPrefactor shellGrowth terminalPrefactor terminalRatio)) *
            (sweeps : Real)) *
        bound := by
  let rho :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellResidualBound
      beta shellPrefactor shellGrowth terminalPrefactor terminalRatio
  have hRho : 0 <= rho := by
    dsimp [rho]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellResidualBound_nonneg
        beta hbeta
        shellPrefactor shellGrowth terminalPrefactor terminalRatio
        hShellPrefactor hTerminalPrefactor hProductLtOne
  have hUniform :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualUniformBound
        N hN beta hbeta rho := by
    dsimp [rho]
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShellResidualBound] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalExponentialShell_to_remoteResidualUniformBound
        N hN beta hbeta
        shellPrefactor shellGrowth terminalPrefactor terminalRatio
        hShellPrefactor hShellGrowth hTerminalPrefactor hTerminalRatio
        hProductLtOne hGeometry hDecay
  have hSweep :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_uniformFullSweepIterate_le_exp
      N hN beta hbeta rho hRho hUniform
      (by simpa [rho] using hGate)
      H A variation hVariationNonneg bound hBoundNonneg hVariationBound sweeps source
  simpa [rho] using hSweep

end

end MathlibAnalytic
end MGAP4D
