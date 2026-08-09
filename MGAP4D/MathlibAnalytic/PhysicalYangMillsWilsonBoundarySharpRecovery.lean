import MGAP4D.MathlibAnalytic.RealSupremumSharpLowerInterval
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryOptimalMassToPhysical
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance wilsonBoundarySharpRecoverySideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance wilsonBoundarySharpRecoverySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance wilsonBoundarySharpRecoverySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance wilsonBoundarySharpRecoverySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance wilsonBoundarySharpRecoverySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance wilsonBoundarySharpRecoverySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer

set_option maxHeartbeats 800000

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}

/-- Sharp recovery criterion for equality of the intrinsic finite-Wilson
boundary mass and the actual continuum variational Yang--Mills mass.

It is enough that every nonnegative mass strictly below the continuum physical
mass be supported by the eventual literal compact-Haar Wilson boundary
Poincare inequality.  The endpoint itself need not be attained by any finite
certificate.

This is the natural variational/Mosco-style reverse direction: finite Wilson
boundary forms must recover every strict lower approximation to the continuum
Rayleigh edge. -/
theorem boundaryPoincareOptimalMass_eq_physicalYangMillsMass_of_all_strict_lower_admissible
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (hNonempty :
      (physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant).Nonempty)
    (hRecovery :
      ∀ m : ℝ,
        0 ≤ m →
        m < T.physicalYangMillsMass →
        m ∈
          physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
            S D halfExtent N hN beta hbeta Q E R hInvariant) :
    physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareOptimalMass
        S D halfExtent N hN beta hbeta Q E R hInvariant =
      T.physicalYangMillsMass := by
  unfold physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareOptimalMass
  apply real_csSup_eq_of_nonempty_nonneg_upper_of_all_lt_mem
  · exact hNonempty
  · intro m hm
    exact hm.1
  · intro m hm
    exact G.admissibleMass_le_physicalYangMillsMass hP W m hm
  · exact hRecovery

end PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer

/-- Proof-relevant statement of the remaining sharp finite-to-continuum
recovery obligation.

No numerical mass occurs.  The data say precisely that the actual finite Wilson
boundary problem is nonempty and recovers every strict lower approximation to
the continuum variational mass. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareSharpRecoveryData
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (B : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (P : D.OSPreHilbertData)
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T) where
  admissible_nonempty :
    (physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
      S D halfExtent N hN beta hbeta Q E R hInvariant).Nonempty
  all_strict_lower_admissible :
    ∀ m : ℝ,
      0 ≤ m →
      m < T.physicalYangMillsMass →
      m ∈
        physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
          S D halfExtent N hN beta hbeta Q E R hInvariant

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareSharpRecoveryData

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T}

/-- Sharp recovery identifies the two intrinsic masses exactly. -/
theorem boundaryPoincareOptimalMass_eq_physicalYangMillsMass
    (A : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareSharpRecoveryData
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T G)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareOptimalMass
        S D halfExtent N hN beta hbeta Q E R hInvariant =
      T.physicalYangMillsMass :=
  G.boundaryPoincareOptimalMass_eq_physicalYangMillsMass_of_all_strict_lower_admissible
    hP W A.admissible_nonempty A.all_strict_lower_admissible

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareSharpRecoveryData

end MathlibAnalytic
end MGAP4D

end