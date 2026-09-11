import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableExact3320GeometricDirichletGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableOneStepExact3320BoundaryL2TransferGap

noncomputable section

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableBoundaryL2DirichletSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableBoundaryL2DirichletSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableBoundaryL2DirichletSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableBoundaryL2DirichletSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableBoundaryL2DirichletSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableBoundaryL2DirichletSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2TransferGapCertificate

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

/-- The actual shared-boundary `L²` one-step transfer estimate of #1490 is
exactly sufficient to obtain the geometric Euclidean two-step Dirichlet
coercivity certificate.

The path is theorem-generated:
`boundary L² operator norm → boundary Gram-moment decay → one-step OS norm
contraction → symmetric doubled-step Dirichlet coercivity`.
No heat-bath generator or foreign finite-volume coercivity is used. -/
noncomputable def toGeometricDirichletGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320GeometricDirichletGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant :=
  A.toBoundaryMomentGapCertificate.toGeometricDirichletGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2TransferGapCertificate

end MathlibAnalytic
end MGAP4D

end
