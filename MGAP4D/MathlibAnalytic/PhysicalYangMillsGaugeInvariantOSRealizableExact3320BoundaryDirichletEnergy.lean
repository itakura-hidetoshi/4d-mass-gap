import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableExact3320GeometricDirichletGap
import Mathlib.Tactic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableBoundaryDirichletEnergySideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableBoundaryDirichletEnergySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableBoundaryDirichletEnergySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableBoundaryDirichletEnergySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableBoundaryDirichletEnergySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableBoundaryDirichletEnergySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The OS seminorm square of every actual finite Wilson carrier is literally
the shared-boundary Haar integral of the squared boundary Gram moment.

This is a theorem, not an extra integrability assumption: OS quadratic value,
the actual finite reflected Gibbs integral, and the boundary Gram factorization
are all already identified upstream. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_carrier_norm_sq_eq_boundaryMoment_norm_sq_auto
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    ‖F‖ ^ 2 =
      ∫ b,
        ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  calc
    ‖F‖ ^ 2 = Pn.osQuadraticValue F :=
      (Pn.osQuadraticValue_eq_norm_sq F).symm
    _ = physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n F :=
      physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n F
    _ = ∫ b,
        ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) :=
      physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq_auto
        S D halfExtent N hN beta hbeta B hInvariant n F

/-- Literal compact-Haar shared-boundary Dirichlet energy of a centered carrier
at one geometric lattice step.  It is the norm-square loss of the actual
boundary Gram moment under the realizable Euclidean translation. -/
def physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredBoundaryDirichletEnergy
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
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) : ℝ :=
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let Fc := Pn.vacuumCenteredCarrier F
  (∫ b,
      ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc b‖ ^ 2
      ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) -
    ∫ b,
      ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        (R.realizableCarrierTranslation hInvariant n 1 Fc) b‖ ^ 2
      ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)

/-- The abstract OS two-step geometric defect is exactly the literal boundary
Haar Dirichlet energy.  The key identity is
`‖T₁ F‖² = ⟪F,T₂F⟫`; both norm squares are then replaced by their actual Wilson
boundary Gram-moment integrals. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_centered_geometricDirichlet_eq_boundaryDirichletEnergy
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
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let Fc := Pn.vacuumCenteredCarrier F
    inner ℝ Fc Fc -
        inner ℝ Fc (R.realizableCarrierTranslation hInvariant n 2 Fc) =
      physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredBoundaryDirichletEnergy
        S D halfExtent N hN beta hbeta Q E R hInvariant n F := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let Fc := Pn.vacuumCenteredCarrier F
  let F1 := R.realizableCarrierTranslation hInvariant n 1 Fc
  have hdouble :=
    R.realizableCarrierTranslation_one_norm_sq_eq_inner_two hInvariant n Fc
  have hnorm0 :=
    physical_yang_mills_evenPeriodicWilsonOS_carrier_norm_sq_eq_boundaryMoment_norm_sq_auto
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc
  have hnorm1 :=
    physical_yang_mills_evenPeriodicWilsonOS_carrier_norm_sq_eq_boundaryMoment_norm_sq_auto
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F1
  change
    inner ℝ Fc Fc - inner ℝ Fc
        (R.realizableCarrierTranslation hInvariant n 2 Fc) = _
  rw [real_inner_self_eq_norm_sq, ← hdouble]
  change ‖Fc‖ ^ 2 - ‖F1‖ ^ 2 = _
  rw [hnorm0, hnorm1]
  rfl

/-- Exact `33/20` quantitative input written entirely as a Poincaré inequality
for the literal compact-Haar boundary Dirichlet energy. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320BoundaryDirichletGapCertificate
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
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  centered_boundary_poincare :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      let Fc := Pn.vacuumCenteredCarrier F
      physicalYangMillsExact3320TwoStepDirichletDefect S n *
          (∫ b,
            ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
              S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc b‖ ^ 2
            ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) ≤
        physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredBoundaryDirichletEnergy
          S D halfExtent N hN beta hbeta Q E R hInvariant n F

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320BoundaryDirichletGapCertificate

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

/-- Boundary Poincaré coercivity reconstructs the geometric OS Dirichlet
certificate with no loss of constants. -/
noncomputable def toGeometricDirichletGapCertificate
    (B : PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320BoundaryDirichletGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320GeometricDirichletGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  twoStep_centered_dirichlet_coercivity := by
    intro n F
    dsimp only
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let Fc := Pn.vacuumCenteredCarrier F
    have h := B.centered_boundary_poincare n F
    dsimp only at h
    rw [physical_yang_mills_evenPeriodicWilsonOS_carrier_norm_sq_eq_boundaryMoment_norm_sq_auto
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc]
    rw [physical_yang_mills_evenPeriodicWilsonOS_centered_geometricDirichlet_eq_boundaryDirichletEnergy
      R hInvariant n F]
    exact h

/-- Therefore the literal compact-Haar boundary Poincaré estimate generates the
exact centered one-step Wilson contraction and all downstream gap machinery. -/
noncomputable def toOneStepExact3320GapCertificate
    (B : PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320BoundaryDirichletGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant :=
  B.toGeometricDirichletGapCertificate.toOneStepExact3320GapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320BoundaryDirichletGapCertificate

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320GeometricDirichletGapCertificate

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

/-- Conversely, geometric OS Dirichlet coercivity is exactly the same boundary
Poincaré inequality after theorem-generated Wilson Gram factorization. -/
noncomputable def toBoundaryDirichletGapCertificate
    (C : PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320GeometricDirichletGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320BoundaryDirichletGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  centered_boundary_poincare := by
    intro n F
    dsimp only
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let Fc := Pn.vacuumCenteredCarrier F
    have h := C.twoStep_centered_dirichlet_coercivity n F
    dsimp only at h
    rw [physical_yang_mills_evenPeriodicWilsonOS_carrier_norm_sq_eq_boundaryMoment_norm_sq_auto
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc] at h
    rw [physical_yang_mills_evenPeriodicWilsonOS_centered_geometricDirichlet_eq_boundaryDirichletEnergy
      R hInvariant n F] at h
    exact h

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320GeometricDirichletGapCertificate

end MathlibAnalytic
end MGAP4D

end