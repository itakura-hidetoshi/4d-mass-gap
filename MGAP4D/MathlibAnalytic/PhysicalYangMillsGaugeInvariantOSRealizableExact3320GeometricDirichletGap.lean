import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSAdditiveSymmetricAction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableOneStepExact3320BoundaryMomentGap
import Mathlib.Tactic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableGeometricDirichletSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableGeometricDirichletSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableGeometricDirichletSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableGeometricDirichletSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableGeometricDirichletSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableGeometricDirichletSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Exact Poincaré/Dirichlet defect corresponding to one realizable lattice
step at mass `33/20`.

Because the one-step norm factor is `r_n = exp (-(33/20) a_n)`, the symmetric
OS identity naturally sees the doubled geometric step and the defect
`1-r_n²`. -/
def physicalYangMillsExact3320TwoStepDirichletDefect
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) (n : ℕ) : ℝ :=
  1 - (physicalYangMillsExact3320OneStepNormFactor S n) ^ 2

/-- The exact geometric Dirichlet defect is nonnegative. -/
theorem physicalYangMillsExact3320TwoStepDirichletDefect_nonneg
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) (n : ℕ) :
    0 ≤ physicalYangMillsExact3320TwoStepDirichletDefect S n := by
  unfold physicalYangMillsExact3320TwoStepDirichletDefect
  have h0 := (physicalYangMillsExact3320OneStepNormFactor_pos S n).le
  have h1 := physicalYangMillsExact3320OneStepNormFactor_le_one S n
  nlinarith

/-- The defect is exactly the exponential Poincaré defect at the doubled
lattice time `2 a_n`. -/
theorem physicalYangMillsExact3320TwoStepDirichletDefect_eq_exp
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) (n : ℕ) :
    physicalYangMillsExact3320TwoStepDirichletDefect S n =
      1 - Real.exp
        (-physicalYangMillsExact3320Mass * (2 * S.latticeSpacing n)) := by
  unfold physicalYangMillsExact3320TwoStepDirichletDefect
    physicalYangMillsExact3320OneStepNormFactor
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance

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

/-- The theorem-generated realizable Wilson carrier action, viewed only with
its additive law and OS inner symmetry.  No quantitative estimate is used. -/
noncomputable def toAdditiveSymmetricAction
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    Pn.AdditiveSymmetricAction ℕ := by
  dsimp only
  exact {
    translate := R.realizableCarrierTranslation hInvariant n
    translate_zero := R.realizableCarrierTranslation_zero hInvariant n
    translate_add := by
      intro k l F
      have h := R.realizableCarrierTranslation_add hInvariant n l k F
      simpa [Nat.add_comm] using h
    inner_symmetric := by
      intro k F G
      exact R.realizableCarrierTranslation_inner_symmetric hInvariant n k F G
  }

@[simp] theorem toAdditiveSymmetricAction_translate
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    (R.toAdditiveSymmetricAction hInvariant n).translate k F =
      R.realizableCarrierTranslation hInvariant n k F :=
  rfl

/-- Exact OS geometric identity at one and two realizable lattice steps:
`‖T_1 F‖² = ⟪F,T_2F⟫`. -/
theorem realizableCarrierTranslation_one_norm_sq_eq_inner_two
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    ‖R.realizableCarrierTranslation hInvariant n 1 F‖ ^ 2 =
      inner ℝ F (R.realizableCarrierTranslation hInvariant n 2 F) := by
  simpa using
    (R.toAdditiveSymmetricAction hInvariant n).norm_translate_sq_eq_inner_double
      (1 : ℕ) F

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance

/-- The exact quantitative finite Wilson input expressed as coercivity of the
**geometric Euclidean two-step defect**, not as heat-bath coercivity.

For every centered OS carrier state `F°`, the only field is

`(1-r_n²) ‖F°‖² ≤ ⟪F°,F°⟫ - ⟪F°,T_2 F°⟫`,

where `r_n = exp (-(33/20) a_n)` and `T_2` is the actual realizable geometric
Euclidean translation generated in #1483--#1484. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320GeometricDirichletGapCertificate
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
  twoStep_centered_dirichlet_coercivity :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      physicalYangMillsExact3320TwoStepDirichletDefect S n *
          ‖Pn.vacuumCenteredCarrier F‖ ^ 2 ≤
        inner ℝ (Pn.vacuumCenteredCarrier F) (Pn.vacuumCenteredCarrier F) -
          inner ℝ (Pn.vacuumCenteredCarrier F)
            (R.realizableCarrierTranslation hInvariant n 2
              (Pn.vacuumCenteredCarrier F))

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

/-- Geometric two-step Dirichlet coercivity is exactly sufficient to recover the
one-step norm certificate of #1485. -/
noncomputable def toOneStepExact3320GapCertificate
    (C : PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320GeometricDirichletGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  oneStep_centered_norm_le := by
    intro n F
    dsimp only
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let r := physicalYangMillsExact3320OneStepNormFactor S n
    let A := R.toAdditiveSymmetricAction hInvariant n
    have hr : 0 ≤ r :=
      (physicalYangMillsExact3320OneStepNormFactor_pos S n).le
    have hdir := C.twoStep_centered_dirichlet_coercivity n F
    dsimp only at hdir
    have h :=
      (A.norm_translate_le_iff_dirichlet_defect (1 : ℕ) r hr
        (Pn.vacuumCenteredCarrier F)).2 (by
          simpa [A, r,
            physicalYangMillsExact3320TwoStepDirichletDefect] using hdir)
    simpa [A, r] using h

/-- Hence the geometric Dirichlet package also generates the boundary-local
one-step exact `33/20` certificate from #1488. -/
noncomputable def toBoundaryMomentGapCertificate
    (C : PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320GeometricDirichletGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  oneStep_centered_boundaryMoment_le := by
    intro n F
    dsimp only
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let G := C.toOneStepExact3320GapCertificate
    have h := G.centered_finiteReflectedIntegral_le_pow_sq n 1 F
    rw [physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq_auto,
      physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq_auto] at h
    simpa using h

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320GeometricDirichletGapCertificate

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate

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

/-- Conversely, the #1485 one-step norm certificate automatically gives the
geometric doubled-step Dirichlet coercivity. -/
noncomputable def toGeometricDirichletGapCertificate
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320GeometricDirichletGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  twoStep_centered_dirichlet_coercivity := by
    intro n F
    dsimp only
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let r := physicalYangMillsExact3320OneStepNormFactor S n
    let A := R.toAdditiveSymmetricAction hInvariant n
    have hr : 0 ≤ r :=
      (physicalYangMillsExact3320OneStepNormFactor_pos S n).le
    have hstep := G.oneStep_centered_norm_le n F
    dsimp only at hstep
    have h :=
      (A.norm_translate_le_iff_dirichlet_defect (1 : ℕ) r hr
        (Pn.vacuumCenteredCarrier F)).1 (by
          simpa [A, r] using hstep)
    simpa [A, r,
      physicalYangMillsExact3320TwoStepDirichletDefect] using h

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryMomentGapCertificate

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

/-- The boundary Gram-moment certificate of #1488 and the geometric Dirichlet
coercivity certificate are theorem-equivalent. -/
noncomputable def toGeometricDirichletGapCertificate
    (B : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320GeometricDirichletGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant :=
  B.toOneStepExact3320GapCertificate.toGeometricDirichletGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryMomentGapCertificate

end MathlibAnalytic
end MGAP4D

end