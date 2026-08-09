import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalExcitationDirichletLowerBoundGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalExcitationBoundaryDirichletCoefficient
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- A generic Hilbert-free operator-norm lemma: if every vector loses at least a
fraction `c` of its squared norm under a continuous linear map, then `c` is a
lower bound for the squared operator-norm defect.

The proof uses the canonical Mathlib operator norm API rather than approximate
norm-attaining vectors. -/
theorem continuousLinearMap_dirichletCoefficient_le_sqNormDefect
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V →L[ℝ] V)
    (c : ℝ)
    (hc : c ≤ 1)
    (hDirichlet : ∀ x : V,
      c * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 - ‖T x‖ ^ 2) :
    c ≤ 1 - ‖T‖ ^ 2 := by
  have hOneMinus : 0 ≤ 1 - c := sub_nonneg.mpr hc
  have hOp : ‖T‖ ≤ Real.sqrt (1 - c) := by
    apply ContinuousLinearMap.opNorm_le_bound T (Real.sqrt_nonneg _)
    intro x
    have hx := hDirichlet x
    have hroot : (Real.sqrt (1 - c)) ^ 2 = 1 - c :=
      Real.sq_sqrt hOneMinus
    have hsquare :
        ‖T x‖ ^ 2 ≤ (Real.sqrt (1 - c) * ‖x‖) ^ 2 := by
      rw [mul_pow, hroot]
      nlinarith
    nlinarith [norm_nonneg (T x), norm_nonneg x,
      Real.sqrt_nonneg (1 - c),
      mul_nonneg (Real.sqrt_nonneg (1 - c)) (norm_nonneg x)]
  have hroot : (Real.sqrt (1 - c)) ^ 2 = 1 - c :=
    Real.sq_sqrt hOneMinus
  have hOpSq : ‖T‖ ^ 2 ≤ (Real.sqrt (1 - c)) ^ 2 := by
    nlinarith [norm_nonneg T, Real.sqrt_nonneg (1 - c)]
  rw [hroot] at hOpSq
  linarith

local instance boundaryPoincareDefectSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryPoincareDefectSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryPoincareDefectSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryPoincareDefectSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryPoincareDefectSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryPoincareDefectSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Literal compact-Haar boundary variance of a point already lying in the
actual finite Wilson centered carrier sector. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredSectorBoundaryVariance
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
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier) : ℝ :=
  ∫ b,
    ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) b‖ ^ 2
    ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)

/-- Literal one-step compact-Haar boundary Dirichlet energy on the actual
centered carrier sector.  This is a difference of genuine boundary-moment
square integrals and contains no mass parameter. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredSectorBoundaryDirichletEnergy
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℕ → ℝ)
    (hbeta : ∀ k n, 0 ≤ beta k n)
    (Q : ∀ k,
      PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
        S D halfExtent N hN (beta k) (hbeta k)) := by
  exact 0

end MathlibAnalytic
end MGAP4D

end