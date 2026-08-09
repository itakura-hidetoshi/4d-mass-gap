import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableCenteredPhysicalExcitationOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

noncomputable section

open Function Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

namespace DenseIsometricCoreOperatorCompletion

variable
    {E H : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Symmetry on a norm-preserving dense represented core extends uniquely to
symmetry of the completed bounded operator.

The core itself need not be declared as a Hilbert space.  The hypothesis is
stated directly in the ambient inner product, which is exactly the form needed
for OS null-quotient carrier cores. -/
theorem completedOperator_isSymmetric
    (e : E →ₗ[ℝ] H)
    (hDense : DenseRange e)
    (hIsometry : ∀ x : E, ‖e x‖ = ‖x‖)
    (T : E →L[ℝ] E)
    (hCore : ∀ x y : E,
      inner ℝ (e (T x)) (e y) = inner ℝ (e x) (e (T y))) :
    (completedOperator e T).IsSymmetric := by
  intro x y
  refine hDense.induction_on₂ ?_ ?_ x y
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro u v
    change
      inner ℝ (completedOperator e T (e u)) (e v) =
        inner ℝ (e u) (completedOperator e T (e v))
    rw [completedOperator_on_core e hDense hIsometry T u,
      completedOperator_on_core e hDense hIsometry T v]
    exact hCore u v

end DenseIsometricCoreOperatorCompletion

local instance actualExcitationSymmetrySideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance actualExcitationSymmetrySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance actualExcitationSymmetrySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance actualExcitationSymmetrySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance actualExcitationSymmetrySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance actualExcitationSymmetrySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

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

/-- The actual integer one-step Wilson translation is symmetric after
restriction to the centered carrier and representation in the completed
vacuum-orthogonal Hilbert space.

The only dynamical input is the theorem-generated finite OS exchange identity
`realizableCarrierTranslation_inner_symmetric`; no positivity or spectral
certificate is assumed. -/
theorem centeredOneStepOperator_represented_inner_symmetric
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F G :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let hPn : Pn.IsNormalized :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    inner ℝ
        (Pn.centeredPhysicalStateLinearMap hPn (A.centeredOneStepOperator n F))
        (Pn.centeredPhysicalStateLinearMap hPn G) =
      inner ℝ
        (Pn.centeredPhysicalStateLinearMap hPn F)
        (Pn.centeredPhysicalStateLinearMap hPn (A.centeredOneStepOperator n G)) := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  have hleft :
      inner ℝ
          (Pn.centeredPhysicalStateLinearMap hPn (A.centeredOneStepOperator n F))
          (Pn.centeredPhysicalStateLinearMap hPn G) =
        inner ℝ (A.centeredOneStepOperator n F) G := by
    change
      inner ℝ
          (Pn.physicalState
            ((A.centeredOneStepOperator n F : Pn.CenteredCarrier) : Pn.Carrier))
          (Pn.physicalState (G : Pn.Carrier)) =
        inner ℝ
          ((A.centeredOneStepOperator n F : Pn.CenteredCarrier) : Pn.Carrier)
          (G : Pn.Carrier)
    exact Pn.inner_physicalState_physicalState
      ((A.centeredOneStepOperator n F : Pn.CenteredCarrier) : Pn.Carrier)
      (G : Pn.Carrier)
  have hright :
      inner ℝ
          (Pn.centeredPhysicalStateLinearMap hPn F)
          (Pn.centeredPhysicalStateLinearMap hPn (A.centeredOneStepOperator n G)) =
        inner ℝ F (A.centeredOneStepOperator n G) := by
    change
      inner ℝ
          (Pn.physicalState (F : Pn.Carrier))
          (Pn.physicalState
            ((A.centeredOneStepOperator n G : Pn.CenteredCarrier) : Pn.Carrier)) =
        inner ℝ
          (F : Pn.Carrier)
          ((A.centeredOneStepOperator n G : Pn.CenteredCarrier) : Pn.Carrier)
    exact Pn.inner_physicalState_physicalState
      (F : Pn.Carrier)
      ((A.centeredOneStepOperator n G : Pn.CenteredCarrier) : Pn.Carrier)
  have hcarrier :
      inner ℝ (A.centeredOneStepOperator n F) G =
        inner ℝ F (A.centeredOneStepOperator n G) := by
    change
      inner ℝ
          (R.realizableCarrierTranslation hInvariant n 1 (F : Pn.Carrier))
          (G : Pn.Carrier) =
        inner ℝ
          (F : Pn.Carrier)
          (R.realizableCarrierTranslation hInvariant n 1 (G : Pn.Carrier))
    exact R.realizableCarrierTranslation_inner_symmetric hInvariant n 1
      (F : Pn.Carrier) (G : Pn.Carrier)
  exact hleft.trans (hcarrier.trans hright.symm)

/-- The **actual completed finite Wilson excitation one-step operator** is
symmetric on `Ωₙ⊥`.

This is the completed-Hilbert consequence of finite OS stationarity plus
reflection reversal.  It introduces no positivity field and no mass input. -/
theorem physicalExcitationOneStepOperator_isSymmetric
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    (A.physicalExcitationOneStepOperator n).IsSymmetric := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  change
    (DenseIsometricCoreOperatorCompletion.completedOperator
      (Pn.centeredPhysicalStateLinearMap hPn)
      (A.centeredOneStepOperator n)).IsSymmetric
  exact DenseIsometricCoreOperatorCompletion.completedOperator_isSymmetric
    (Pn.centeredPhysicalStateLinearMap hPn)
    (Pn.centeredPhysicalStateLinearMap_denseRange hPn)
    (Pn.norm_centeredPhysicalStateLinearMap hPn)
    (A.centeredOneStepOperator n)
    (A.centeredOneStepOperator_represented_inner_symmetric n)

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

end MathlibAnalytic
end MGAP4D

end