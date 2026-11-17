import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2SameRootCompletedOSPeriodicGibbsCoefficientV5_PZ37AMQ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMR — exact control of the unchosen abstract OS semigroup

AMQ expresses the completed OS boundary time-two matrix coefficient as an
original same-root finite periodic Wilson Gibbs integral. However, its
positive-time translation is supplied by an *independently chosen* contractive
algebra semigroup C, not by the physical normalized one-slab Wilson kernel.

This unit makes that logical degree of freedom concrete. For every coherent
Wilson finite Gibbs pullback Q and reflection-invariant family, the constant
identity observable translation is itself a valid instance of the published
OS approximating semigroup interface, using no additional axioms or physical
model changes. The corresponding completed boundary transfer acts as identity
on all actual canonical OS boundary moments for *every* transfer time.

This is a control/obstruction theorem: it does not claim that the identity
semigroup is the physically intended Wilson time evolution, nor that the
normalized Wilson one-slab operator differs from identity. It shows why Q's
Gibbs measure plus the current generic semigroup interface cannot by
themselves **select** the genuine physical Wilson one-slab time action.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37AMR_sideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  change 2 * (H + 1) ≠ 0
  omega⟩
local instance p4Q2PZ37AMR_group (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2PZ37AMR_compact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2PZ37AMR_countable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2PZ37AMR_measurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2PZ37AMR_borel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Every coherent finite Wilson OS model Q admits the time-independent
identity semigroup as a valid *abstract* positive-time contraction semigroup.
No identification with a Wilson one-slab Haar integral is made. -/
noncomputable def p4Q2PZ37AMR_identityAbstractOSSemigroup
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant where
  translate := fun _ => AlgHom.id ℝ D.positiveTimeSubalgebra
  translate_zero := by rfl
  translate_add := by
    intro s t
    rfl
  osQuadratic_translate_le := by
    intro n t F
    let Pn := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    change Pn.osQuadraticValue
      (Pn.translateCarrierByPositiveTimeAlgHom
        (AlgHom.id ℝ D.positiveTimeSubalgebra) F) ≤
      Pn.osQuadraticValue F
    have hId :
        Pn.translateCarrierByPositiveTimeAlgHom
          (AlgHom.id ℝ D.positiveTimeSubalgebra) F = F := by
      change Pn.carrierOfPositiveTime (Pn.positiveTimeElement F) = F
      exact Pn.carrierOfPositiveTime_positiveTimeElement F
    exact le_of_eq (congrArg Pn.osQuadraticValue hId)

/-- On every genuine OS canonical boundary moment, the *completed* OS transfer
of the legitimate identity-semigroup control is exactly the identity at any
nonnegative boundary time.  This is not an assertion on the entire ambient
boundary Haar L2, where the completed operator may project onto ran J_n. -/
theorem p4Q2PZ37AMR_identityAbstractOS_completedBoundary_apply_canonicalMoment
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    Q.completedBoundaryTransfer hInvariant
        (p4Q2PZ37AMR_identityAbstractOSSemigroup Q hInvariant) n t
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F := by
  let Pn := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let C0 := p4Q2PZ37AMR_identityAbstractOSSemigroup Q hInvariant
  have hId :
      (C0.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
        (t / 2) F = F := by
    change Pn.carrierOfPositiveTime (Pn.positiveTimeElement F) = F
    exact Pn.carrierOfPositiveTime_positiveTimeElement F
  calc
    Q.completedBoundaryTransfer hInvariant C0 n t
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        ((C0.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
          (t / 2) F) := by
      exact Q.completedBoundaryTransfer_apply_canonicalBoundaryMoment
        hInvariant C0 n t F
    _ = _ := by rw [hId]

/-- Hence all ambient boundary-L2 test matrix coefficients of the identity
control equal their initial canonical moment coefficients, at every time.
The genuine physical Wilson coefficient from AMP is independently determined;
this theorem does not equate the two. -/
theorem p4Q2PZ37AMR_identityAbstractOS_completedBoundary_inner_canonicalMoment
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier)
    (z : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) :
    inner ℝ
      (Q.completedBoundaryTransfer hInvariant
        (p4Q2PZ37AMR_identityAbstractOSSemigroup Q hInvariant) n t
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F)) z =
      inner ℝ
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F) z := by
  rw [p4Q2PZ37AMR_identityAbstractOS_completedBoundary_apply_canonicalMoment
    Q hInvariant n t F]

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMR_identityAbstractOSSemigroup
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMR_identityAbstractOS_completedBoundary_apply_canonicalMoment
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMR_identityAbstractOS_completedBoundary_inner_canonicalMoment
