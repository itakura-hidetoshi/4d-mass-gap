import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5SU2NoGo
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairIndependentGaugeFixedEquality
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairFixedSpaceCharacterization
import Mathlib.Tactic

/-!
# Positive-coupling SU(2) no-go for the old vacuum/top alignment route

The completed H1-D5 compatibility is now theorem-level false at positive SU(2)
coupling.  Because the canonical-sign vacuum-normalized OS vacuum pair is
already in the physical pair carrier (#5029), alignment of that vacuum with the
physical pair top line would force normalized physical-pair transfer fixedness.

The completed OS boundary transfer fixes the same finite OS vacuum
automatically.  Therefore vacuum/top alignment would imply the old completed
H1-D5 compatibility.

Combining this converse implication with #5061 shows that the old vacuum/top
alignment itself is impossible whenever the coupling is strictly positive at
some finite scale.

This excludes returning to the pre-#5061 alignment route and justifies the
weaker excitation-level scalar replacement introduced after the no-go.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance vacuumTopNoGoTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance vacuumTopNoGoCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance vacuumTopNoGoSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance vacuumTopNoGoMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance vacuumTopNoGoBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance vacuumTopNoGoSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance vacuumTopNoGoSpatialHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section VacuumTopAlignmentImpliesCompatibility

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta
        Q.vacuumNormalized.toWeakStarBridge hInvariant)

/-- For the canonical-sign vacuum-normalized finite OS vacuum pair, top-line
alignment implies the old completed H1-D5 compatibility.

The implication uses only:
1. H1-D4/#5029 physical-pair membership of the vacuum;
2. the fixed-space characterization of normalized physical pair transfer;
3. automatic vacuum fixedness of completed OS boundary transfer. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_of_vacuumPairTopAlignment
    (hAlign :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairTopAlignment
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant)) :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C := by
  intro n
  let vac :=
    physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n
  have hCarrier :
      vac ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) N := by
    simpa [vac] using
      physicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumBoundaryPairL2_mem_physicalPairCarrier
        Q hInvariant n
  have hTop :
      vac ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
        (halfExtent n) N hN (beta n) (hbeta n) := by
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_eq_span_pairTopMode
        (halfExtent n) N hN (beta n) (hbeta n)]
    simpa [vac] using hAlign n
  have hPhysicalFixed :
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n) vac =
        vac := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_fixed_iff_mem_topTopBlockClosure
        (halfExtent n) N hN (beta n) (hbeta n) vac hCarrier).2 hTop
  have hOSFixed :
      periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
          (halfExtent n) N
          (Q.vacuumNormalized.completedBoundaryTransfer hInvariant C n 2)
          vac =
        vac := by
    simpa [vac] using
      (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2_completedBoundaryPairTransfer_fixed
        (Q := Q.vacuumNormalized) C n 2)
  calc
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n) vac =
      vac := hPhysicalFixed
    _ =
      periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
        (halfExtent n) N
        (Q.vacuumNormalized.completedBoundaryTransfer hInvariant C n 2)
        vac := hOSFixed.symm

end VacuumTopAlignmentImpliesCompatibility

private theorem vacuumTopNoGoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance vacuumTopNoGoNontrivialSU2 :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section SU2VacuumTopAlignmentNoGo

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 vacuumTopNoGoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 vacuumTopNoGoRankPositive beta hbeta
        Q.vacuumNormalized.toWeakStarBridge hInvariant)

/-- A strictly positive coupling at one finite scale excludes the old global
vacuum/top alignment condition. -/
include C in
theorem
    physicalYangMillsVacuumNormalizedSU2TwoMode_not_vacuumPairTopAlignment_of_pos
    (n : ℕ)
    (hpos : 0 < beta n) :
    ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairTopAlignment
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := 2) (hN := vacuumTopNoGoRankPositive)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) := by
  intro hAlign
  apply
    physicalYangMillsVacuumNormalizedSU2TwoMode_not_completedCompatibility_of_pos
      Q hInvariant C n hpos
  exact
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_of_vacuumPairTopAlignment
      Q hInvariant C hAlign

/-- Equivalently, if the coupling is positive at some finite scale, the old
vacuum/top alignment route is globally impossible. -/
include C in
theorem
    physicalYangMillsVacuumNormalizedSU2TwoMode_not_vacuumPairTopAlignment_of_exists_pos
    (hpos : ∃ n : ℕ, 0 < beta n) :
    ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairTopAlignment
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := 2) (hN := vacuumTopNoGoRankPositive)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) := by
  rcases hpos with ⟨n, hn⟩
  exact
    physicalYangMillsVacuumNormalizedSU2TwoMode_not_vacuumPairTopAlignment_of_pos
      Q hInvariant C n hn

end SU2VacuumTopAlignmentNoGo

end

end MathlibAnalytic
end MGAP4D
