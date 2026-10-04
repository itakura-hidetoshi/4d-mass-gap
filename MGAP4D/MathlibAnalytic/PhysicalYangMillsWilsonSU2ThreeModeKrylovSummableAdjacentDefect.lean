import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovFiniteMarginalCauchyDefect
import Mathlib.Tactic

/-!
# Reduce SU(2) Krylov Cauchy control to summable adjacent finite defects

PR #5096 reduces H1-C3 strong-limit existence to a tail-uniform finite
union-marginal Cauchy defect d_{n,j}^{m,k}.

That is still stronger than necessary. A standard metric-space criterion says
that if the consecutive distances are summable, then the sequence is Cauchy.

For the concrete SU(2) Krylov sequence, #5096 identifies each continuum
consecutive distance exactly with the finite union-marginal defect
d_{n,n+1}^{m,k}.

Therefore it is enough to prove, for every natural time m and basis mode k,

  Summable (fun n => d_{n,n+1}^{m,k}).

The existing Mathlib theorem cauchySeq_of_summable_dist then theorem-generates
the Krylov Cauchy property, the continuum mode by completeness, the three-mode
basis coherence, and all evolved strong limits with the already proved q0^m
bound.

This leaves a one-step refinement-error summability frontier.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2KrylovSummableAdjacentTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2KrylovSummableAdjacentCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2KrylovSummableAdjacentSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2KrylovSummableAdjacentMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2KrylovSummableAdjacentBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2KrylovSummableAdjacentSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2KrylovSummableAdjacentSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2KrylovSummableAdjacentNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section KrylovSummableAdjacent

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)

noncomputable def physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
    (n m : ℕ) (k : Fin 3) : ℝ :=
  physicalYangMillsSU2ThreeModeFiniteCommonMarginalKrylovDefect
    (Q := Q) (R := R) n (n + 1) m k

theorem physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_dist_succ_eq_finiteAdjacentKrylovDefect
    (n m : ℕ) (k : Fin 3) :
    dist
        (physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L n m k)
        (physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L (n + 1) m k) =
      physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
        (Q := Q) (R := R) n m k := by
  rw [dist_eq_norm]
  exact
    physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_sub_norm_eq_finiteCommonMarginalKrylovDefect
      Q R L n (n + 1) m k

structure PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput where
  adjacentDefect_summable :
    ∀ (m : ℕ) (k : Fin 3),
      Summable
        (fun n =>
          physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
            (Q := Q) (R := R) n m k)

namespace PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput

variable
    (C :
      PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput
        (Q := Q) (R := R))

include C

theorem krylov_cauchy
    (m : ℕ) (k : Fin 3) :
    CauchySeq
      (fun n =>
        physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L n m k) := by
  apply cauchySeq_of_summable_dist
  apply (C.adjacentDefect_summable m k).congr
  intro n
  exact
    (physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_dist_succ_eq_finiteAdjacentKrylovDefect
      Q R L n m k).symm

noncomputable def toFiniteMarginalKrylovCauchyInput :
    PhysicalYangMillsSU2ThreeModeFiniteMarginalKrylovCauchyInput
      (Q := Q) (R := R) where
  finiteDefect_tail := by
    intro m k ε hε
    have hcauchy := krylov_cauchy Q R L C m k
    rw [Metric.cauchySeq_iff] at hcauchy
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, ?_⟩
    intro n hn j hj
    have hdist := hN n hn j hj
    rw [dist_eq_norm] at hdist
    rw [
      physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_sub_norm_eq_finiteCommonMarginalKrylovDefect
        Q R L n j m k] at hdist
    exact hdist

noncomputable def continuumKrylovMode
    (m : ℕ) (k : Fin 3) :
    Lp ℝ 2 L.continuumMeasure :=
  PhysicalYangMillsSU2ThreeModeFiniteMarginalKrylovCauchyInput.continuumKrylovMode
    Q R L
    (toFiniteMarginalKrylovCauchyInput Q R L C)
    m k

theorem krylov_tendsto
    (m : ℕ) (k : Fin 3) :
    Tendsto
      (fun n =>
        physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L n m k)
      atTop
      (𝓝 (continuumKrylovMode Q R L C m k)) := by
  exact
    PhysicalYangMillsSU2ThreeModeFiniteMarginalKrylovCauchyInput.krylov_tendsto
      Q R L
      (toFiniteMarginalKrylovCauchyInput Q R L C)
      m k

noncomputable def toEvolvedBasisCoherenceInput :
    PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput
      Q R L :=
  PhysicalYangMillsSU2ThreeModeFiniteMarginalKrylovCauchyInput.toEvolvedBasisCoherenceInput
    Q R L
    (toFiniteMarginalKrylovCauchyInput Q R L C)

theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ cInf : EuclideanSpace ℝ (Fin 3),
        ‖cInf‖ = 1 ∧
        ∀ m : ℕ,
          Tendsto
            (fun j =>
              physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
                Q R L hInvariant (phi j) m)
            atTop
            (𝓝
              (PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                Q R L
                (toEvolvedBasisCoherenceInput Q R L C)
                m cInf)) := by
  exact
    PhysicalYangMillsSU2ThreeModeFiniteMarginalKrylovCauchyInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
      Q R L
      (toFiniteMarginalKrylovCauchyInput Q R L C)
      hInvariant

theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ cInf : EuclideanSpace ℝ (Fin 3),
        ‖cInf‖ = 1 ∧
        ∀ m : ℕ,
          Tendsto
              (fun j =>
                physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
                  Q R L hInvariant (phi j) m)
              atTop
              (𝓝
                (PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                  Q R L
                  (toEvolvedBasisCoherenceInput Q R L C)
                  m cInf)) ∧
            ‖PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                Q R L
                (toEvolvedBasisCoherenceInput Q R L C)
                m cInf‖ ≤
              GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  exact
    PhysicalYangMillsSU2ThreeModeFiniteMarginalKrylovCauchyInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
      Q R L
      (toFiniteMarginalKrylovCauchyInput Q R L C)
      hInvariant s hs hcut

end PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput

end KrylovSummableAdjacent

end

end MathlibAnalytic
end MGAP4D
