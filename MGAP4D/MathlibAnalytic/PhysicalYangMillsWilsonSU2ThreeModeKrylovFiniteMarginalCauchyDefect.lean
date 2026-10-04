import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovFiniteMarginalPairCorrelation
import Mathlib.Tactic

/-!
# Reduce SU(2) Krylov strong limits to one finite-marginal Cauchy defect

PR #5095 rewrites every cross-scale continuum Krylov inner product inside one
common finite union marginal.

For existence of a strong limit, even the separate self-correlation and
pair-correlation scalar limits are unnecessary.  It is enough to prove directly
that the finite representatives are Cauchy after transport to a common union
marginal.

For finite marginals J and K and vectors f,g,

  ||pull_J f - pull_K g||
    =
  ||transition_{J→J∪K} f - transition_{K→J∪K} g||.

Thus the common-continuum Krylov sequence is Cauchy exactly when its canonical
finite union-marginal representatives are Cauchy.

This gives a very small H1-C3 frontier:

for each natural time m and each of the three basis modes k, prove that the
finite union-marginal transition defect tends uniformly to zero on tails.

Completeness of the projective continuum L2 carrier then theorem-generates the
three continuum Krylov modes, and #5091 supplies all evolved strong limits.
The #5084 q0^m estimate is inherited automatically.

No scalar limit, candidate continuum vector, global operator compatibility, or
cofinality assumption is needed for this strong-limit existence route.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

/-- Cross-scale continuum distance is exactly the finite union-marginal
transition distance. -/
theorem finiteMarginalL2Pullback_cross_norm_sub_eq_union_transition_norm_sub
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (J K : Finset EuclideanFourSpace)
    (f : Lp ℝ 2 (F.finiteMarginal J))
    (g : Lp ℝ 2 (F.finiteMarginal K)) :
    ‖L.finiteMarginalL2Pullback J f -
        L.finiteMarginalL2Pullback K g‖ =
      ‖EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F)
          (show J ⊆ J ∪ K from Finset.subset_union_left) f -
        EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F)
          (show K ⊆ J ∪ K from Finset.subset_union_right) g‖ := by
  rw [
    L.finiteMarginalL2Pullback_compatible
      (show J ⊆ J ∪ K from Finset.subset_union_left) f,
    L.finiteMarginalL2Pullback_compatible
      (show K ⊆ J ∪ K from Finset.subset_union_right) g]
  calc
    ‖L.finiteMarginalL2Pullback (J ∪ K)
          (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
            (F := F)
            (show J ⊆ J ∪ K from Finset.subset_union_left) f) -
        L.finiteMarginalL2Pullback (J ∪ K)
          (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
            (F := F)
            (show K ⊆ J ∪ K from Finset.subset_union_right) g)‖ =
      ‖L.finiteMarginalL2Pullback (J ∪ K)
          (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
              (F := F)
              (show J ⊆ J ∪ K from Finset.subset_union_left) f -
            EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
              (F := F)
              (show K ⊆ J ∪ K from Finset.subset_union_right) g)‖ := by
        rw [map_sub]
    _ =
      ‖EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F)
          (show J ⊆ J ∪ K from Finset.subset_union_left) f -
        EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F)
          (show K ⊆ J ∪ K from Finset.subset_union_right) g‖ :=
      L.finiteMarginalL2Pullback_norm (J ∪ K) _

local instance su2KrylovFiniteCauchyTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2KrylovFiniteCauchyCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2KrylovFiniteCauchySecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2KrylovFiniteCauchyMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2KrylovFiniteCauchyBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2KrylovFiniteCauchySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2KrylovFiniteCauchySpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance su2KrylovFiniteCauchyNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section KrylovFiniteCauchy

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

/-- Canonical finite union-marginal Cauchy defect of two scales. -/
noncomputable def physicalYangMillsSU2ThreeModeFiniteCommonMarginalKrylovDefect
    (n j m : ℕ) (k : Fin 3) : ℝ :=
  ‖EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
      (F := F)
      (show R.marginalIndex n ⊆ R.marginalIndex n ∪ R.marginalIndex j from
        Finset.subset_union_left)
      (physicalYangMillsSU2ThreeModeEvolvedFiniteMarginalKrylovMode
        Q R n m k) -
    EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
      (F := F)
      (show R.marginalIndex j ⊆ R.marginalIndex n ∪ R.marginalIndex j from
        Finset.subset_union_right)
      (physicalYangMillsSU2ThreeModeEvolvedFiniteMarginalKrylovMode
        Q R j m k)‖

/-- Exact identification of the common-continuum Krylov difference norm with
the finite union-marginal Cauchy defect. -/
theorem physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_sub_norm_eq_finiteCommonMarginalKrylovDefect
    (n j m : ℕ) (k : Fin 3) :
    ‖physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L n m k -
        physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L j m k‖ =
      physicalYangMillsSU2ThreeModeFiniteCommonMarginalKrylovDefect
        (Q := Q) (R := R) n j m k := by
  unfold physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
  rw [
    physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding_eq_finitePullback
      Q R L n
      ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) ^ m)
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
          (halfExtent n) k)),
    physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding_eq_finitePullback
      Q R L j
      ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent j) 2 specialUnitaryTwoWilsonRankPositive
          (beta j) (hbeta j) ^ m)
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
          (halfExtent j) k))]
  exact
    finiteMarginalL2Pullback_cross_norm_sub_eq_union_transition_norm_sub
      L
      (R.marginalIndex n)
      (R.marginalIndex j)
      (physicalYangMillsSU2ThreeModeEvolvedFiniteMarginalKrylovMode
        Q R n m k)
      (physicalYangMillsSU2ThreeModeEvolvedFiniteMarginalKrylovMode
        Q R j m k)

/-- Minimal H1-C3 strong-limit input: the three finite Krylov families are
Cauchy after canonical transport to the union finite marginal. -/
structure PhysicalYangMillsSU2ThreeModeFiniteMarginalKrylovCauchyInput where
  finiteDefect_tail :
    ∀ (m : ℕ) (k : Fin 3) (ε : ℝ), 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, N ≤ j →
        physicalYangMillsSU2ThreeModeFiniteCommonMarginalKrylovDefect
          (Q := Q) (R := R) n j m k < ε

namespace PhysicalYangMillsSU2ThreeModeFiniteMarginalKrylovCauchyInput

variable
    (C :
      PhysicalYangMillsSU2ThreeModeFiniteMarginalKrylovCauchyInput
        (Q := Q) (R := R))

include C

/-- Finite union-marginal defect control is exactly enough to make each
common-continuum Krylov sequence Cauchy. -/
theorem krylov_cauchy
    (m : ℕ) (k : Fin 3) :
    CauchySeq
      (fun n =>
        physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L n m k) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := C.finiteDefect_tail m k ε hε
  refine ⟨N, ?_⟩
  intro n hn j hj
  rw [dist_eq_norm]
  rw [
    physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_sub_norm_eq_finiteCommonMarginalKrylovDefect
      Q R L n j m k]
  exact hN n hn j hj

/-- The continuum Krylov mode is theorem-generated from finite marginal Cauchy
data alone. -/
noncomputable def continuumKrylovMode
    (m : ℕ) (k : Fin 3) :
    Lp ℝ 2 L.continuumMeasure :=
  Classical.choose
    (cauchySeq_tendsto_of_complete
      (krylov_cauchy Q R L C m k))

/-- The theorem-generated Krylov mode is the strong limit of the concrete
finite sequence. -/
theorem krylov_tendsto
    (m : ℕ) (k : Fin 3) :
    Tendsto
      (fun n =>
        physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L n m k)
      atTop
      (𝓝 (continuumKrylovMode Q R L C m k)) :=
  Classical.choose_spec
    (cauchySeq_tendsto_of_complete
      (krylov_cauchy Q R L C m k))

/-- Finite-marginal Cauchy data theorem-generate the #5091 basis-coherence
package. -/
noncomputable def toEvolvedBasisCoherenceInput :
    PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput
      Q R L where
  continuumKrylovMode := continuumKrylovMode Q R L C
  krylov_tendsto := krylov_tendsto Q R L C

/-- The finite union-marginal Cauchy defect suffices for all fixed-time strong
limits of the exact theorem-generated excitation. -/
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
    PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
      Q R L
      (toEvolvedBasisCoherenceInput Q R L C)
      hInvariant

/-- The same finite Cauchy defect data inherit the uniform q0^m estimate. -/
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
    PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
      Q R L
      (toEvolvedBasisCoherenceInput Q R L C)
      hInvariant s hs hcut

end PhysicalYangMillsSU2ThreeModeFiniteMarginalKrylovCauchyInput

end KrylovFiniteCauchy

end

end MathlibAnalytic
end MGAP4D
