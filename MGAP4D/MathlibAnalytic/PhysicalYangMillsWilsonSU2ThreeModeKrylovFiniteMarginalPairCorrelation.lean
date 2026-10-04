import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovPairCorrelationCauchy
import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitL2CylinderIsometricSystem
import Mathlib.Tactic

/-!
# Replace continuum Krylov pair correlations by one common finite marginal

PR #5094 removes any preselected continuum Krylov vector.  Its only remaining
cross-scale strong-limit input is a tail estimate for

  <x_{n,m,k}, x_{j,m,k}>

inside the common continuum projective-limit L2 carrier.

That scalar is already finite-dimensional.

For any two finite marginals J and K, let I = J ∪ K.  Projective compatibility
gives

  pull_J f = pull_I (transition_{J→I} f)
  pull_K g = pull_I (transition_{K→I} g),

and the common pullback is isometric. Therefore

  <pull_J f, pull_K g>
    =
  <transition_{J→I} f, transition_{K→I} g>_I.

Applying this to the two finite SU(2) evolved Krylov marginal vectors replaces
the #5094 continuum pair-correlation tail by a scalar inner product computed
entirely in one larger finite interacting marginal.

No transfer-operator scale compatibility is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

/-- Cross-inner-products of two projective cylinder vectors can always be
computed after transporting both vectors to the union finite marginal. -/
theorem finiteMarginalL2Pullback_cross_inner_eq_union_transition_inner
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (J K : Finset EuclideanFourSpace)
    (f : Lp ℝ 2 (F.finiteMarginal J))
    (g : Lp ℝ 2 (F.finiteMarginal K)) :
    inner ℝ
        (L.finiteMarginalL2Pullback J f)
        (L.finiteMarginalL2Pullback K g) =
      inner ℝ
        (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F)
          (show J ⊆ J ∪ K from Finset.subset_union_left) f)
        (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F)
          (show K ⊆ J ∪ K from Finset.subset_union_right) g) := by
  rw [
    L.finiteMarginalL2Pullback_compatible
      (show J ⊆ J ∪ K from Finset.subset_union_left) f,
    L.finiteMarginalL2Pullback_compatible
      (show K ⊆ J ∪ K from Finset.subset_union_right) g,
    L.finiteMarginalL2Pullback_inner]

local instance su2KrylovFinitePairTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2KrylovFinitePairCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2KrylovFinitePairSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2KrylovFinitePairMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2KrylovFinitePairBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2KrylovFinitePairSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2KrylovFinitePairSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance su2KrylovFinitePairNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section KrylovFinitePairCorrelation

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

/-- The actual finite marginal representative of one evolved first-three
Krylov mode before the final pullback to the continuum carrier. -/
noncomputable def physicalYangMillsSU2ThreeModeEvolvedFiniteMarginalKrylovMode
    (n m : ℕ) (k : Fin 3) :
    Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n)) :=
  physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n
    ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) ^ m)
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
        (halfExtent n) k))

/-- The common finite marginal used to compare scales n and j. -/
def physicalYangMillsSU2ThreeModeKrylovCommonMarginalIndex
    (n j : ℕ) :
    Finset EuclideanFourSpace :=
  R.marginalIndex n ∪ R.marginalIndex j

/-- Fully finite cross-scale scalar pair correlation: each finite Krylov vector
is transported to the union selected marginal before taking the inner product. -/
noncomputable def physicalYangMillsSU2ThreeModeFiniteCommonMarginalPairCorrelation
    (n j m : ℕ) (k : Fin 3) : ℝ :=
  inner ℝ
    (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
      (F := F)
      (show R.marginalIndex n ⊆
          physicalYangMillsSU2ThreeModeKrylovCommonMarginalIndex (Q := Q) (R := R) n j by
        exact Finset.subset_union_left)
      (physicalYangMillsSU2ThreeModeEvolvedFiniteMarginalKrylovMode
        Q R n m k))
    (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
      (F := F)
      (show R.marginalIndex j ⊆
          physicalYangMillsSU2ThreeModeKrylovCommonMarginalIndex (Q := Q) (R := R) n j by
        exact Finset.subset_union_right)
      (physicalYangMillsSU2ThreeModeEvolvedFiniteMarginalKrylovMode
        Q R j m k))

/-- Exact reduction of the common-continuum cross-scale Krylov inner product to
one finite union marginal. -/
theorem physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_inner_eq_finiteCommonMarginalPairCorrelation
    (n j m : ℕ) (k : Fin 3) :
    inner ℝ
        (physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L n m k)
        (physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L j m k) =
      physicalYangMillsSU2ThreeModeFiniteCommonMarginalPairCorrelation
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
    finiteMarginalL2Pullback_cross_inner_eq_union_transition_inner
      L
      (R.marginalIndex n)
      (R.marginalIndex j)
      (physicalYangMillsSU2ThreeModeEvolvedFiniteMarginalKrylovMode
        Q R n m k)
      (physicalYangMillsSU2ThreeModeEvolvedFiniteMarginalKrylovMode
        Q R j m k)

/-- H1-C3 scalar input stated entirely on finite interacting marginals.

The first field is the already-concrete 2m-step self-correlation from #5093.
The second is the common-union finite marginal cross-correlation tail. -/
structure PhysicalYangMillsSU2ThreeModeFiniteMarginalPairCorrelationCauchyInput where
  scalarLimit : ℕ → Fin 3 → ℝ
  selfCorrelation_tendsto :
    ∀ (m : ℕ) (k : Fin 3),
      Tendsto
        (fun n =>
          physicalYangMillsSU2ThreeModeFiniteKrylovSelfCorrelation
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n m k)
        atTop
        (𝓝 (scalarLimit m k))
  finitePairCorrelation_tail :
    ∀ (m : ℕ) (k : Fin 3) (ε : ℝ), 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, N ≤ j →
        |physicalYangMillsSU2ThreeModeFiniteCommonMarginalPairCorrelation
            (Q := Q) (R := R) n j m k -
          scalarLimit m k| < ε

namespace PhysicalYangMillsSU2ThreeModeFiniteMarginalPairCorrelationCauchyInput

variable
    (C :
      PhysicalYangMillsSU2ThreeModeFiniteMarginalPairCorrelationCauchyInput
        (Q := Q) (R := R))

include C

/-- The purely finite common-marginal tail theorem-generates the #5094
continuum-carrier pair-correlation tail. -/
theorem pairCorrelation_tail
    (m : ℕ) (k : Fin 3) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, N ≤ j →
      |inner ℝ
          (physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
            Q R L n m k)
          (physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
            Q R L j m k) -
        C.scalarLimit m k| < ε := by
  obtain ⟨N, hN⟩ := C.finitePairCorrelation_tail m k ε hε
  refine ⟨N, ?_⟩
  intro n hn j hj
  rw [
    physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_inner_eq_finiteCommonMarginalPairCorrelation
      Q R L n j m k]
  exact hN n hn j hj

/-- The finite-marginal scalar package theorem-generates the candidate-free
#5094 Cauchy package. -/
noncomputable def toKrylovPairCorrelationCauchyInput :
    PhysicalYangMillsSU2ThreeModeKrylovPairCorrelationCauchyInput
      Q R L where
  scalarLimit := C.scalarLimit
  selfCorrelation_tendsto := C.selfCorrelation_tendsto
  pairCorrelation_tail :=
    pairCorrelation_tail Q R L C

/-- Finite marginal scalar data suffice for all fixed-time strong limits of
the exact theorem-generated excitation. -/
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
                (PhysicalYangMillsSU2ThreeModeKrylovPairCorrelationCauchyInput.toEvolvedBasisCoherenceInput
                  Q R L (toKrylovPairCorrelationCauchyInput (Q := Q) (R := R) (L := L) (C := C)))
                m cInf)) := by
  exact
    PhysicalYangMillsSU2ThreeModeKrylovPairCorrelationCauchyInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
      Q R L
      (toKrylovPairCorrelationCauchyInput (Q := Q) (R := R) (L := L) (C := C))
      hInvariant

/-- The same finite common-marginal scalar data retain the uniform q0^m decay
after the continuum passage. -/
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
                  (PhysicalYangMillsSU2ThreeModeKrylovPairCorrelationCauchyInput.toEvolvedBasisCoherenceInput
                    Q R L (toKrylovPairCorrelationCauchyInput (Q := Q) (R := R) (L := L) (C := C)))
                  m cInf)) ∧
            ‖PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                Q R L
                (PhysicalYangMillsSU2ThreeModeKrylovPairCorrelationCauchyInput.toEvolvedBasisCoherenceInput
                  Q R L (toKrylovPairCorrelationCauchyInput (Q := Q) (R := R) (L := L) (C := C)))
                m cInf‖ ≤
              GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  exact
    PhysicalYangMillsSU2ThreeModeKrylovPairCorrelationCauchyInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
      Q R L
      (toKrylovPairCorrelationCauchyInput (Q := Q) (R := R) (L := L) (C := C))
      hInvariant s hs hcut

end PhysicalYangMillsSU2ThreeModeFiniteMarginalPairCorrelationCauchyInput

end KrylovFinitePairCorrelation

end

end MathlibAnalytic
end MGAP4D
