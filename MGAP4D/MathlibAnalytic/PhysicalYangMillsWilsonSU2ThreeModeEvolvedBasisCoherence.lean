import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeEvolvedSynthesisCoherence
import Mathlib.Tactic

/-!
# Reduce evolved three-mode synthesis coherence to three Krylov-mode limits

PR #5090 reduces evolved strong convergence of the theorem-generated exact
SU(2) excitation to pointwise strong convergence of a three-dimensional
evolved synthesis.

That is still more data than necessary.

For each natural transfer time m, the finite evolved synthesis is a linear map
from R^3.  Hence it is completely determined by its values on the three
standard basis vectors.  Those values are exactly the three finite Krylov
sequences

  J_n (S_n^m u_{0,n}),
  J_n (S_n^m u_{1,n}),
  J_n (S_n^m u_{2,n}).

This file takes strong convergence of only those three sequences as input.
Their limits uniquely determine a linear map R^3 -> continuum L2.  Since the
domain is finite-dimensional, Mathlib upgrades that linear map canonically to
a continuous linear map.  Finite-sum continuity then gives pointwise strong
convergence of the full evolved synthesis, so the #5090 package applies.

Thus the remaining H1-C3 strong-limit existence frontier is reduced to three
concrete Krylov-mode sequences at each fixed natural time.

No global selected-marginal operator compatibility, no cofinality, and no
independent operator-norm bound are assumed here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2ThreeModeBasisTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2ThreeModeBasisCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2ThreeModeBasisSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2ThreeModeBasisMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2ThreeModeBasisBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2ThreeModeBasisSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2ThreeModeBasisSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance su2ThreeModeBasisNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section EvolvedBasisCoherence

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

/-- The k-th first-three Gram--Schmidt pair mode after m genuine finite transfer
steps, embedded into the common projective continuum carrier. -/
noncomputable def physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
    (n m : ℕ) (k : Fin 3) :
    Lp ℝ 2 L.continuumMeasure :=
  physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
    Q R L n
    ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) ^ m)
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
        (halfExtent n) k))

/-- The evolved synthesis evaluated at a standard basis vector is exactly the
corresponding concrete Krylov mode. -/
@[simp]
theorem physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis_basisFun
    (n m : ℕ) (k : Fin 3) :
    physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
        Q R L n m
        (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
        Q R L n m k := by
  unfold physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
  unfold physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
  change
    physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding Q R L n
      ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) ^ m)
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
          (halfExtent n)
          (EuclideanSpace.basisFun (Fin 3) ℝ k))) =
    _
  rw [
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis_basisFun]

/-- Minimal finite-dimensional H1-C3 strong-limit input: for every fixed
natural time, only the three evolved basis/Krylov modes need strong limits. -/
structure PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput where
  continuumKrylovMode :
    ℕ → Fin 3 → Lp ℝ 2 L.continuumMeasure
  krylov_tendsto :
    ∀ (m : ℕ) (k : Fin 3),
      Tendsto
        (fun n =>
          physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
            Q R L n m k)
        atTop
        (𝓝 (continuumKrylovMode m k))

namespace PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput

variable
    (C :
      PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput
        Q R L)

/-- Linear synthesis uniquely determined by the three continuum Krylov-mode
limits. -/
noncomputable def continuumSynthesisLinearMap
    (m : ℕ) :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.constr ℝ
    (C.continuumKrylovMode m)

/-- Because the source is finite-dimensional, the basis-defined continuum
synthesis is automatically continuous. -/
noncomputable def continuumSynthesis
    (m : ℕ) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  LinearMap.toContinuousLinearMap
    (C.continuumSynthesisLinearMap m)

@[simp]
theorem continuumSynthesis_basisFun
    (m : ℕ) (k : Fin 3) :
    C.continuumSynthesis m
        (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      C.continuumKrylovMode m k := by
  change
    C.continuumSynthesisLinearMap m
        (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      C.continuumKrylovMode m k
  unfold continuumSynthesisLinearMap
  change
    ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.constr ℝ
      (C.continuumKrylovMode m))
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis k) =
    C.continuumKrylovMode m k
  exact
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.constr_basis ℝ
      (C.continuumKrylovMode m) k

/-- Three basis-vector limits imply pointwise strong convergence of the full
evolved R^3 synthesis. -/
theorem finiteSynthesis_tendsto
    (m : ℕ) (c : EuclideanSpace ℝ (Fin 3)) :
    Tendsto
      (fun n =>
        physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
          Q R L n m c)
      atTop
      (𝓝 (C.continuumSynthesis m c)) := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hsum :
      Tendsto
        (fun n =>
          ∑ k : Fin 3,
            (b.repr c k) •
              physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
                Q R L n m (b k))
        atTop
        (𝓝
          (∑ k : Fin 3,
            (b.repr c k) • C.continuumSynthesis m (b k))) := by
    apply tendsto_finset_sum (Finset.univ : Finset (Fin 3))
    intro k hk
    exact
      ((C.krylov_tendsto m k).congr'
        (Filter.Eventually.of_forall fun n => by
          symm
          exact
            physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis_basisFun
              Q R L n m k)).const_smul (b.repr c k)
  have hc : (∑ k : Fin 3, b.repr c k • b k) = c :=
    b.sum_repr c
  simpa [b, hc] using hsum

/-- The three concrete Krylov-mode limits theorem-generate the synthesis
coherence input of #5090. -/
noncomputable def toEvolvedSynthesisCoherenceInput :
    PhysicalYangMillsSU2ThreeModeEvolvedSynthesisCoherenceInput
      Q R L where
  continuumSynthesis := C.continuumSynthesis
  finiteSynthesis_tendsto := C.finiteSynthesis_tendsto

/-- Three Krylov-mode limits at every natural time are enough for same-subsequence
strong limits of the theorem-generated exact finite excitation. -/
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
            (𝓝 (C.continuumSynthesis m cInf)) := by
  exact
    PhysicalYangMillsSU2ThreeModeEvolvedSynthesisCoherenceInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
      Q R L
      (C.toEvolvedSynthesisCoherenceInput)
      hInvariant

/-- The same three Krylov-mode limits also inherit the existing uniform q0^m
bound on every evolved continuum limit. -/
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
              (𝓝 (C.continuumSynthesis m cInf)) ∧
            ‖C.continuumSynthesis m cInf‖ ≤
              GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  exact
    PhysicalYangMillsSU2ThreeModeEvolvedSynthesisCoherenceInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
      Q R L
      (C.toEvolvedSynthesisCoherenceInput)
      hInvariant s hs hcut

end PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput

end EvolvedBasisCoherence

end

end MathlibAnalytic
end MGAP4D
