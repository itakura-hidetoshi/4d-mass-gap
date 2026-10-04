import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovSelfCorrelation
import Mathlib.Tactic

/-!
# Reduce SU(2) Krylov strong limits to scalar pair-correlation Cauchy data

PR #5093 replaces finite Krylov norm-square convergence by concrete 2m-step
self-correlation convergence, but still asks for overlap convergence against an
already chosen continuum limit vector.

This file removes that candidate continuum vector from the input.

For a real Hilbert sequence x_n,

  ||x_n - x_j||^2
    = ||x_n||^2 + ||x_j||^2 - 2 <x_n,x_j>.

Hence, if

* ||x_n||^2 tends to one scalar r, and
* the tail pair correlations <x_n,x_j> approach the same scalar r uniformly
  in n,j,

then x_n is Cauchy. Completeness of the common projective continuum L2 carrier
then theorem-generates the continuum Krylov mode and its strong convergence.

Applied to the three finite SU(2) Krylov modes, the remaining H1-C3 strong-limit
input becomes entirely scalar and candidate-free:

* concrete 2m-step self-correlation convergence;
* tail pair-correlation convergence between two finite embedded Krylov modes.

No continuum vector, global selected-marginal operator compatibility,
cofinality, or independent operator-norm bound is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

/-- Scalar norm-square convergence plus tail pair-correlation convergence to
the same scalar makes a real Hilbert sequence Cauchy. -/
theorem realHilbert_cauchySeq_of_normSq_tendsto_and_pairCorrelation_tail
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : ℕ → H) (r : ℝ)
    (hnormSq : Tendsto (fun n => ‖x n‖ ^ 2) atTop (𝓝 r))
    (hpair :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, N ≤ j →
          |inner ℝ (x n) (x j) - r| < ε) :
    CauchySeq x := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let δ : ℝ := ε ^ 2 / 4
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨N₁, hN₁⟩ :=
    (Metric.tendsto_atTop.1 hnormSq) δ hδ
  obtain ⟨N₂, hN₂⟩ := hpair δ hδ
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn j hj
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hj₁ : N₁ ≤ j := le_trans (le_max_left _ _) hj
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hj₂ : N₂ ≤ j := le_trans (le_max_right _ _) hj
  have hnormN :
      |‖x n‖ ^ 2 - r| < δ := by
    simpa [Real.dist_eq] using hN₁ n hn₁
  have hnormJ :
      |‖x j‖ ^ 2 - r| < δ := by
    simpa [Real.dist_eq] using hN₁ j hj₁
  have hinner :
      |inner ℝ (x n) (x j) - r| < δ :=
    hN₂ n hn₂ j hj₂
  rcases abs_lt.mp hnormN with ⟨hnormNLower, hnormNUpper⟩
  rcases abs_lt.mp hnormJ with ⟨hnormJLower, hnormJUpper⟩
  rcases abs_lt.mp hinner with ⟨hinnerLower, hinnerUpper⟩
  have hsq : ‖x n - x j‖ ^ 2 < ε ^ 2 := by
    rw [norm_sub_sq_real]
    dsimp [δ] at *
    nlinarith
  have hnorm : ‖x n - x j‖ < ε := by
    have hnonneg : 0 ≤ ‖x n - x j‖ := norm_nonneg _
    nlinarith
  simpa [dist_eq_norm] using hnorm

/-- In a complete real Hilbert space, the same scalar data theorem-generate an
actual strong limit. -/
theorem realHilbert_exists_tendsto_of_normSq_tendsto_and_pairCorrelation_tail
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (x : ℕ → H) (r : ℝ)
    (hnormSq : Tendsto (fun n => ‖x n‖ ^ 2) atTop (𝓝 r))
    (hpair :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, N ≤ j →
          |inner ℝ (x n) (x j) - r| < ε) :
    ∃ z : H, Tendsto x atTop (𝓝 z) :=
  cauchySeq_tendsto_of_complete
    (realHilbert_cauchySeq_of_normSq_tendsto_and_pairCorrelation_tail
      x r hnormSq hpair)

local instance su2KrylovPairCorrelationTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2KrylovPairCorrelationCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2KrylovPairCorrelationSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2KrylovPairCorrelationMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2KrylovPairCorrelationBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2KrylovPairCorrelationSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2KrylovPairCorrelationSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance su2KrylovPairCorrelationNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section KrylovPairCorrelation

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

/-- Candidate-free scalar H1-C3 data for the three Krylov modes.

The common scalar r_{m,k} is the limiting 2m-step self-correlation and also the
tail limit of pair correlations between two finite embedded Krylov vectors. -/
structure PhysicalYangMillsSU2ThreeModeKrylovPairCorrelationCauchyInput where
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
  pairCorrelation_tail :
    ∀ (m : ℕ) (k : Fin 3) (ε : ℝ), 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, N ≤ j →
        |inner ℝ
            (physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
              Q R L n m k)
            (physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
              Q R L j m k) -
          scalarLimit m k| < ε

namespace PhysicalYangMillsSU2ThreeModeKrylovPairCorrelationCauchyInput

variable
    (C :
      PhysicalYangMillsSU2ThreeModeKrylovPairCorrelationCauchyInput
        Q R L)

include C

/-- The projective Krylov norm-square converges to the same scalar through the
#5093 exact self-correlation identity. -/
theorem normSq_tendsto
    (m : ℕ) (k : Fin 3) :
    Tendsto
      (fun n =>
        ‖physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L n m k‖ ^ 2)
      atTop
      (𝓝 (C.scalarLimit m k)) := by
  apply (C.selfCorrelation_tendsto m k).congr'
  exact Filter.Eventually.of_forall fun n =>
    (physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_norm_sq_eq_selfCorrelation
      Q R L n m k).symm

/-- Every fixed-time fixed-basis Krylov sequence is Cauchy using scalar finite
pair-correlation data only. -/
theorem krylov_cauchy
    (m : ℕ) (k : Fin 3) :
    CauchySeq
      (fun n =>
        physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L n m k) := by
  exact
    realHilbert_cauchySeq_of_normSq_tendsto_and_pairCorrelation_tail
      (fun n =>
        physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L n m k)
      (C.scalarLimit m k)
      (C.normSq_tendsto m k)
      (C.pairCorrelation_tail m k)

/-- Canonical theorem-generated continuum Krylov mode as the limit of its
candidate-free scalar-Cauchy sequence. -/
noncomputable def continuumKrylovMode
    (m : ℕ) (k : Fin 3) :
    Lp ℝ 2 L.continuumMeasure :=
  Classical.choose
    (cauchySeq_tendsto_of_complete (C.krylov_cauchy m k))

/-- The theorem-generated continuum Krylov mode is the actual strong limit. -/
theorem krylov_tendsto
    (m : ℕ) (k : Fin 3) :
    Tendsto
      (fun n =>
        physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L n m k)
      atTop
      (𝓝 (C.continuumKrylovMode m k)) :=
  Classical.choose_spec
    (cauchySeq_tendsto_of_complete (C.krylov_cauchy m k))

/-- Candidate-free scalar Cauchy data theorem-generate the #5091
basis-coherence package. -/
noncomputable def toEvolvedBasisCoherenceInput :
    PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput
      Q R L where
  continuumKrylovMode := C.continuumKrylovMode
  krylov_tendsto := C.krylov_tendsto

/-- Candidate-free finite scalar data suffice for all fixed-time strong limits
of the theorem-generated exact excitation. -/
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
                Q R L (C.toEvolvedBasisCoherenceInput) m cInf)) := by
  exact
    PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
      Q R L
      (C.toEvolvedBasisCoherenceInput)
      hInvariant

/-- The same candidate-free scalar data inherit the scale-uniform q0^m
estimate after passage to the theorem-generated limits. -/
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
                  Q R L (C.toEvolvedBasisCoherenceInput) m cInf)) ∧
            ‖PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                Q R L (C.toEvolvedBasisCoherenceInput) m cInf‖ ≤
              GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  exact
    PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
      Q R L
      (C.toEvolvedBasisCoherenceInput)
      hInvariant s hs hcut

end PhysicalYangMillsSU2ThreeModeKrylovPairCorrelationCauchyInput

end KrylovPairCorrelation

end

end MathlibAnalytic
end MGAP4D
