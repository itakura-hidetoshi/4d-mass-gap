import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeEvolvedBasisCoherence
import Mathlib.Tactic

/-!
# Reduce SU(2) Krylov strong convergence to scalar Hilbert data

PR #5091 reduces the evolved strong-limit existence problem for the exact
three-mode SU(2) excitation to strong convergence of three concrete Krylov
mode sequences at each fixed natural time.

This file removes the remaining vector-valued convergence assumption.

For a sequence x_n in a real Hilbert space and a candidate limit z, the
identity

  ||x_n - z||^2
    = ||x_n||^2 + ||z||^2 - 2 <x_n,z>

shows that strong convergence follows from only two scalar limits:

  ||x_n||^2 -> ||z||^2
  <x_n,z>   -> ||z||^2.

We package exactly these two scalar convergence statements for the three
finite Krylov modes.  They theorem-generate the #5091 basis-coherence input,
hence all evolved strong limits and the existing q0^m bounds.

The norm-square scalar is also exposed before the projective embedding: the
common continuum embedding is isometric, so no norm information is lost.

Thus the remaining H1-C3 strong-limit frontier is scalar rather than
Hilbert-valued.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

/-- In a real Hilbert space, convergence of norm squares together with
convergence of the overlap against the candidate limit implies strong
convergence. -/
theorem realHilbert_tendsto_of_normSq_and_overlap_tendsto
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : ℕ → H) (z : H)
    (hnormSq :
      Tendsto (fun n => ‖x n‖ ^ 2) atTop (𝓝 (‖z‖ ^ 2)))
    (hoverlap :
      Tendsto (fun n => inner ℝ (x n) z) atTop (𝓝 (‖z‖ ^ 2))) :
    Tendsto x atTop (𝓝 z) := by
  have htwice :
      Tendsto
        (fun n => inner ℝ (x n) z + inner ℝ (x n) z)
        atTop
        (𝓝 (‖z‖ ^ 2 + ‖z‖ ^ 2)) :=
    hoverlap.add hoverlap
  have hsum :
      Tendsto
        (fun n => ‖x n‖ ^ 2 + ‖z‖ ^ 2)
        atTop
        (𝓝 (‖z‖ ^ 2 + ‖z‖ ^ 2)) :=
    hnormSq.add_const (‖z‖ ^ 2)
  have hsq :
      Tendsto (fun n => ‖x n - z‖ ^ 2) atTop (𝓝 0) := by
    have h := hsum.sub htwice
    convert h using 1
    · funext n
      rw [norm_sub_sq_real]
      ring
    · ring
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hεsq : 0 < ε ^ 2 := by positivity
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 hsq) (ε ^ 2) hεsq
  refine ⟨N, ?_⟩
  intro n hn
  have hs := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)] at hs
  rw [dist_eq_norm]
  have hnonneg : 0 ≤ ‖x n - z‖ := norm_nonneg _
  nlinarith

local instance su2KrylovScalarTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2KrylovScalarCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2KrylovScalarSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2KrylovScalarMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2KrylovScalarBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2KrylovScalarSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2KrylovScalarSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance su2KrylovScalarNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section KrylovScalar

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

/-- The projective continuum embedding preserves the exact finite Krylov
norm-square. -/
theorem physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_norm_sq
    (n m : ℕ) (k : Fin 3) :
    ‖physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
        Q R L n m k‖ ^ 2 =
      ‖(periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) ^ m)
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
          (halfExtent n) k)‖ ^ 2 := by
  unfold physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
  rw [physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding_norm]

/-- Minimal scalar strong-limit input for the three Krylov modes.

For every natural time and each of the three basis modes, only two real scalar
limits are required. -/
structure PhysicalYangMillsSU2ThreeModeKrylovScalarStrongLimitInput where
  continuumKrylovMode :
    ℕ → Fin 3 → Lp ℝ 2 L.continuumMeasure
  normSq_tendsto :
    ∀ (m : ℕ) (k : Fin 3),
      Tendsto
        (fun n =>
          ‖physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
            Q R L n m k‖ ^ 2)
        atTop
        (𝓝 (‖continuumKrylovMode m k‖ ^ 2))
  overlap_tendsto :
    ∀ (m : ℕ) (k : Fin 3),
      Tendsto
        (fun n =>
          inner ℝ
            (physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
              Q R L n m k)
            (continuumKrylovMode m k))
        atTop
        (𝓝 (‖continuumKrylovMode m k‖ ^ 2))

namespace PhysicalYangMillsSU2ThreeModeKrylovScalarStrongLimitInput

variable
    (C :
      PhysicalYangMillsSU2ThreeModeKrylovScalarStrongLimitInput
        Q R L)

/-- The two scalar limits imply strong convergence of each concrete Krylov
mode sequence. -/
theorem krylov_tendsto
    (m : ℕ) (k : Fin 3) :
    Tendsto
      (fun n =>
        physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L n m k)
      atTop
      (𝓝 (C.continuumKrylovMode m k)) := by
  exact
    realHilbert_tendsto_of_normSq_and_overlap_tendsto
      (fun n =>
        physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L n m k)
      (C.continuumKrylovMode m k)
      (C.normSq_tendsto m k)
      (C.overlap_tendsto m k)

/-- Scalar Krylov data theorem-generate the #5091 basis-coherence package. -/
noncomputable def toEvolvedBasisCoherenceInput :
    PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput
      Q R L where
  continuumKrylovMode := C.continuumKrylovMode
  krylov_tendsto := C.krylov_tendsto

/-- Scalar norm-square and overlap convergence are enough for all fixed-time
strong limits of the exact theorem-generated excitation. -/
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

/-- The same scalar data retain the full scale-uniform q0^m estimate after the
continuum passage. -/
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

end PhysicalYangMillsSU2ThreeModeKrylovScalarStrongLimitInput

end KrylovScalar

end

end MathlibAnalytic
end MGAP4D
