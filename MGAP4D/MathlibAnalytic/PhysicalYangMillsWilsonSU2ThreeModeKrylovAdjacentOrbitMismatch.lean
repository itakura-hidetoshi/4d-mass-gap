import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentCommonTransferPerturbation
import Mathlib.Tactic

/-!
# Vector-wise adjacent transfer mismatch along the finite Krylov orbit

The full common-transfer operator norm used in PR #5103 is a convenient
sufficient condition, and PR #5105 further splits that whole-space mismatch
into geometry and coupling pieces.  The present route is complementary: it
compares the two compressed operators only where the Krylov argument actually
uses them, rather than on the whole union-marginal Hilbert space.  The coarse and fine embeddings need not have
identical ranges, so that norm can be stronger than the fixed-time Krylov
problem actually requires.

For contractions A and B, a one-sided telescoping estimate gives

  ||A^m x - B^m y||
    <= ||x-y|| + sum_{r < m} ||(A-B) (B^r y)||.

Thus the SU(2) adjacent Krylov defect only needs the transfer mismatch evaluated
along the finite fine-side Krylov orbit.  For every fixed natural time m this is
a finite family of vector-wise quantities, not a whole-space operator norm.

Under the existing coherent readout, the initial mismatch is summable (indeed
eventually zero).  Hence summability of each fixed orbit mismatch in the scale
index theorem-generates all fixed-time strong limits.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology BigOperators

noncomputable section

/-- A contraction on the left accumulates operator mismatch only along the
right orbit.  No operator-norm bound on A-B and no contraction hypothesis on B
is needed. -/
theorem continuousLinearMap_contraction_pow_apply_sub_pow_apply_norm_le_initial_add_orbitSum
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E →L[ℝ] E)
    (hA : ‖A‖ ≤ 1)
    (m : ℕ)
    (x y : E) :
    ‖(A ^ m) x - (B ^ m) y‖ ≤
      ‖x - y‖ +
        ∑ r ∈ Finset.range m, ‖(A - B) ((B ^ r) y)‖ := by
  have hA_apply : ∀ z : E, ‖A z‖ ≤ ‖z‖ := by
    intro z
    calc
      ‖A z‖ ≤ ‖A‖ * ‖z‖ := A.le_opNorm z
      _ ≤ 1 * ‖z‖ :=
        mul_le_mul_of_nonneg_right hA (norm_nonneg z)
      _ = ‖z‖ := one_mul _
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hdecomp :
          (A ^ (m + 1)) x - (B ^ (m + 1)) y =
            A ((A ^ m) x - (B ^ m) y) +
              (A - B) ((B ^ m) y) := by
        rw [pow_succ', pow_succ',
          ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
        simp only [map_sub, ContinuousLinearMap.sub_apply]
        abel
      rw [hdecomp]
      calc
        ‖A ((A ^ m) x - (B ^ m) y) +
            (A - B) ((B ^ m) y)‖ ≤
          ‖A ((A ^ m) x - (B ^ m) y)‖ +
            ‖(A - B) ((B ^ m) y)‖ :=
          norm_add_le _ _
        _ ≤
          ‖(A ^ m) x - (B ^ m) y‖ +
            ‖(A - B) ((B ^ m) y)‖ :=
          add_le_add_left
            (hA_apply ((A ^ m) x - (B ^ m) y)) _
        _ ≤
          (‖x - y‖ +
            ∑ r ∈ Finset.range m, ‖(A - B) ((B ^ r) y)‖) +
              ‖(A - B) ((B ^ m) y)‖ :=
          add_le_add_left ih _
        _ =
          ‖x - y‖ +
            ∑ r ∈ Finset.range (m + 1), ‖(A - B) ((B ^ r) y)‖ := by
          rw [Finset.sum_range_succ]
          ring

local instance su2AdjacentOrbitTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentOrbitCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentOrbitSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentOrbitMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentOrbitBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentOrbitSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentOrbitSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentOrbitNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section AdjacentKrylovOrbitMismatch

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

/-- Vector-wise adjacent transfer mismatch evaluated on the r-th fine-side
Krylov orbit vector. -/
noncomputable def physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
    (n r : ℕ) (k : Fin 3) : ℝ :=
  ‖(physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
      physicalYangMillsSU2AdjacentCommonRightTransfer Q R n)
      ((physicalYangMillsSU2AdjacentCommonRightTransfer Q R n ^ r)
        (physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode Q R n k))‖

/-- The full evolved adjacent defect is controlled by the time-zero mismatch
plus the finite sum of vector-wise transfer mismatches along the fine orbit. -/
theorem physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect_le_zero_add_sum_rightOrbitMismatch
    (n m : ℕ) (k : Fin 3) :
    physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
        (Q := Q) (R := R) n m k ≤
      physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
          (Q := Q) (R := R) n 0 k +
        ∑ r ∈ Finset.range m,
          physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
            Q R n r k := by
  have hpert :=
    continuousLinearMap_contraction_pow_apply_sub_pow_apply_norm_le_initial_add_orbitSum
      (physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n)
      (physicalYangMillsSU2AdjacentCommonRightTransfer Q R n)
      (physicalYangMillsSU2AdjacentCommonLeftTransfer_opNorm_le_one Q R n)
      m
      (physicalYangMillsSU2AdjacentCommonLeftInitialKrylovMode Q R n k)
      (physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode Q R n k)
  have hzero :
      physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
          (Q := Q) (R := R) n 0 k =
        ‖physicalYangMillsSU2AdjacentCommonLeftInitialKrylovMode Q R n k -
          physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode Q R n k‖ := by
    simpa using
      physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect_eq_commonTransferPowerDifference
        Q R n 0 k
  calc
    physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
        (Q := Q) (R := R) n m k =
      ‖(physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n ^ m)
          (physicalYangMillsSU2AdjacentCommonLeftInitialKrylovMode Q R n k) -
        (physicalYangMillsSU2AdjacentCommonRightTransfer Q R n ^ m)
          (physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode Q R n k)‖ :=
      physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect_eq_commonTransferPowerDifference
        Q R n m k
    _ ≤
      ‖physicalYangMillsSU2AdjacentCommonLeftInitialKrylovMode Q R n k -
        physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode Q R n k‖ +
        ∑ r ∈ Finset.range m,
          ‖(physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
              physicalYangMillsSU2AdjacentCommonRightTransfer Q R n)
              ((physicalYangMillsSU2AdjacentCommonRightTransfer Q R n ^ r)
                (physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode Q R n k))‖ :=
      hpert
    _ =
      physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
          (Q := Q) (R := R) n 0 k +
        ∑ r ∈ Finset.range m,
          physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
            Q R n r k := by
      rw [← hzero]
      rfl

/-- Only the vector-wise common-transfer mismatch along each fixed finite Krylov
orbit needs to be summable in the refinement scale. -/
structure PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchSummableInput where
  orbitMismatch_summable :
    ∀ (r : ℕ) (k : Fin 3),
      Summable
        (fun n =>
          physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
            Q R n r k)

namespace PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchSummableInput

variable
    (V :
      PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchSummableInput
        (Q := Q) (R := R))

include V

/-- For fixed natural time, the finite sum of orbit mismatches is summable in
the refinement scale. -/
theorem orbitMismatch_finsetSum_summable
    (m : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        ∑ r ∈ Finset.range m,
          physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
            Q R n r k) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      simpa [Finset.sum_range_succ] using
        ih.add (V.orbitMismatch_summable m k)

/-- Coherent time-zero readout plus summable vector-wise orbit mismatch gives
summability of every fixed-time adjacent Krylov defect. -/
theorem adjacentDefect_summable
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (m : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
          (Q := Q) (R := R) n m k) := by
  have hzero :
      Summable
        (fun n =>
          physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
            (Q := Q) (R := R) n 0 k) :=
    physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect_zero_summable
      Q R L hInvariant C k
  have horbit :=
    orbitMismatch_finsetSum_summable Q R V m k
  have hmajorant :
      Summable
        (fun n =>
          physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
              (Q := Q) (R := R) n 0 k +
            ∑ r ∈ Finset.range m,
              physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
                Q R n r k) :=
    hzero.add horbit
  refine Summable.of_nonneg_of_le
    (fun n => ?_)
    (fun n =>
      physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect_le_zero_add_sum_rightOrbitMismatch
        Q R n m k)
    hmajorant
  unfold physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
  unfold physicalYangMillsSU2ThreeModeFiniteCommonMarginalKrylovDefect
  exact norm_nonneg _

/-- Vector-wise orbit summability theorem-generates the #5098 adjacent-defect
summability package. -/
noncomputable def toFiniteAdjacentKrylovSummableInput
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput
      (Q := Q) (R := R) where
  adjacentDefect_summable :=
    adjacentDefect_summable Q R L V hInvariant C

/-- Vector-wise orbit mismatch summability is sufficient for all fixed-time
strong limits of the theorem-generated norm-one excitation. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
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
                (PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.toEvolvedBasisCoherenceInput
                  Q R L
                  (toFiniteAdjacentKrylovSummableInput
                    Q R L V hInvariant C))
                m cInf)) := by
  exact
    PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
      Q R L
      (toFiniteAdjacentKrylovSummableInput Q R L V hInvariant C)
      hInvariant

/-- The same vector-wise hypothesis preserves the uniform q0^m continuum
decay. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
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
                  (PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.toEvolvedBasisCoherenceInput
                    Q R L
                    (toFiniteAdjacentKrylovSummableInput
                      Q R L V hInvariant C))
                  m cInf)) ∧
            ‖PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                Q R L
                (PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.toEvolvedBasisCoherenceInput
                  Q R L
                  (toFiniteAdjacentKrylovSummableInput
                    Q R L V hInvariant C))
                m cInf‖ ≤
              GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  exact
    PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
      Q R L
      (toFiniteAdjacentKrylovSummableInput Q R L V hInvariant C)
      hInvariant s hs hcut

end PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchSummableInput

end AdjacentKrylovOrbitMismatch

end

end MathlibAnalytic
end MGAP4D
