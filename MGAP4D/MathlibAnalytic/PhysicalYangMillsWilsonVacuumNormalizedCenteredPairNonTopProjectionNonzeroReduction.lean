import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedCenteredPairNonTopProjection
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5TwoModeFeatureKernelResidual
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSUNTwoModeFiniteOSVacuumPairFixedSeam
import Mathlib.Tactic

/-!
# Nonzero projected centered excitation reduced to one vacuum/top overlap

PR #5065 makes the canonical physical non-top projection of every actual
vacuum-normalized centered two-mode pair available unconditionally and places
it in the uniform q0 receiver.

This file isolates the remaining finite-dimensional nonzero question.  The
two uncentered endpoint-pair modes are orthonormal.  In a real Hilbert space,
if a unit centering vacuum has nonzero overlap with the selected top direction,
two orthonormal vectors cannot both have their vacuum-centered parts trapped in
that one-dimensional top line.

Specializing this elementary fact to the Wilson pair carrier shows:

  <OS vacuum pair, physical pair-top mode> != 0
    ->
  at least one of the two canonical non-top projections is nonzero.

Thus the next model-specific residual is one scalar overlap, not a transfer
compatibility or a top-alignment statement.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

/-- Pure Hilbert-space two-mode lemma.  A unit centering vector with nonzero
overlap against a selected line cannot center two orthonormal vectors entirely
into that same line. -/
theorem exists_finiteVacuumCentered_not_mem_span_singleton_of_orthonormal_two
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (vac top : E)
    (u : Fin 2 → E)
    (hvacNorm : ‖vac‖ = 1)
    (hOverlap : inner ℝ vac top ≠ 0)
    (hu : Orthonormal ℝ u) :
    ∃ k : Fin 2, finiteVacuumCentered vac (u k) ∉ ℝ ∙ top := by
  by_contra h
  push_neg at h
  have hCenteredZero :
      ∀ k : Fin 2, finiteVacuumCentered vac (u k) = 0 := by
    intro k
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (h k)
    have hOrth :
        inner ℝ vac (finiteVacuumCentered vac (u k)) = 0 :=
      inner_finiteVacuumCentered_eq_zero_of_norm_one vac (u k) hvacNorm
    have hScaled : a * inner ℝ vac top = 0 := by
      calc
        a * inner ℝ vac top = inner ℝ vac (a • top) := by
          rw [real_inner_smul_right]
        _ = inner ℝ vac (finiteVacuumCentered vac (u k)) := by
          rw [ha]
        _ = 0 := hOrth
    have haZero : a = 0 :=
      (mul_eq_zero.mp hScaled).resolve_right hOverlap
    rw [← ha, haZero, zero_smul]
  have huEq :
      ∀ k : Fin 2, u k = inner ℝ vac (u k) • vac := by
    intro k
    have hz := hCenteredZero k
    unfold finiteVacuumCentered at hz
    exact sub_eq_zero.mp hz
  let c0 : ℝ := inner ℝ vac (u 0)
  let c1 : ℝ := inner ℝ vac (u 1)
  have hc0 : c0 ≠ 0 := by
    intro hc
    have hu0 : u 0 = 0 := by
      rw [huEq 0]
      simp [c0, hc]
    have hn := hu.norm_eq_one (0 : Fin 2)
    rw [hu0, norm_zero] at hn
    norm_num at hn
  have hc1 : c1 ≠ 0 := by
    intro hc
    have hu1 : u 1 = 0 := by
      rw [huEq 1]
      simp [c1, hc]
    have hn := hu.norm_eq_one (1 : Fin 2)
    rw [hu1, norm_zero] at hn
    norm_num at hn
  have h01 : inner ℝ (u 0) (u 1) = 0 :=
    hu.inner_eq_zero (by norm_num)
  have hprod : c0 * c1 = 0 := by
    rw [huEq 0, huEq 1, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hvacNorm] at h01
    simpa [c0, c1] using h01
  exact (mul_ne_zero hc0 hc1) hprod

local instance centeredProjectionNonzeroTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance centeredProjectionNonzeroCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance centeredProjectionNonzeroSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance centeredProjectionNonzeroMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance centeredProjectionNonzeroBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance centeredProjectionNonzeroSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance centeredProjectionNonzeroSpatialHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance centeredProjectionNonzeroTopTopCompleteSpace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
        H N hN beta hbeta) := by
  let PairE :=
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
  let PairT :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
      H N hN beta hbeta
  have hclosed : IsClosed (PairT : Set PairE) := by
    change IsClosed
      ((((periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan
        H N hN beta hbeta).topologicalClosure : Submodule ℝ PairE) : Set PairE))
    exact Submodule.isClosed_topologicalClosure _
  exact hclosed.completeSpace_coe

/-- The concrete uncentered two-mode pair family remains orthonormal after the
exact boundary-Haar to ordered spatial-pair isometry. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeUncenteredBoundaryPairL2_orthonormal
    (H N : ℕ)
    (hN2 : 2 ≤ N) :
    Orthonormal ℝ
      (fun k : Fin 2 =>
        periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N
          (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
            H hN2 k)) := by
  let E :=
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N
  let b := fun k : Fin 2 =>
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
      H hN2 k
  have hb :
      Orthonormal ℝ b := by
    simpa [b] using
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2_orthonormal
        H N hN2
  rw [orthonormal_iff_ite]
  intro i j
  change inner ℝ (E (b i)) (E (b j)) = if i = j then 1 else 0
  calc
    inner ℝ (E (b i)) (E (b j)) = inner ℝ (b i) (b j) :=
      E.inner_map_map (b i) (b j)
    _ = if i = j then 1 else 0 :=
      (orthonormal_iff_ite.mp hb) i j

section VacuumNormalizedProjectedNonzeroReduction

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N} {hN2 : 2 ≤ N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))

/-- At one finite scale, nonzero overlap of the canonical-sign OS vacuum pair
with the selected physical pair-top mode forces at least one of the two
canonical physical non-top projections to be nonzero. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_exists_nonzero_centeredBoundaryPairNonTopProjection_of_vacuumPair_inner_pairTop_ne_zero
    (n : ℕ)
    (hOverlap :
      inner ℝ
          (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
            (S := S) (D := D) (halfExtent := halfExtent)
            (N := N) (hN := hN)
            (beta := beta) (hbeta := hbeta)
            (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
            (halfExtent n) N hN (beta n) (hbeta n)) ≠ 0) :
    ∃ k : Fin 2,
      physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
          (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) k n ≠ 0 := by
  let vac :=
    physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n
  let top :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
      (halfExtent n) N hN (beta n) (hbeta n)
  let u := fun k : Fin 2 =>
    physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2
      (halfExtent := halfExtent) (N := N) (hN2 := hN2) k n
  have hvacNorm : ‖vac‖ = 1 := by
    simpa [vac] using
      physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2_norm
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n
  have hu : Orthonormal ℝ u := by
    simpa [u,
      physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2] using
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeUncenteredBoundaryPairL2_orthonormal
        (halfExtent n) N hN2
  have hCenteredOutside :
      ∃ k : Fin 2, finiteVacuumCentered vac (u k) ∉ ℝ ∙ top := by
    exact
      exists_finiteVacuumCentered_not_mem_span_singleton_of_orthonormal_two
        vac top u hvacNorm (by simpa [vac, top] using hOverlap) hu
  rcases hCenteredOutside with ⟨k, hkOutside⟩
  refine ⟨k, ?_⟩
  intro hprojZero
  let TT :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
      (halfExtent n) N hN (beta n) (hbeta n)
  let centered :=
    physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN) (hN2 := hN2)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n
  have hdecomp :=
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPair_top_add_nonTopProjection
      (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) k n
  have htopMem :
      physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairTopProjection
          (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) k n ∈ TT := by
    unfold
      physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairTopProjection
    exact
      Submodule.starProjection_apply_mem TT
        (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN) (hN2 := hN2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n)
  have hcenteredMem : centered ∈ TT := by
    have hEq :
        physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairTopProjection
            (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) k n =
          centered := by
      simpa [centered, hprojZero] using hdecomp
    rw [← hEq]
    exact htopMem
  have hcenteredSpan : centered ∈ ℝ ∙ top := by
    rw [←
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_eq_span_pairTopMode
        (halfExtent n) N hN (beta n) (hbeta n)]
    simpa [TT] using hcenteredMem
  have hcenteredEq :
      centered = finiteVacuumCentered vac (u k) := by
    simpa [centered, vac, u] using
      physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2_eq_finiteVacuumCentered
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n
  apply hkOutside
  rw [← hcenteredEq]
  exact hcenteredSpan

end VacuumNormalizedProjectedNonzeroReduction

end

end MathlibAnalytic
end MGAP4D
