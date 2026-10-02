import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5StrictPositiveSubtopEigenObstruction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedPairCompactness
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPoincareDefect
import Mathlib.Tactic

/-!
# H1-D5 forces the normalized top-orthogonal one-slab restriction to vanish

#5039 shows that any strictly positive physical one-slab eigenvalue below the
top norm contradicts H1-D5.

For the normalized physical transfer, the full top-eigenspace orthogonal
restriction is already positive, compact, and strictly contractive.  Therefore,
if that restriction is nonzero, Mathlib compact spectral theory produces a unit
top eigenvector of the restriction at its strictly positive norm.  Since that
norm is strictly below one, rescaling back by the positive raw top norm gives
exactly the strict-positive subtop raw eigenmode consumed by #5039.

Thus the remaining H1-D5 seam has an even sharper necessary condition:

  H1-D5 => R_n = 0

at every finite scale, where R_n is the normalized physical one-slab transfer
restricted to the full top-eigenspace orthogonal complement.

No new compatibility, spectrum, or model assumption is added.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

local instance h1d5OrthogonalZeroTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance h1d5OrthogonalZeroCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance h1d5OrthogonalZeroSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance h1d5OrthogonalZeroMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance h1d5OrthogonalZeroBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance h1d5OrthogonalZeroSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance h1d5OrthogonalZeroPhysicalSliceComplete (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance h1d5OrthogonalZeroExcitationSliceComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
  ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
    H N hN beta hbeta).isClosed_orthogonal).completeSpace_coe

/-- A nonzero positive compact operator on a complete real Hilbert space has a
unit eigenvector at its strictly positive operator norm. -/
theorem realHilbertPositiveCompact_nonzero_exists_unit_topEigenvector
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (R : E →L[ℝ] E)
    (hPositive : (R : E →ₗ[ℝ] E).IsPositive)
    (hCompact : IsCompactOperator R)
    (hRne : R ≠ 0) :
    ∃ v : E,
      ‖v‖ = 1 ∧
      0 < ‖R‖ ∧
      R v = ‖R‖ • v := by
  have hex : ∃ u : E, R u ≠ 0 := by
    by_contra h
    push_neg at h
    apply hRne
    apply ContinuousLinearMap.ext
    intro u
    simpa using h u
  obtain ⟨u, huR⟩ := hex
  have hu : u ≠ 0 := by
    intro hu0
    apply huR
    rw [hu0, map_zero]
  let unit : E := ‖u‖⁻¹ • u
  have hunit : ‖unit‖ = 1 := by
    have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
    dsimp [unit]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hunorm]
    exact inv_mul_cancel₀ hunorm.ne'
  have hnormPos : 0 < ‖R‖ :=
    norm_pos_iff.mpr hRne
  obtain ⟨v, hvnorm, hveig⟩ :=
    realHilbertPositiveCompact_exists_unit_topEigenvector
      R unit hunit hPositive hCompact
  exact ⟨v, hvnorm, hnormPos, hveig⟩

/-- The concrete normalized physical top-orthogonal one-slab restriction is
a positive operator on its native subtype Hilbert structure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_isPositive
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta →L[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta) :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta).IsPositive := by
  refine ⟨?_, ?_⟩
  · intro x y
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_inner_symm
        H N hN beta hbeta x y
  · intro x
    change
      0 ≤ RCLike.re
        (inner ℝ
          (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta
            (x :
              periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                H N))
          (x :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              H N))
    exact
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isPositive
        H N hN beta hbeta).re_inner_nonneg_left _

/-- If the normalized physical top-orthogonal restriction is nonzero, it
theorem-generates a strictly positive raw physical one-slab eigenmode strictly
below the raw top norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_exists_strictPositiveSubtopEigenmode_of_topOrthogonalRestriction_ne_zero
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hRne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta ≠ 0) :
    ∃ rho : ℝ,
      ∃ f :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
        f ≠ 0 ∧
        0 < rho ∧
        rho <
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖ ∧
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta f =
          rho • f := by
  let G :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  obtain ⟨v, hvnorm, hqpos, hveig⟩ :=
    realHilbertPositiveCompact_nonzero_exists_unit_topEigenvector
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_isPositive
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_isCompact
        H N hN beta hbeta)
      hRne
  let q : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  have hvneK : v ≠ 0 := by
    intro hv0
    rw [hv0, norm_zero] at hvnorm
    norm_num at hvnorm
  have hvneG : (v : G) ≠ 0 := by
    intro hv0
    apply hvneK
    exact Subtype.ext hv0
  have hSEig :
      S (v : G) = q • (v : G) := by
    have hcoe :=
      congrArg
        (fun z :
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            H N hN beta hbeta =>
          (z : G))
        hveig
    change
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta (v : G) =
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ • (v : G) at hcoe
    simpa [S, q] using hcoe
  have hTpos : 0 < ‖T‖ := by
    simpa [T] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta
  have hRaw :
      T (v : G) =
        (‖T‖ * q) • (v : G) := by
    change ‖T‖⁻¹ • T (v : G) = q • (v : G) at hSEig
    have hscaled :=
      congrArg (fun z : G => ‖T‖ • z) hSEig
    rw [smul_smul, mul_inv_cancel₀ hTpos.ne', one_smul, smul_smul] at hscaled
    exact hscaled
  have hqlt : q < 1 := by
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta
  have hrhoPos : 0 < ‖T‖ * q := by
    exact mul_pos hTpos (by simpa [q] using hqpos)
  have hrhoTop : ‖T‖ * q < ‖T‖ := by
    calc
      ‖T‖ * q < ‖T‖ * 1 := (mul_lt_mul_left hTpos).2 hqlt
      _ = ‖T‖ := mul_one _
  refine ⟨‖T‖ * q, (v : G), hvneG, hrhoPos, ?_, ?_⟩
  · simpa [T] using hrhoTop
  · simpa [T] using hRaw

section PhysicalWilsonH1D5OrthogonalZero

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

/-- A nonzero normalized physical top-orthogonal restriction at even one scale
refutes H1-D5. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_topOrthogonalRestriction_ne_zero
    (n : ℕ)
    (hRne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n) ≠ 0) :
    ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C := by
  obtain ⟨rho, f, hf, hrho, hrhoTop, hEigen⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_exists_strictPositiveSubtopEigenmode_of_topOrthogonalRestriction_ne_zero
      (halfExtent n) N hN (beta n) (hbeta n) hRne
  exact
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_strictPositiveSubtopEigenmode
      Q hInvariant C n rho f hf hrho hrhoTop hEigen

/-- Therefore H1-D5 forces the normalized physical top-orthogonal one-slab
restriction to be the zero operator at every finite scale. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_topOrthogonalRestriction_eq_zero
    (hCompat :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n) = 0 := by
  by_contra hRne
  exact
    (physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_topOrthogonalRestriction_ne_zero
      Q hInvariant C n hRne) hCompat

/-- Audit-visible package for the exact remaining one-slice obstruction. -/
structure PhysicalYangMillsVacuumNormalizedH1D5OrthogonalRestrictionZeroObstructionPackage : Prop where
  compatibilityForcesZero :
    ∀ (_hCompat :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C),
      ∀ n : ℕ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n) = 0
  nonzeroRestrictionObstructs :
    ∀ n : ℕ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n) ≠ 0 →
      ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C

theorem physicalYangMillsVacuumNormalizedH1D5OrthogonalRestrictionZeroObstructionPackage :
    PhysicalYangMillsVacuumNormalizedH1D5OrthogonalRestrictionZeroObstructionPackage
      (Q := Q) (hInvariant := hInvariant) (C := C) :=
  { compatibilityForcesZero := by
      intro hCompat n
      exact
        physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_topOrthogonalRestriction_eq_zero
          Q hInvariant C hCompat n
    nonzeroRestrictionObstructs := by
      intro n hRne
      exact
        physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_topOrthogonalRestriction_ne_zero
          Q hInvariant C n hRne }

end PhysicalWilsonH1D5OrthogonalZero

end

end MathlibAnalytic
end MGAP4D
