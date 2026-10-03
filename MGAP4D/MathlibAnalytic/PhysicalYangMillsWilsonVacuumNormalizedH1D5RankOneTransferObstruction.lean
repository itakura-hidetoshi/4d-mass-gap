import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5OrthogonalRestrictionZeroObstruction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceSimplicity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalCenteredTransferConvergence
import MGAP4D.MathlibAnalytic.WightmanOSVacuumRankOneProjection
import MGAP4D.MathlibAnalytic.WightmanOSVacuumStarProjectionStructure
import Mathlib.Tactic

/-!
# H1-D5 forces the finite physical one-slab transfer to be rank one

#5040 proves that H1-D5 forces the normalized physical one-slab transfer to
vanish on the orthogonal complement of its full top eigenspace.

For a symmetric operator, the norm of the centered operator
`S - P_top` is exactly the norm of that orthogonal restriction.  Hence #5040
forces

  `S = P_top`.

#5012 identifies the full finite-volume top eigenspace with the line generated
by the normalized physical top eigenvector.  Mathlib's orthogonal projection
onto that unit line is the rank-one operator `|Ω><Ω|`.  Therefore H1-D5
forces

  `S = |Ω><Ω|`

at every finite scale.  Undoing the operator-norm normalization gives the raw
statement

  `T = ‖T‖ |Ω><Ω|`.

Thus a single finite scale at which the actual Wilson one-slab transfer is not
this rank-one operator refutes H1-D5.

No new model assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

local instance h1d5RankOneTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance h1d5RankOneCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance h1d5RankOneSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance h1d5RankOneMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance h1d5RankOneBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance h1d5RankOneSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance h1d5RankOnePhysicalSliceComplete (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- If a symmetric real-Hilbert operator vanishes on the orthogonal complement
of its eigenvalue-one space, then it is exactly the orthogonal projection onto
that top eigenspace. -/
theorem realHilbertSymmetric_eq_topEigenspaceProjection_of_orthogonalRestriction_eq_zero
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hRzero :
      realHilbertTopEigenspaceOrthogonalRestriction S hS = 0) :
    S = realHilbertTopEigenspaceProjection S := by
  have hnorm :=
    realHilbertCenteredOperator_norm_eq_orthogonalRestriction S hS
  have hRnorm :
      ‖realHilbertTopEigenspaceOrthogonalRestriction S hS‖ = 0 := by
    rw [ContinuousLinearMap.opNorm_zero_iff]
    exact hRzero
  have hcenterNorm :
      ‖S - realHilbertTopEigenspaceProjection S‖ = 0 :=
    hnorm.trans hRnorm
  have hzero :
      S - realHilbertTopEigenspaceProjection S = 0 :=
    norm_eq_zero.mp hcenterNorm
  exact sub_eq_zero.mp hzero

/-- The concrete finite-volume normalized physical one-slab transfer is the
canonical top projection whenever its top-orthogonal restriction vanishes. -/
theorem
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_eq_topSpectralProjection_of_topOrthogonalRestriction_eq_zero
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hRzero :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta = 0) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let hS :
      (S :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsSymmetric := by
    simpa only [S] using
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
        H N hN beta hbeta
  have hR :
      realHilbertTopEigenspaceOrthogonalRestriction S hS = 0 := by
    simpa only [
      S, hS,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    ] using hRzero
  have hEq :=
    realHilbertSymmetric_eq_topEigenspaceProjection_of_orthogonalRestriction_eq_zero
      S hS hR
  simpa only [
    S,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
  ] using hEq

/-- The concrete full top projection is rank one because #5012 identifies the
top eigenspace with the line generated by the chosen normalized top vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_eq_rankOne_topEigenvector
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta =
      InnerProductSpace.rankOne ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN beta hbeta) := by
  let G :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
  let P : G →L[ℝ] G :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H N hN beta hbeta
  let Omega : G :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      H N hN beta hbeta
  let Q : G →L[ℝ] G :=
    InnerProductSpace.rankOne ℝ Omega Omega
  have hOmega : ‖Omega‖ = 1 := by
    simpa only [G, Omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
        H N hN beta hbeta
  have hPStar : IsStarProjection P := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_isSymmetricProjection
        H N hN beta hbeta).isStarProjection
  have hQStar : IsStarProjection Q := by
    exact real_unit_rankOne_isStarProjection Omega hOmega
  have hPRange :
      P.range =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
          H N hN beta hbeta := by
    simpa only [P, G] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_range
        H N hN beta hbeta
  have hTop :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
          H N hN beta hbeta =
        ℝ ∙ Omega := by
    simpa only [G, Omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_topEigenvector
        (H := H) (N := N) hN beta hbeta
  have hQRange : Q.range = ℝ ∙ Omega := by
    simpa only [Q, G] using real_unit_rankOne_range Omega hOmega
  have hPQ : P = Q := by
    exact
      (ContinuousLinearMap.IsStarProjection.ext_iff hPStar hQStar).2
        (hPRange.trans (hTop.trans hQRange.symm))
  simpa only [P, Q, G, Omega] using hPQ

/-- Zero top-orthogonal dynamics is therefore equivalent to a rank-one
normalized physical transfer. -/
theorem
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_eq_rankOne_topEigenvector_of_topOrthogonalRestriction_eq_zero
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hRzero :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta = 0) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta =
      InnerProductSpace.rankOne ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN beta hbeta) := by
  calc
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta :=
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_eq_topSpectralProjection_of_topOrthogonalRestriction_eq_zero
        H N hN beta hbeta hRzero
    _ =
      InnerProductSpace.rankOne ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN beta hbeta) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_eq_rankOne_topEigenvector
        H N hN beta hbeta

/-- Raw version: if the normalized top-orthogonal restriction vanishes, the
actual raw physical one-slab transfer is its top norm times the rank-one vacuum
projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_eq_norm_smul_rankOne_topEigenvector_of_topOrthogonalRestriction_eq_zero
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hRzero :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta = 0) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ •
        InnerProductSpace.rankOne ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
            H N hN beta hbeta) := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      H N hN beta hbeta
  let P :=
    InnerProductSpace.rankOne ℝ Omega Omega
  have hnorm : 0 < ‖T‖ := by
    simpa only [T] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta
  have hNormalized :
      ‖T‖⁻¹ • T = P := by
    change
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta =
        InnerProductSpace.rankOne ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
            H N hN beta hbeta)
    exact
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_eq_rankOne_topEigenvector_of_topOrthogonalRestriction_eq_zero
        H N hN beta hbeta hRzero
  apply ContinuousLinearMap.ext
  intro x
  have hx :=
    congrArg
      (fun A :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N =>
        A x)
      hNormalized
  change ‖T‖⁻¹ • T x = P x at hx
  have hRawx :=
    real_inv_smul_eq_smul_rescale
      ‖T‖ 1 hnorm.ne' (T x) (P x)
      (by simpa only [one_smul] using hx)
  change T x = ‖T‖ • P x
  simpa only [mul_one] using hRawx

section PhysicalWilsonH1D5RankOne

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

/-- H1-D5 forces the normalized finite Wilson one-slab physical transfer to be
the rank-one projection onto the chosen normalized top mode at every scale. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_normalizedPhysicalOneSlabTransfer_rankOne
    (hCompat :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n) =
      InnerProductSpace.rankOne ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          (halfExtent n) N hN (beta n) (hbeta n))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          (halfExtent n) N hN (beta n) (hbeta n)) := by
  have hRzero :=
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_topOrthogonalRestriction_eq_zero
      Q hInvariant C hCompat n
  exact
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_eq_rankOne_topEigenvector_of_topOrthogonalRestriction_eq_zero
      (halfExtent n) N hN (beta n) (hbeta n) hRzero

/-- Raw rank-one consequence of H1-D5. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_physicalOneSlabTransfer_norm_smul_rankOne
    (hCompat :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n)‖ •
        InnerProductSpace.rankOne ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
            (halfExtent n) N hN (beta n) (hbeta n))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
            (halfExtent n) N hN (beta n) (hbeta n)) := by
  have hRzero :=
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_topOrthogonalRestriction_eq_zero
      Q hInvariant C hCompat n
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_eq_norm_smul_rankOne_topEigenvector_of_topOrthogonalRestriction_eq_zero
      (halfExtent n) N hN (beta n) (hbeta n) hRzero

/-- A single finite scale at which the normalized physical one-slab Wilson
transfer is not the rank-one top projection refutes H1-D5. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_normalizedPhysicalOneSlabTransfer_ne_rankOne
    (n : ℕ)
    (hne :
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n) ≠
        InnerProductSpace.rankOne ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
            (halfExtent n) N hN (beta n) (hbeta n))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
            (halfExtent n) N hN (beta n) (hbeta n))) :
    ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C := by
  intro hCompat
  exact hne
    (physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_normalizedPhysicalOneSlabTransfer_rankOne
      Q hInvariant C hCompat n)

/-- Audit-visible package for the exact rank-one consequence of H1-D5. -/
structure PhysicalYangMillsVacuumNormalizedH1D5RankOneTransferObstructionPackage : Prop where
  normalizedRankOne :
    ∀ (_hCompat :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C),
      ∀ n : ℕ,
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n) =
          InnerProductSpace.rankOne ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
              (halfExtent n) N hN (beta n) (hbeta n))
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
              (halfExtent n) N hN (beta n) (hbeta n))
  rawRankOne :
    ∀ (_hCompat :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C),
      ∀ n : ℕ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n) =
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              (halfExtent n) N hN (beta n) (hbeta n)‖ •
            InnerProductSpace.rankOne ℝ
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
                (halfExtent n) N hN (beta n) (hbeta n))
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
                (halfExtent n) N hN (beta n) (hbeta n))

theorem physicalYangMillsVacuumNormalizedH1D5RankOneTransferObstructionPackage :
    PhysicalYangMillsVacuumNormalizedH1D5RankOneTransferObstructionPackage
      (Q := Q) (hInvariant := hInvariant) (C := C) :=
  { normalizedRankOne := by
      intro hCompat n
      exact
        physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_normalizedPhysicalOneSlabTransfer_rankOne
          Q hInvariant C hCompat n
    rawRankOne := by
      intro hCompat n
      exact
        physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_physicalOneSlabTransfer_norm_smul_rankOne
          Q hInvariant C hCompat n }

end PhysicalWilsonH1D5RankOne

end

end MathlibAnalytic
end MGAP4D
