import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGramPhysicalRank
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# P4-Q2-AF3: genuine finite Wilson physical-coordinate singular values

The original frozen-Wilson all-link innovation synthesis is retained.
Its independent physical realization is identified with standard
finite-dimensional real Euclidean coordinates by the ACTUAL orthonormal
basis from AF1.

We apply mathlib's finite-dimensional singular-value API to the map
obtained only by conjugating the actual synthesis with exact linear
equivalences and the physical-coordinate isometry. The positive
singular-value support has size exactly rank of the ORIGINAL Gram
matrix, not rank of an independent proxy.

For each finite depth, every nonzero singular value is positive.
Neither a depth/volume-uniform positive lower bound, nor a continuum
mass gap, is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter Matrix
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 850000

/-- The REAL physical synthesis expressed in the standard coefficient
Euclidean norm and the ACTUAL orthonormal physical range coordinates.
This is an exact coordinate change of AD's original synthesis. -/
noncomputable def p4Q2AG_realFinitePhysicalCoordinateSynthesis
    {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (v : ι → E) :
    EuclideanSpace ℝ ι →ₗ[ℝ]
      EuclideanSpace ℝ
        (Fin (Module.finrank ℝ (p4Q2AD_realFiniteSynthesis v).range)) := by
  let T := p4Q2AD_realFiniteSynthesis v
  let Φ := p4Q2AE_realFiniteSynthesisPhysicalOrthonormalCoordinates v
  let e := WithLp.linearEquiv 2 ℝ (ι → ℝ)
  exact Φ.toLinearEquiv.toLinearMap.comp
    (T.rangeRestrict.comp e.toLinearMap)

/-- Every independent physical coordinate is realized by some
coefficient combination of the original vectors. -/
theorem p4Q2AG_realFinitePhysicalCoordinateSynthesis_surjective
    {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (v : ι → E) :
    Function.Surjective (p4Q2AG_realFinitePhysicalCoordinateSynthesis v) := by
  classical
  let T := p4Q2AD_realFiniteSynthesis v
  let Φ := p4Q2AE_realFiniteSynthesisPhysicalOrthonormalCoordinates v
  let e := WithLp.linearEquiv 2 ℝ (ι → ℝ)
  intro y
  obtain ⟨x, hx⟩ := Φ.surjective y
  obtain ⟨a, ha⟩ := x.property
  refine ⟨e.symm a, ?_⟩
  change Φ (T.rangeRestrict (e (e.symm a))) = y
  rw [e.apply_symm_apply]
  have hSub : T.rangeRestrict a = x := by
    apply Subtype.ext
    exact ha
  rw [hSub, hx]

/-- The exact number of positive singular values is the number of
independent realized physical vectors, not the number of coefficients. -/
theorem p4Q2AG_realFinitePhysicalCoordinateSynthesis_singularValues_pos_iff
    {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (v : ι → E) (j : ℕ) :
    0 < (p4Q2AG_realFinitePhysicalCoordinateSynthesis v).singularValues j ↔
      j < Module.finrank ℝ (p4Q2AD_realFiniteSynthesis v).range := by
  classical
  let F := p4Q2AG_realFinitePhysicalCoordinateSynthesis v
  have hRange : F.range = ⊤ := LinearMap.range_eq_top.mpr
    (p4Q2AG_realFinitePhysicalCoordinateSynthesis_surjective v)
  have hSV := F.singularValues_pos_iff_lt_finrank_range (n := j)
  change 0 < F.singularValues j ↔
    j < Module.finrank ℝ (p4Q2AD_realFiniteSynthesis v).range
  rw [hRange, finrank_top, finrank_euclideanSpace_fin] at hSV
  exact hSV

/-- Above physical rank there are only zero singular values. -/
theorem p4Q2AG_realFinitePhysicalCoordinateSynthesis_singularValues_eq_zero_iff
    {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (v : ι → E) (j : ℕ) :
    (p4Q2AG_realFinitePhysicalCoordinateSynthesis v).singularValues j = 0 ↔
      Module.finrank ℝ (p4Q2AD_realFiniteSynthesis v).range ≤ j := by
  have hPos := p4Q2AG_realFinitePhysicalCoordinateSynthesis_singularValues_pos_iff v j
  have hNonneg :=
    (p4Q2AG_realFinitePhysicalCoordinateSynthesis v).singularValues_nonneg j
  constructor
  · intro hZero
    have hn : ¬ j < Module.finrank ℝ (p4Q2AD_realFiniteSynthesis v).range := by
      intro hj
      exact (ne_of_gt (hPos.mpr hj)) hZero
    omega
  · intro hj
    have hn : ¬ 0 < (p4Q2AG_realFinitePhysicalCoordinateSynthesis v).singularValues j :=
      fun hh => Nat.not_lt.mpr hj (hPos.mp hh)
    exact le_antisymm (le_of_not_gt hn) hNonneg

local instance p4AGGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4AGCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4AGSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4AGMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4AGBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4AGLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4AGComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- Actual original-Wilson physical finite-coordinate synthesis:
the same frozen-beta posterior innovations, now in mathlib Hilbert
coordinates. Its domain is the standard coefficient Euclidean space. -/
noncomputable def fineRightKrylov_originalPhysicalCoordinateSynthesis
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) :=
  p4Q2AG_realFinitePhysicalCoordinateSynthesis
    (fun j : Fin (r+1) =>
      WithLp.toLp 2
        (fun e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n+1)) =>
          physicalOriginalReceiverPosteriorInnovation
            (halfExtent (n+1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) e
            (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n (j : ℕ))))

/-- Every strictly positive singular value of the AUTHENTIC
finite Wilson synthesis corresponds to the original Gram rank. -/
theorem fineRightKrylov_originalPhysicalCoordinateSynthesis_singularValues_pos_iff_gramRank
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r j : ℕ) :
    0 < (fineRightKrylov_originalPhysicalCoordinateSynthesis
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r).singularValues j ↔
      j < (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r).rank := by
  let V (k : Fin (r+1)) :=
    WithLp.toLp 2
      (fun e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n+1)) =>
        physicalOriginalReceiverPosteriorInnovation
          (halfExtent (n+1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) e
          (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n (k : ℕ)))
  have hRank :=
    fineRightKrylov_originalGram_rank_eq_physicalImage_finrank
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have hSV :=
    p4Q2AG_realFinitePhysicalCoordinateSynthesis_singularValues_pos_iff V j
  rw [hRank]
  exact hSV

/-- At every fixed finite r with nonzero physical rank, the last
positive singular value is strictly positive; no uniformity is stated. -/
theorem fineRightKrylov_originalPhysicalCoordinateSynthesis_lastPositiveSingularValue_pos
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ)
    (hRank : 0 < (fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r).rank) :
    0 < (fineRightKrylov_originalPhysicalCoordinateSynthesis
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r).singularValues
        ((fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r).rank - 1) := by
  apply (fineRightKrylov_originalPhysicalCoordinateSynthesis_singularValues_pos_iff_gramRank
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r _).mpr
  omega

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
