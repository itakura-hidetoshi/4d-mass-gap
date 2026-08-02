import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalL2Isometry
import Mathlib.MeasureTheory.Function.LpSpace.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance boundaryMarginalGibbsNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryMarginalGibbsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryMarginalGibbsCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryMarginalGibbsSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryMarginalGibbsMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryMarginalGibbsBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Pullback along boundary restriction embeds the interacting boundary
marginal `L²` isometrically into the actual finite Wilson Gibbs `L²` space. -/
noncomputable def periodicHypercubicEvenBoundaryMarginalToGibbsL2Isometry
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryMarginalL2 H N hN beta hbeta →ₗᵢ[ℝ]
      Lp ℝ 2
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure :=
  Lp.compMeasurePreservingₗᵢ
    (E := ℝ) (p := 2) ℝ
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction
    (periodicHypercubicEvenSpecialUnitaryBoundaryRestrictionMeasurePreserving
      H N hN beta hbeta)

/-- The marginal pullback has the expected representative: composition with
boundary restriction. -/
theorem periodicHypercubicEvenBoundaryMarginalToGibbsL2Isometry_coeFn
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryMarginalL2 H N hN beta hbeta) :
    periodicHypercubicEvenBoundaryMarginalToGibbsL2Isometry
        H N hN beta hbeta f =ᵐ[
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure]
      f ∘ (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction := by
  exact Lp.coeFn_compMeasurePreserving f
    (periodicHypercubicEvenSpecialUnitaryBoundaryRestrictionMeasurePreserving
      H N hN beta hbeta)

/-- The canonical OS-compatible boundary analysis is reciprocal-vacuum
normalization followed by pullback along the actual boundary restriction. -/
noncomputable def periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
      Lp ℝ 2
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure :=
  let J := periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry
    H N hN beta hbeta
  let U := periodicHypercubicEvenBoundaryMarginalToGibbsL2Isometry
    H N hN beta hbeta
  LinearIsometry.mk
    (U.toLinearMap.comp J.toLinearMap)
    (fun f => by
      rw [U.norm_map, J.norm_map])

@[simp] theorem periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_apply
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta f =
      periodicHypercubicEvenBoundaryMarginalToGibbsL2Isometry
        H N hN beta hbeta
        (periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry
          H N hN beta hbeta f) :=
  rfl

end

end MathlibAnalytic
end MGAP4D
