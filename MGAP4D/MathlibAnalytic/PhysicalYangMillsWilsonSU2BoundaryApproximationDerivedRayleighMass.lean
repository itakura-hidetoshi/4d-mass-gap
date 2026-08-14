import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2BoundaryRangeDerivedRayleighMass
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set Topology
open scoped InnerProduct InnerProductSpace

noncomputable section

/-- The set-theoretic range of a linear isometry from a complete normed space
is closed, so any norm-limit of actual image vectors is again an actual image
vector.

Keeping the proof on `Set.range` avoids conflating the closed topological image
with the `Submodule` returned by `LinearMap.range`.  No surjectivity is assumed. -/
theorem realLinearIsometry_mem_setRange_of_tendsto
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (J : E →ₗᵢ[ℝ] F) (u : ℕ → E) (y : F)
    (h : Tendsto (fun m => J (u m)) atTop (𝓝 y)) :
    y ∈ Set.range (fun x : E => J x) := by
  have hComplete : IsComplete (Set.range (fun x : E => J x)) :=
    J.isometry.isUniformInducing.isComplete_range
  have hClosed : IsClosed (Set.range (fun x : E => J x)) := hComplete.isClosed
  apply hClosed.mem_of_tendsto h
  exact Filter.Eventually.of_forall fun m => ⟨u m, rfl⟩

private theorem boundaryApproximationDerivedRayleighMassTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryApproximationDerivedRayleighMassTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryApproximationDerivedRayleighMassCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryApproximationDerivedRayleighMassSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryApproximationDerivedRayleighMassMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryApproximationDerivedRayleighMassBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryApproximationDerivedRayleighMassSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

private abbrev boundaryApproximationPreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 boundaryApproximationDerivedRayleighMassTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
    boundaryApproximationDerivedRayleighMassTwoRankPositive beta hbeta
    Q.toWeakStarBridge hInvariant n

/-- It is enough to approximate the concrete density-corrected normalized-trace
boundary Haar mode by images of genuine completed OS physical states.

Because the completed boundary-moment map is a linear isometry and the OS
physical Hilbert space is complete, its image is closed.  Hence an `L²` limit
of reconstructed physical boundary moments is itself reconstructed.  This
replaces the abstract exact-range premise by a concrete approximation target
without assuming surjectivity. -/
theorem normalizedTracePolynomial_boundaryHaar_mem_physicalHilbertBoundaryMoment_range_of_tendsto
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 boundaryApproximationDerivedRayleighMassTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ) (c : Fin (k + 1) → ℝ)
    (psi : ℕ → (boundaryApproximationPreHilbert Q hInvariant n).PhysicalHilbert)
    (hApprox : Tendsto (fun m => Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n (psi m)) atTop
      (𝓝 (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2 (halfExtent n) (beta n) (hbeta n) k c))) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
      LinearMap.range (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n).toLinearMap := by
  rcases realLinearIsometry_mem_setRange_of_tendsto
      (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n) psi
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
        (halfExtent n) (beta n) (hbeta n) k c) hApprox with
    ⟨phi, hphi⟩
  exact ⟨phi, hphi⟩

/-- The actual reconstructed Yang--Mills variational mass is therefore
nonnegative once the theorem-generated Wilson boundary mode is obtainable as
an `L²` limit of completed OS physical boundary moments.

The former exact range assumption disappears: closedness of the isometric OS
image supplies it automatically.  The remaining obligation is now the
constructive one appropriate for the full model -- produce the physical
approximating sequence. -/
theorem normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_boundaryHaar_tendsto
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 boundaryApproximationDerivedRayleighMassTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility Q hInvariant)
    (n k : ℕ) (c : Fin (k + 1) → ℝ)
    (hzero : inner ℝ (periodicHypercubicEvenBoundaryMarginalVacuumL2 (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2 (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hpos : 0 < inner ℝ (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator (halfExtent n) 2
      boundaryApproximationDerivedRayleighMassTwoRankPositive (beta n) (hbeta n)
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2 (halfExtent n) (beta n) (hbeta n) k c))
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2 (halfExtent n) (beta n) (hbeta n) k c))
    (psi : ℕ → (boundaryApproximationPreHilbert Q hInvariant n).PhysicalHilbert)
    (hApprox : Tendsto (fun m => Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n (psi m)) atTop
      (𝓝 (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2 (halfExtent n) (beta n) (hbeta n) k c)))
    (T : (boundaryApproximationPreHilbert Q hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    0 ≤ T.physicalYangMillsMass := by
  have hRange :=
    Q.normalizedTracePolynomial_boundaryHaar_mem_physicalHilbertBoundaryMoment_range_of_tendsto
      hInvariant n k c psi hApprox
  exact
    Q.normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_boundaryHaar_range_of_factorized_inner_self_pos
      hInvariant U n k c hzero hpos hRange T hSelf

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
