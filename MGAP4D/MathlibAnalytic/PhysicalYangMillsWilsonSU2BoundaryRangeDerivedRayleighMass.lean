import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ActualAnalysisStrictPhysicalExcitation
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedMassExcitationWitness
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedRayleighMass
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

private theorem boundaryRangeDerivedRayleighMassTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryRangeDerivedRayleighMassTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryRangeDerivedRayleighMassCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryRangeDerivedRayleighMassSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryRangeDerivedRayleighMassMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryRangeDerivedRayleighMassBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryRangeDerivedRayleighMassSU2Nontrivial :
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

/-- A theorem-generated centered SU(2) Wilson boundary mode gives a genuine
nonzero vector in the completed OS vacuum-orthogonal sector as soon as that
**boundary mode itself** lies in the range of the already-constructed completed
boundary-moment isometry `Ĵ_n`.

This is strictly downstream of the earlier open-half realization condition:
there is no requirement that the Wilson analysis output, or the raw analysis
witness, admit a preimage under `positiveHalfL2LinearMap`.  The proof instead
uses strict factorized Wilson positivity, the exact completed linear isometry,
vacuum-unit compatibility, and the already-proved density-transport
centeredness of the normalized-trace polynomial.

Thus no static Wilson Gram operator is identified with Euclidean time
translation and no new mass, decay, coercivity, determinant, or projective
assumption is introduced. -/
theorem normalizedTracePolynomial_exists_nonzero_vacuumOrthogonalPhysicalState_of_boundaryHaar_range_of_factorized_inner_self_pos
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 boundaryRangeDerivedRayleighMassTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility Q hInvariant)
    (n k : ℕ) (c : Fin (k + 1) → ℝ)
    (hzero : inner ℝ (periodicHypercubicEvenBoundaryMarginalVacuumL2 (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2 (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hpos : 0 < inner ℝ (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator (halfExtent n) 2
      boundaryRangeDerivedRayleighMassTwoRankPositive (beta n) (hbeta n)
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2 (halfExtent n) (beta n) (hbeta n) k c))
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2 (halfExtent n) (beta n) (hbeta n) k c))
    (hBoundaryRange : periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
      (halfExtent n) (beta n) (hbeta n) k c ∈ LinearMap.range
        (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n).toLinearMap) :
    let Pn := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
      boundaryRangeDerivedRayleighMassTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n
    ∃ psi : Pn.VacuumOrthogonalHilbert, psi ≠ 0 := by
  dsimp only
  let Pn := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 boundaryRangeDerivedRayleighMassTwoRankPositive beta hbeta
    Q.toWeakStarBridge hInvariant n
  let J := Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
  let f := periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
    (halfExtent n) (beta n) (hbeta n) k c
  change f ∈ LinearMap.range J.toLinearMap at hBoundaryRange
  rcases hBoundaryRange with ⟨phi, hphi⟩
  have hphiImage : J phi = f := by
    exact hphi
  have hAnalysisNe :
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        (halfExtent n) 2 boundaryRangeDerivedRayleighMassTwoRankPositive
        (beta n) (hbeta n) f ≠ 0 := by
    exact
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_apply_ne_zero_of_factorized_inner_self_pos
        (beta n) (hbeta n) f hpos
  have hfNe : f ≠ 0 := by
    intro hf
    apply hAnalysisNe
    simp [hf]
  have hphiNe : phi ≠ 0 := by
    intro hphiZero
    apply hfNe
    calc
      f = J phi := hphiImage.symm
      _ = J 0 := by rw [hphiZero]
      _ = 0 := map_zero J
  have hVacImage :
      J Pn.vacuum = periodicHypercubicEvenBoundaryVacuumHaarL2
        (halfExtent n) (beta n) (hbeta n) := by
    change Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        (Pn.physicalState Pn.vacuumObservable) =
      periodicHypercubicEvenBoundaryVacuumHaarL2 (halfExtent n) (beta n) (hbeta n)
    rw [Q.physicalHilbertBoundaryMomentLinearIsometry_physicalState]
    apply Lp.ext
    exact
      (U.canonicalBoundaryMomentL2_vacuum_coeFn n).trans
        (periodicHypercubicEvenBoundaryVacuumHaarL2_coeFn
          (halfExtent n) (beta n) (hbeta n)).symm
  have hfCentered : inner ℝ
      (periodicHypercubicEvenBoundaryVacuumHaarL2 (halfExtent n) (beta n) (hbeta n)) f = 0 := by
    exact periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2_centered
      (halfExtent n) (beta n) (hbeta n) k c hzero
  have hImageOrth : inner ℝ (J Pn.vacuum) (J phi) = 0 := by
    rw [hVacImage, hphiImage]
    exact hfCentered
  have hOrth : inner ℝ Pn.vacuum phi = 0 := by
    simpa using hImageOrth
  have hphiMem : phi ∈ Pn.vacuumOrthogonal := by
    rw [Pn.mem_vacuumOrthogonal_iff]
    exact hOrth
  refine ⟨⟨phi, hphiMem⟩, ?_⟩
  intro hzeroPsi
  apply hphiNe
  exact congrArg Subtype.val hzeroPsi

/-- Boundary-range realization already suffices to make the closed physical
Hamiltonian excitation domain nonempty.  Domain membership is generated from
self-adjointness and density; it is not an additional Wilson-side assumption. -/
noncomputable def normalizedTracePolynomial_excitationDomainWitness_of_boundaryHaar_range_of_factorized_inner_self_pos
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 boundaryRangeDerivedRayleighMassTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility Q hInvariant)
    (n k : ℕ) (c : Fin (k + 1) → ℝ)
    (hzero : inner ℝ (periodicHypercubicEvenBoundaryMarginalVacuumL2 (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2 (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hpos : 0 < inner ℝ (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator (halfExtent n) 2
      boundaryRangeDerivedRayleighMassTwoRankPositive (beta n) (hbeta n)
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2 (halfExtent n) (beta n) (hbeta n) k c))
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2 (halfExtent n) (beta n) (hbeta n) k c))
    (hBoundaryRange : periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
      (halfExtent n) (beta n) (hbeta n) k c ∈ LinearMap.range
        (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n).toLinearMap)
    (T : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
      boundaryRangeDerivedRayleighMassTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) : T.PhysicalYangMillsExcitationDomainWitness := by
  let Pn := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 boundaryRangeDerivedRayleighMassTwoRankPositive beta hbeta
    Q.toWeakStarBridge hInvariant n
  have hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent 2 boundaryRangeDerivedRayleighMassTwoRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  have hNonempty : Nonempty T.PhysicalYangMillsExcitationDomainWitness := by
    rcases
        Q.normalizedTracePolynomial_exists_nonzero_vacuumOrthogonalPhysicalState_of_boundaryHaar_range_of_factorized_inner_self_pos
          hInvariant U n k c hzero hpos hBoundaryRange with
      ⟨psi, hpsi⟩
    exact ⟨T.physicalYangMillsExcitationDomainWitness_of_nonzeroExcitation
      hPn hSelf psi hpsi⟩
  exact Classical.choice hNonempty

/-- Consequently the variational mass attached to the actual reconstructed
closed Yang--Mills Hamiltonian is nonnegative under the completed boundary-range
realization.  No numerical mass value is inserted here. -/
theorem normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_boundaryHaar_range_of_factorized_inner_self_pos
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 boundaryRangeDerivedRayleighMassTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility Q hInvariant)
    (n k : ℕ) (c : Fin (k + 1) → ℝ)
    (hzero : inner ℝ (periodicHypercubicEvenBoundaryMarginalVacuumL2 (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2 (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hpos : 0 < inner ℝ (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator (halfExtent n) 2
      boundaryRangeDerivedRayleighMassTwoRankPositive (beta n) (hbeta n)
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2 (halfExtent n) (beta n) (hbeta n) k c))
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2 (halfExtent n) (beta n) (hbeta n) k c))
    (hBoundaryRange : periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
      (halfExtent n) (beta n) (hbeta n) k c ∈ LinearMap.range
        (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n).toLinearMap)
    (T : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
      boundaryRangeDerivedRayleighMassTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) : 0 ≤ T.physicalYangMillsMass := by
  let W :=
    Q.normalizedTracePolynomial_excitationDomainWitness_of_boundaryHaar_range_of_factorized_inner_self_pos
      hInvariant U n k c hzero hpos hBoundaryRange T hSelf
  exact T.physicalYangMillsMass_nonneg W

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
