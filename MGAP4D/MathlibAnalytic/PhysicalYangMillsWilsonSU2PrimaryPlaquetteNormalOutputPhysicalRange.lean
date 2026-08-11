import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentSeparationCompletion

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance su2NormalPhysicalRangeTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2NormalPhysicalRangeCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2NormalPhysicalRangeSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2NormalPhysicalRangeMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2NormalPhysicalRangeBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2NormalPhysicalRangeNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private theorem su2NormalPhysicalRangeRankPositive : 0 < (2 : ℕ) := by
  norm_num

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- A single-scale physical-range bridge for the actual SU(2) Wilson normal outputs.

If the canonical analysis image `A g_j` is itself in the range of the coherent
positive-half physical pullback, then the normal output `A† A g_j` is in the
range of the actual OS boundary-moment isometry.  This is strictly weaker than
asking for arbitrary open-half `L²` surjectivity: only the finitely selected
analysis images are required to have physical carrier preimages. -/
theorem primaryPlaquetteNormalOutput_mem_boundaryMoment_range_of_analysisImage_mem_positiveHalf_range
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 su2NormalPhysicalRangeRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (j : Fin (k + 1))
    (hAnalysisRange :
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
          (halfExtent n) (beta n) (hbeta n) k j ∈
        (Q.positiveHalfL2LinearMap hInvariant n).range) :
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutput
        (halfExtent n) (beta n) (hbeta n) k j ∈
      (Q.boundaryMomentLinearIsometry hInvariant n).toLinearMap.range := by
  rcases hAnalysisRange with ⟨F, hF⟩
  refine ⟨F, ?_⟩
  have hF' :
      physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
          S D halfExtent 2 su2NormalPhysicalRangeRankPositive beta hbeta
          Q.toWeakStarBridge hInvariant n F =
        periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
          (halfExtent n) (beta n) (hbeta n) k j := by
    simpa using hF
  change Q.boundaryMomentLinearIsometry hInvariant n F =
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutput
      (halfExtent n) (beta n) (hbeta n) k j
  rw [Q.boundaryMomentLinearIsometry_apply,
    physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis,
    hF']
  exact
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutput_eq_synthesis_analysisImage
      (halfExtent n) (beta n) (hbeta n) k j).symm

/-- Because the actual OS boundary range is a linear submodule, Mathlib
Gram--Schmidt preserves physical boundary realizability once the finitely many
raw normal outputs are physically realizable. -/
theorem primaryPlaquetteNormalOutputGramSchmidt_mem_boundaryMoment_range_of_analysisImages_mem_positiveHalf_range
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 su2NormalPhysicalRangeRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (hAnalysisRange : ∀ i : Fin (k + 1),
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
          (halfExtent n) (beta n) (hbeta n) k i ∈
        (Q.positiveHalfL2LinearMap hInvariant n).range)
    (j : Fin (k + 1)) :
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
        (halfExtent n) (beta n) (hbeta n) k j ∈
      (Q.boundaryMomentLinearIsometry hInvariant n).toLinearMap.range := by
  apply (Submodule.span_le.2 ?_)
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt_mem_normalOutput_span_Iic
      (halfExtent n) (beta n) (hbeta n) k j)
  rintro y ⟨i, _hi, rfl⟩
  exact
    Q.primaryPlaquetteNormalOutput_mem_boundaryMoment_range_of_analysisImage_mem_positiveHalf_range
      hInvariant n k i (hAnalysisRange i)

/-- Existence form on the actual dense OS carrier.  No arbitrary synthesis
preimage is used: the witness is a genuine carrier state whose boundary moment
is the theorem-generated normal-output Gram--Schmidt vector. -/
theorem primaryPlaquetteNormalOutputGramSchmidt_exists_carrier_boundaryMoment_preimage
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 su2NormalPhysicalRangeRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (hAnalysisRange : ∀ i : Fin (k + 1),
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
          (halfExtent n) (beta n) (hbeta n) k i ∈
        (Q.positiveHalfL2LinearMap hInvariant n).range)
    (j : Fin (k + 1)) :
    ∃ F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2 su2NormalPhysicalRangeRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n).Carrier,
      Q.boundaryMomentLinearIsometry hInvariant n F =
        periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
          (halfExtent n) (beta n) (hbeta n) k j := by
  exact
    Q.primaryPlaquetteNormalOutputGramSchmidt_mem_boundaryMoment_range_of_analysisImages_mem_positiveHalf_range
      hInvariant n k hAnalysisRange j

/-- The same one-scale realization lies in the completed physical Hilbert
boundary range.  Completion adds no new compatibility condition. -/
theorem primaryPlaquetteNormalOutputGramSchmidt_exists_physicalHilbert_boundaryMoment_preimage
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 su2NormalPhysicalRangeRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (hAnalysisRange : ∀ i : Fin (k + 1),
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
          (halfExtent n) (beta n) (hbeta n) k i ∈
        (Q.positiveHalfL2LinearMap hInvariant n).range)
    (j : Fin (k + 1)) :
    ∃ psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2 su2NormalPhysicalRangeRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n).PhysicalHilbert,
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi =
        periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
          (halfExtent n) (beta n) (hbeta n) k j := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2 su2NormalPhysicalRangeRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  rcases
      Q.primaryPlaquetteNormalOutputGramSchmidt_exists_carrier_boundaryMoment_preimage
        hInvariant n k hAnalysisRange j with ⟨F, hF⟩
  refine ⟨Pn.physicalState F, ?_⟩
  calc
    Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n (Pn.physicalState F) =
        physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent 2 su2NormalPhysicalRangeRankPositive beta hbeta
          Q.toWeakStarBridge hInvariant n F := by
      simpa [Pn] using
        Q.physicalHilbertBoundaryMomentLinearIsometry_physicalState hInvariant n F
    _ = Q.boundaryMomentLinearIsometry hInvariant n F := by
      exact (Q.boundaryMomentLinearIsometry_apply hInvariant n F).symm
    _ = periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
          (halfExtent n) (beta n) (hbeta n) k j := hF

/-- One-scale compatibility package: determinant nondegeneracy gives the
orthonormality from #1639, while finite positive-half physical-range membership
places every resulting mode in the completed physical OS boundary range. -/
theorem primaryPlaquetteNormalOutputGramSchmidt_orthonormal_and_physicalHilbert_realizable
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 su2NormalPhysicalRangeRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (hdet :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
        (halfExtent n) (beta n) (hbeta n) k).det ≠ 0)
    (hAnalysisRange : ∀ i : Fin (k + 1),
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
          (halfExtent n) (beta n) (hbeta n) k i ∈
        (Q.positiveHalfL2LinearMap hInvariant n).range) :
    Orthonormal ℝ
        (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
          (halfExtent n) (beta n) (hbeta n) k) ∧
      ∀ j : Fin (k + 1),
        ∃ psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent 2 su2NormalPhysicalRangeRankPositive beta hbeta
          Q.toWeakStarBridge hInvariant n).PhysicalHilbert,
          Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi =
            periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
              (halfExtent n) (beta n) (hbeta n) k j := by
  constructor
  · exact
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt_orthonormal_of_analysisGram_det_ne_zero
        (halfExtent n) (beta n) (hbeta n) k hdet
  · intro j
    exact
      Q.primaryPlaquetteNormalOutputGramSchmidt_exists_physicalHilbert_boundaryMoment_preimage
        hInvariant n k hAnalysisRange j

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
