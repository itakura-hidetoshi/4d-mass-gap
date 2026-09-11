import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PrimaryPlaquetteNormalOutputPhysicalRange
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryHaarProjectiveCylinderOrthonormal

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance su2NormalProjectiveReadoutTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2NormalProjectiveReadoutCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2NormalProjectiveReadoutSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2NormalProjectiveReadoutMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2NormalProjectiveReadoutBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2NormalProjectiveReadoutNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private theorem su2NormalProjectiveReadoutRankPositive : 0 < (2 : ℕ) := by
  norm_num

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 su2NormalProjectiveReadoutRankPositive beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}

/-- The selected finite OS/projective isometry factors literally through the
completed physical boundary-moment isometry followed by the generic
boundary-Haar/projective isometry.

This equality is the theorem-level API seam needed to reuse any boundary-Haar
family in the existing projective readout.  It changes no physical assumption:
it only exposes the composition already present in the definition of
`finiteOSMarginalLinearIsometry`. -/
theorem finiteOSMarginalLinearIsometry_eq_boundaryHaarProjectiveL2Isometry_physicalBoundaryMoment
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent 2 su2NormalProjectiveReadoutRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n) :
    R.finiteOSMarginalLinearIsometry hInvariant n psi =
      R.boundaryHaarProjectiveL2Isometry n
        (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi) := by
  rfl

/-- A physical-boundary realization of one #1639 normal-output Gram--Schmidt
mode therefore gives an exact realization of its density-corrected projective
marginal image by a genuine completed OS Hilbert state. -/
theorem primaryPlaquetteNormalOutputGramSchmidt_exists_physicalHilbert_projective_preimage
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (hAnalysisRange : ∀ i : Fin (k + 1),
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
          (halfExtent n) (beta n) (hbeta n) k i ∈
        (Q.positiveHalfL2LinearMap hInvariant n).range)
    (j : Fin (k + 1)) :
    ∃ psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent 2 su2NormalProjectiveReadoutRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n,
      R.finiteOSMarginalLinearIsometry hInvariant n psi =
        R.boundaryHaarProjectiveL2Isometry n
          (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
            (halfExtent n) (beta n) (hbeta n) k j) := by
  rcases
      Q.primaryPlaquetteNormalOutputGramSchmidt_exists_physicalHilbert_boundaryMoment_preimage
        hInvariant n k hAnalysisRange j with ⟨psi, hpsi⟩
  refine ⟨psi, ?_⟩
  rw [R.finiteOSMarginalLinearIsometry_eq_boundaryHaarProjectiveL2Isometry_physicalBoundaryMoment,
    hpsi]

/-- The nonzero finite actual Wilson analysis Gram determinant from #1638/#1639
makes the projective images of the theorem-generated normal-output
Gram--Schmidt family orthonormal at the same Wilson scale.

Only Mathlib isometry transport is used here; no projective naturality of the
Wilson analysis operator across different scales is assumed. -/
theorem primaryPlaquetteNormalOutputGramSchmidt_projective_orthonormal_of_analysisGram_det_ne_zero
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (n k : ℕ)
    (hdet :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
        (halfExtent n) (beta n) (hbeta n) k).det ≠ 0) :
    Orthonormal ℝ
      ((R.boundaryHaarProjectiveL2Isometry n) ∘
        periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
          (halfExtent n) (beta n) (hbeta n) k) := by
  exact R.boundaryHaarProjectiveL2Isometry_orthonormal n _
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt_orthonormal_of_analysisGram_det_ne_zero
      (halfExtent n) (beta n) (hbeta n) k hdet)

/-- Fixed-scale physical/projective package for the actual normal-output family.

Under exactly the two still-visible finite hypotheses

* nonzero actual analysis Gram determinant, and
* physical positive-half range membership of the finitely many `A g_i`,

there is a family of genuine completed OS Hilbert states whose selected
projective marginal images are the #1639 theorem-generated boundary-Haar modes,
and those physical projective images are orthonormal.

This closes the one-scale physical/projective compatibility layer.  It does
not identify scale-dependent modes across `n`, and therefore does not replace
the separate continuum/projective cylinder coherence obligation. -/
theorem primaryPlaquetteNormalOutputGramSchmidt_exists_physicalHilbert_projective_orthonormal_family
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
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
    ∃ psi : Fin (k + 1) →
        PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
          S D halfExtent 2 su2NormalProjectiveReadoutRankPositive beta hbeta
          Q.toWeakStarBridge hInvariant n,
      (∀ j : Fin (k + 1),
        R.finiteOSMarginalLinearIsometry hInvariant n (psi j) =
          R.boundaryHaarProjectiveL2Isometry n
            (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
              (halfExtent n) (beta n) (hbeta n) k j)) ∧
      Orthonormal ℝ
        (fun j : Fin (k + 1) =>
          R.finiteOSMarginalLinearIsometry hInvariant n (psi j)) := by
  have hexists : ∀ j : Fin (k + 1),
      ∃ psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
          S D halfExtent 2 su2NormalProjectiveReadoutRankPositive beta hbeta
          Q.toWeakStarBridge hInvariant n,
        R.finiteOSMarginalLinearIsometry hInvariant n psi =
          R.boundaryHaarProjectiveL2Isometry n
            (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
              (halfExtent n) (beta n) (hbeta n) k j) := by
    intro j
    exact
      R.primaryPlaquetteNormalOutputGramSchmidt_exists_physicalHilbert_projective_preimage
        hInvariant n k hAnalysisRange j
  choose psi hpsi using hexists
  refine ⟨psi, hpsi, ?_⟩
  have hfamily :
      (fun j : Fin (k + 1) =>
        R.finiteOSMarginalLinearIsometry hInvariant n (psi j)) =
      (R.boundaryHaarProjectiveL2Isometry n) ∘
        periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
          (halfExtent n) (beta n) (hbeta n) k := by
    funext j
    exact hpsi j
  rw [hfamily]
  exact
    R.primaryPlaquetteNormalOutputGramSchmidt_projective_orthonormal_of_analysisGram_det_ne_zero
      n k hdet

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

end

end MathlibAnalytic
end MGAP4D
