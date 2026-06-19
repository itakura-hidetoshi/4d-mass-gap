import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSPullback

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A Hilbert-space Gram factorization of the actual compact Wilson pullback
reflection form.

This formulation is not restricted to a finite feature set.  In the intended
`SU(N)` specialization, the feature Hilbert space can carry the countable
Peter--Weyl matrix-coefficient expansion of the plaquettes crossing the
reflection plane. -/
structure PhysicalYangMillsOrientedWilsonOSHilbertGramCertificate
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)) where
  FeatureHilbert : Type
  [featureNormedAddCommGroup : NormedAddCommGroup FeatureHilbert]
  [featureInnerProductSpace : InnerProductSpace ℝ FeatureHilbert]
  [featureCompleteSpace : CompleteSpace FeatureHilbert]
  moment : ℕ → D.positiveTimeSubalgebra → FeatureHilbert
  pullbackForm_eq_norm_sq :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      D.orientedWilsonPullbackForm G L n F = ‖moment n F‖ ^ 2

attribute [instance]
  PhysicalYangMillsOrientedWilsonOSHilbertGramCertificate.featureNormedAddCommGroup
  PhysicalYangMillsOrientedWilsonOSHilbertGramCertificate.featureInnerProductSpace
  PhysicalYangMillsOrientedWilsonOSHilbertGramCertificate.featureCompleteSpace

/-- A Hilbert Gram factorization proves nonnegativity of every compact Wilson
pullback reflection form. -/
theorem physical_yang_mills_oriented_hilbertGram_pullbackForm_nonneg
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (C : PhysicalYangMillsOrientedWilsonOSHilbertGramCertificate G L D)
    (n : ℕ)
    (F : D.positiveTimeSubalgebra) :
    0 ≤ D.orientedWilsonPullbackForm G L n F := by
  rw [C.pullbackForm_eq_norm_sq]
  exact sq_nonneg ‖C.moment n F‖

/-- Forget the explicit Hilbert Gram realization while retaining the generated
finite-volume compact Wilson reflection positivity. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSHilbertGramCertificate.toPullbackCertificate
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    (C : PhysicalYangMillsOrientedWilsonOSHilbertGramCertificate G L D) :
    PhysicalYangMillsOrientedWilsonOSPullbackCertificate G L D where
  finiteReflectionPositive n F :=
    physical_yang_mills_oriented_hilbertGram_pullbackForm_nonneg
      G L D C n F

/-- A Hilbert Gram certificate makes every physical approximating weak-star
state reflection positive. -/
theorem physical_yang_mills_oriented_hilbertGram_approximating_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (C : PhysicalYangMillsOrientedWilsonOSHilbertGramCertificate G L D)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState
        (G.toSymmetryLimit L) n) :=
  physical_yang_mills_oriented_pullback_approximating_reflectionPositive
    G L D C.toPullbackCertificate n

/-- A compact-group Hilbert Gram factorization, together with the actual
interpolation and Prokhorov weak limit, yields continuum OS reflection
positivity. -/
theorem physical_yang_mills_oriented_hilbertGram_continuum_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (C : PhysicalYangMillsOrientedWilsonOSHilbertGramCertificate G L D) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState
        (G.toSymmetryLimit L)) :=
  physical_yang_mills_oriented_pullback_continuum_reflectionPositive
    G L D C.toPullbackCertificate

end

end MathlibAnalytic
end MGAP4D
