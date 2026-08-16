import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSPullback

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Pulling a physical gauge-invariant observable back through an equivariant
oriented Wilson interpolation produces a pointwise lattice-gauge-invariant
observable at every selected Prokhorov scale.

No new gauge-invariance or interpolation hypothesis is introduced here: the
proof is exactly the composition of the existing interpolation equivariance
with membership in the physical gauge-invariant observable subalgebra. -/
theorem physical_yang_mills_oriented_gaugeInvariantObservable_pullback_gaugeTransform
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra
      (G.toSymmetryLimit L))
    (g : G.Symmetry)
    (U : (E.system (L.subsequence n)).base.Configuration) :
    (O : BoundedContinuousFunction
        (G.toSymmetryLimit L).Configuration ℝ)
        (E.interpolate (L.subsequence n)
          ((E.system (L.subsequence n)).base.gaugeTransform
            (G.latticeGauge (L.subsequence n) g) U)) =
      (O : BoundedContinuousFunction
        (G.toSymmetryLimit L).Configuration ℝ)
        (E.interpolate (L.subsequence n) U) := by
  rw [G.interpolate_equivariant (L.subsequence n) g U]
  exact O.property g (E.interpolate (L.subsequence n) U)

/-- Functional form of lattice gauge invariance for the pullback of a physical
gauge-invariant observable.  This is convenient for rewriting raw integrands
before applying Haar/Gibbs measure transport. -/
theorem physical_yang_mills_oriented_gaugeInvariantObservable_pullback_comp_gaugeTransform
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra
      (G.toSymmetryLimit L))
    (g : G.Symmetry) :
    (fun U : (E.system (L.subsequence n)).base.Configuration =>
      (O : BoundedContinuousFunction
        (G.toSymmetryLimit L).Configuration ℝ)
        (E.interpolate (L.subsequence n)
          ((E.system (L.subsequence n)).base.gaugeTransform
            (G.latticeGauge (L.subsequence n) g) U))) =
      fun U : (E.system (L.subsequence n)).base.Configuration =>
        (O : BoundedContinuousFunction
          (G.toSymmetryLimit L).Configuration ℝ)
          (E.interpolate (L.subsequence n) U) := by
  funext U
  exact physical_yang_mills_oriented_gaugeInvariantObservable_pullback_gaugeTransform
    G L n O g U

/-- The raw compact-Wilson integrand defining the OS pullback quadratic form is
itself pointwise invariant under the lattice gauge transformation induced by a
physical symmetry.

This specializes the generic pullback theorem to `Theta(F) * F`; consequently
no separate gauge-invariance field is required for the OS quadratic integrand. -/
theorem PhysicalYangMillsGaugeInvariantOSReflectionData.orientedWilsonPullbackIntegrand_gaugeInvariant
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (n : ℕ)
    (F : D.positiveTimeSubalgebra)
    (g : G.Symmetry)
    (U : (E.system (L.subsequence n)).base.Configuration) :
    ((D.quadraticObservable F :
        physicalYangMillsGaugeInvariantObservableSubalgebra
          (G.toSymmetryLimit L)) :
      BoundedContinuousFunction (G.toSymmetryLimit L).Configuration ℝ)
        (E.interpolate (L.subsequence n)
          ((E.system (L.subsequence n)).base.gaugeTransform
            (G.latticeGauge (L.subsequence n) g) U)) =
      ((D.quadraticObservable F :
          physicalYangMillsGaugeInvariantObservableSubalgebra
            (G.toSymmetryLimit L)) :
        BoundedContinuousFunction (G.toSymmetryLimit L).Configuration ℝ)
          (E.interpolate (L.subsequence n) U) :=
  physical_yang_mills_oriented_gaugeInvariantObservable_pullback_gaugeTransform
    G L n (D.quadraticObservable F) g U

end

end MathlibAnalytic
end MGAP4D
