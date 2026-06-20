import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSHalfLatticePeterWeyl
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureProduct

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Scale-dependent local crossing-kernel data.

The number and type of crossing plaquettes may vary with the lattice scale.
Each local kernel has its own Hilbert feature realization, while the global
crossing kernel is their finite ordered product.  The global feature Hilbert
space is therefore allowed to vary with `n`; it is generated automatically by
completed tensor products. -/
structure PhysicalYangMillsOrientedWilsonOSLocalKernelProductCertificate
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D) where
  LocalLabel : ℕ → Type
  crossingLabels : ∀ n, List (LocalLabel n)
  localKernel :
    ∀ n, LocalLabel n →
      H.HalfConfiguration → H.HalfConfiguration → ℝ
  localFeature :
    ∀ n i, RealHilbertKernelFeature H.HalfConfiguration (localKernel n i)
  crossingKernel_eq_localProduct :
    ∀ (n : ℕ) (x y : H.HalfConfiguration),
      H.crossingKernel n x y =
        ((crossingLabels n).map fun i => localKernel n i x y).prod
  weightedGlobalFeature_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      Integrable
        (fun x => H.amplitude n F x •
          (RealHilbertKernelFeature.listProd
            (crossingLabels n) (localKernel n) (localFeature n)).feature x)
        H.halfMeasure

/-- The completed tensor-product feature for all crossing plaquettes at one
lattice scale. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSLocalKernelProductCertificate.globalFeature
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    {H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D}
    (C : PhysicalYangMillsOrientedWilsonOSLocalKernelProductCertificate H)
    (n : ℕ) :
    RealHilbertKernelFeature H.HalfConfiguration
      (fun x y =>
        ((C.crossingLabels n).map fun i => C.localKernel n i x y).prod) :=
  RealHilbertKernelFeature.listProd
    (C.crossingLabels n) (C.localKernel n) (C.localFeature n)

/-- The full crossing kernel is the inner product of the generated global
completed tensor-product features. -/
theorem physical_yang_mills_oriented_localKernelProduct_crossingKernel_eq_inner
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    {H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D}
    (C : PhysicalYangMillsOrientedWilsonOSLocalKernelProductCertificate H)
    (n : ℕ)
    (x y : H.HalfConfiguration) :
    H.crossingKernel n x y =
      inner ℝ ((C.globalFeature n).feature x)
        ((C.globalFeature n).feature y) := by
  rw [C.crossingKernel_eq_localProduct]
  exact (C.globalFeature n).kernel_eq_inner x y

/-- Local Hilbert features for every crossing plaquette imply nonnegativity of
the actual compact Wilson pullback form at each lattice scale. -/
theorem physical_yang_mills_oriented_localKernelProduct_pullbackForm_nonneg
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    (C : PhysicalYangMillsOrientedWilsonOSLocalKernelProductCertificate H)
    (n : ℕ)
    (F : D.positiveTimeSubalgebra) :
    0 ≤ D.orientedWilsonPullbackForm G L n F := by
  let P := C.globalFeature n
  let g : H.HalfConfiguration → P.FeatureHilbert :=
    fun x => H.amplitude n F x • P.feature x
  have hg : Integrable g H.halfMeasure :=
    C.weightedGlobalFeature_integrable n F
  calc
    0 ≤ ‖∫ x, g x ∂H.halfMeasure‖ ^ 2 := sq_nonneg _
    _ = ∫ x, ∫ y, inner ℝ (g x) (g y)
          ∂H.halfMeasure ∂H.halfMeasure :=
      (iterated_integral_real_inner_eq_norm_integral_sq
        H.halfMeasure g hg).symm
    _ = ∫ x, ∫ y,
          H.amplitude n F x * H.crossingKernel n x y *
            H.amplitude n F y
          ∂H.halfMeasure ∂H.halfMeasure := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with y
      rw [physical_yang_mills_oriented_localKernelProduct_crossingKernel_eq_inner
        C n x y]
      simp only [g, real_inner_smul_left, real_inner_smul_right]
      ring
    _ = D.orientedWilsonPullbackForm G L n F :=
      (H.pullbackForm_eq_kernelQuadratic n F).symm

/-- Forget the explicit local decomposition while retaining the generated
finite-volume compact Wilson reflection positivity. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSLocalKernelProductCertificate.toPullbackCertificate
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    {H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D}
    (C : PhysicalYangMillsOrientedWilsonOSLocalKernelProductCertificate H) :
    PhysicalYangMillsOrientedWilsonOSPullbackCertificate G L D where
  finiteReflectionPositive n F :=
    physical_yang_mills_oriented_localKernelProduct_pullbackForm_nonneg
      G L D H C n F

/-- Local crossing-plaquette kernel features make every physical approximating
weak-star state reflection positive. -/
theorem physical_yang_mills_oriented_localKernelProduct_approximating_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    (C : PhysicalYangMillsOrientedWilsonOSLocalKernelProductCertificate H)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState
        (G.toSymmetryLimit L) n) :=
  physical_yang_mills_oriented_pullback_approximating_reflectionPositive
    G L D C.toPullbackCertificate n

/-- A local Peter--Weyl feature theorem for every crossing plaquette, together
with the exact half-lattice decomposition, yields continuum
Osterwalder--Schrader reflection positivity. -/
theorem physical_yang_mills_oriented_localKernelProduct_continuum_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    (C : PhysicalYangMillsOrientedWilsonOSLocalKernelProductCertificate H) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState
        (G.toSymmetryLimit L)) :=
  physical_yang_mills_oriented_pullback_continuum_reflectionPositive
    G L D C.toPullbackCertificate

end

end MathlibAnalytic
end MGAP4D
