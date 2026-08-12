import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeNormalizedTraceHilbertPowerPullback
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelPartialLimit

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct InnerProductSpace

noncomputable section

/-- The four actual shared-boundary `SU(2)` edge values of the canonical
primary spatial plaquette, kept in the same `Fin 4` slots as the four-edge
Hilbert contraction. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord
    (H : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  fun k => b (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k)

/-- Pull the degree-`n` genuine four-edge Hilbert feature back to the four
actual shared-boundary edge coordinates. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature
    (H n : ℕ) :
    RealHilbertKernelFeature
      ((periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (fun b c =>
        specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H c) ^ n) :=
  (specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n).comap
    (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H)

/-- Rectangular boundary/open-half pairing of the degree-`n` four-edge Hilbert
feature.  This is the exact Hilbert realization of the product kernel that
appears after boundary fiberization of the four temporal companions. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryOpenHalfFourEdgeDegreeFeature_inner
    (H n : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    inner ℝ
        ((periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature
          H n).feature b)
        ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeDegreeFeature
          H n).feature x) =
      specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x) ^ n := by
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeDegreeFeature] using
    ((specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n).kernel_eq_inner
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x)).symm

/-- The normalized trace of the `k`-th actual temporal companion in boundary
fibered coordinates.  The negative-half coordinate is retained here only so
that this is literally the plaquette trace occurring in the Wilson action. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace
    (H : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (k : Fin 4) : ℝ :=
  normalizedSpecialUnitaryRealTrace 2
    (periodicHypercubicPlaquetteHolonomy
      ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))

/-- Each actual temporal-companion trace is exactly the normalized relative
trace kernel between its physical boundary edge and its three-edge open-half
path. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace_eq_relativeKernel
    {H : ℕ}
    (hH : 0 < H)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (k : Fin 4) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace
        H b x y k =
      specialUnitaryNormalizedTraceRelativeKernel 2
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b k)
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x k) := by
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace,
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord] using
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_normalizedTrace_boundaryFibered_eq_relativeKernel
      hH b x y k)

/-- Degree-`n` scalar Taylor term of one selected temporal-companion trace
exponential, before the common `exp (-beta)` Wilson-energy constant. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionTaylorDegreeTerm
    (H : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (k : Fin 4) : ℝ :=
  (beta *
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace
        H b x y k) ^ n /
    (Nat.factorial n : ℝ)

/-- The actual degree-`n` temporal-companion Taylor term is the corresponding
normalized relative-kernel monomial with the exact Mathlib coefficient
`beta^n / n!`. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionTaylorDegreeTerm_eq_relativeKernel
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (n : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (k : Fin 4) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionTaylorDegreeTerm
        H beta n b x y k =
      (beta *
        specialUnitaryNormalizedTraceRelativeKernel 2
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b k)
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x k)) ^ n /
        (Nat.factorial n : ℝ) := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionTaylorDegreeTerm
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace_eq_relativeKernel
    hH b x y k]

/-- Product of the equal-degree Taylor terms of the four selected temporal
companions, in the validated cyclic pair order `(2,3)|(0,1)`.  This is the
diagonal sector of the full four-factor multi-index Taylor expansion. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionDiagonalTaylorDegreeTerm
    (H : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) : ℝ :=
  (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionTaylorDegreeTerm
      H beta n b x y 2 *
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionTaylorDegreeTerm
      H beta n b x y 3) *
  (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionTaylorDegreeTerm
      H beta n b x y 0 *
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionTaylorDegreeTerm
      H beta n b x y 1)

private theorem cyclicFourEdgeDiagonalTaylorScalarFactorization
    (beta a₂ a₃ a₀ a₁ : ℝ)
    (n : ℕ) :
    ((((beta * a₂) ^ n / (Nat.factorial n : ℝ)) *
        ((beta * a₃) ^ n / (Nat.factorial n : ℝ))) *
      (((beta * a₀) ^ n / (Nat.factorial n : ℝ)) *
        ((beta * a₁) ^ n / (Nat.factorial n : ℝ)))) =
      (beta ^ n / (Nat.factorial n : ℝ)) ^ 4 *
        (((a₂ * a₃) * (a₀ * a₁)) ^ n) := by
  ring

/-- The four-companion diagonal Taylor sector is exactly the scalar Taylor
coefficient times the degree-`n` genuine four-edge kernel.  In particular, no
cyclic-composite relative kernel is substituted for the product of four edge
kernels. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionDiagonalTaylorDegreeTerm_eq_edgewiseKernel
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (n : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionDiagonalTaylorDegreeTerm
        H beta n b x y =
      (beta ^ n / (Nat.factorial n : ℝ)) ^ 4 *
        specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x) ^ n := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionDiagonalTaylorDegreeTerm
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionTaylorDegreeTerm_eq_relativeKernel
      hH beta n b x y 2,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionTaylorDegreeTerm_eq_relativeKernel
      hH beta n b x y 3,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionTaylorDegreeTerm_eq_relativeKernel
      hH beta n b x y 0,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionTaylorDegreeTerm_eq_relativeKernel
      hH beta n b x y 1]
  simpa [specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel] using
    (cyclicFourEdgeDiagonalTaylorScalarFactorization
      beta
      (specialUnitaryNormalizedTraceRelativeKernel 2
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 2)
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x 2))
      (specialUnitaryNormalizedTraceRelativeKernel 2
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 3)
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x 3))
      (specialUnitaryNormalizedTraceRelativeKernel 2
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 0)
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x 0))
      (specialUnitaryNormalizedTraceRelativeKernel 2
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 1)
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x 1))
      n)

/-- Hilbert form of the preceding identity.  This is the exact bridge from the
four selected actual Wilson Taylor terms to the arbitrary-degree four-edge
Hilbert feature constructed in this package. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionDiagonalTaylorDegreeTerm_eq_featureInner
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (n : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionDiagonalTaylorDegreeTerm
        H beta n b x y =
      (beta ^ n / (Nat.factorial n : ℝ)) ^ 4 *
        inner ℝ
          ((periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature
            H n).feature b)
          ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeDegreeFeature
            H n).feature x) := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionDiagonalTaylorDegreeTerm_eq_edgewiseKernel
    hH beta n b x y]
  rw [← periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryOpenHalfFourEdgeDegreeFeature_inner]

/-- The exact finite scalar exponential kernel on each boundary/open-half
companion pair is the ordinary Mathlib Taylor sum. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionExponentialPartialKernel_eq_sum
    (H degree : ℕ)
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (k : Fin 4) :
    RealHilbertKernelFeature.exponentialPartialKernel
        (specialUnitaryNormalizedTraceRelativeKernel 2) beta degree
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b k)
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x k) =
      ∑ m ∈ Finset.range (degree + 1),
        (beta *
          specialUnitaryNormalizedTraceRelativeKernel 2
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b k)
            (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x k)) ^ m /
          (Nat.factorial m : ℝ) := by
  exact RealHilbertKernelFeature.exponentialPartialKernel_eq_sum
    (specialUnitaryNormalizedTraceRelativeKernel 2) beta degree
    (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b k)
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x k)

/-- The same finite Taylor sum written literally in terms of the normalized
trace of the actual temporal-companion plaquette in the Wilson action. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionExponentialPartialKernel_eq_sum_actualTrace
    {H : ℕ}
    (hH : 0 < H)
    (degree : ℕ)
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (k : Fin 4) :
    RealHilbertKernelFeature.exponentialPartialKernel
        (specialUnitaryNormalizedTraceRelativeKernel 2) beta degree
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b k)
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x k) =
      ∑ m ∈ Finset.range (degree + 1),
        (beta *
          periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace
            H b x y k) ^ m /
          (Nat.factorial m : ℝ) := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionExponentialPartialKernel_eq_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace_eq_relativeKernel
    hH b x y k]

/-- Each selected actual temporal-companion Wilson Boltzmann factor has the
exact constant-times-relative-kernel exponential form used by the Taylor
feature construction. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionWilsonBoltzmannCentralFunction_eq_relativeKernelExp
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (k : Fin 4) :
    specialUnitaryWilsonBoltzmannCentralFunction 2 beta
        (periodicHypercubicPlaquetteHolonomy
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)) =
      Real.exp (-beta) *
        Real.exp
          (beta *
            specialUnitaryNormalizedTraceRelativeKernel 2
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b k)
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x k)) := by
  rw [specialUnitaryWilsonBoltzmannCentralFunction_eq_trace]
  rw [← periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace_eq_relativeKernel
    hH b x y k]
  rfl

end

end MathlibAnalytic
end MGAP4D
