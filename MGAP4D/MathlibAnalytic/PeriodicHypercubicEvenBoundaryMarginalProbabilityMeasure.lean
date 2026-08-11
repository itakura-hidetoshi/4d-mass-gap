import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalEffectiveDensity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundedContinuousTransport
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance boundaryMarginalProbabilityNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryMarginalProbabilityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryMarginalProbabilityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryMarginalProbabilitySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryMarginalProbabilityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryMarginalProbabilityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The actual finite Wilson boundary marginal measure: boundary Haar tilted by
exactly the effective density obtained after integrating out both open halves. -/
noncomputable def periodicHypercubicEvenBoundaryMarginalMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measure (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :=
  (periodicHypercubicEvenBoundaryHaarMeasure H N).withDensity
    (periodicHypercubicEvenBoundaryMarginalEffectiveDensity
      H N hN beta hbeta)

/-- The real density of the actual boundary marginal is integrable.  The proof
uses the already-established integrability of the constant reflected observable
and Fubini, rather than introducing a separate boundedness estimate. -/
theorem periodicHypercubicEvenBoundaryMarginalEffectiveDensity_toReal_integrable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Integrable
      (fun b =>
        (periodicHypercubicEvenBoundaryMarginalEffectiveDensity
          H N hN beta hbeta b).toReal)
      (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  let one : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ := 1
  let T :=
    periodicHypercubicEvenWilsonGibbsReflectionTransportData_of_boundedContinuous
      H N hN beta hbeta one
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H N
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let density := periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
    H N hN beta hbeta
  have hKernel :
      Integrable
        (fun z => (density z).toReal)
        (boundaryMeasure.prod (halfMeasure.prod halfMeasure)) := by
    simpa [T, one, boundaryMeasure, halfMeasure, density,
      periodicHypercubicEvenBoundaryWeightedReflectedObservable,
      periodicHypercubicEvenBoundaryReflectedObservable] using T.kernelIntegrable
  have hOuter :
      Integrable
        (fun b => ∫ z, (density (b, z)).toReal ∂(halfMeasure.prod halfMeasure))
        boundaryMeasure :=
    hKernel.integral_prod_right
  apply hOuter.congr
  filter_upwards [] with b
  have hFiber :
      Integrable
        (fun z => (density (b, z)).toReal)
        (halfMeasure.prod halfMeasure) := by
    have h := T.fiberKernelIntegrable b
    simpa [T, one, halfMeasure, density,
      periodicHypercubicEvenBoundaryWeightedReflectedObservable,
      periodicHypercubicEvenBoundaryReflectedObservable] using h
  have hProd :
      (∫ z, (density (b, z)).toReal ∂(halfMeasure.prod halfMeasure)) =
        ∫ x, ∫ y, (density (b, (x, y))).toReal ∂halfMeasure ∂halfMeasure :=
    MeasureTheory.integral_prod _ hFiber
  calc
    (∫ z, (density (b, z)).toReal ∂(halfMeasure.prod halfMeasure)) =
        ∫ x, ∫ y, (density (b, (x, y))).toReal ∂halfMeasure ∂halfMeasure := hProd
    _ = (periodicHypercubicEvenBoundaryMarginalEffectiveDensity
          H N hN beta hbeta b).toReal := by
      symm
      simpa [density, halfMeasure] using
        periodicHypercubicEvenBoundaryMarginalEffectiveDensity_toReal_eq_openHalf_integrals
          H N hN beta hbeta b

/-- Exact normalization of the real effective density.  This is the constant
observable `1` case of the already-proved reflection transport theorem: the
left side is the integral of `1` against the finite Wilson Gibbs probability
measure, while the right side is the boundary marginal density. -/
theorem periodicHypercubicEvenBoundaryMarginalEffectiveDensity_integral_eq_one
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∫ b,
      (periodicHypercubicEvenBoundaryMarginalEffectiveDensity
        H N hN beta hbeta b).toReal
      ∂(periodicHypercubicEvenBoundaryHaarMeasure H N)) = 1 := by
  let one : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ := 1
  let T :=
    periodicHypercubicEvenWilsonGibbsReflectionTransportData_of_boundedContinuous
      H N hN beta hbeta one
  have hTransport :=
    periodicHypercubicEvenWilsonGibbs_reflectedObservable_integral_eq_boundaryIntegral
      H N hN beta hbeta one T
  have hTriple :
      (1 : ℝ) =
        ∫ b, ∫ x, ∫ y,
          (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
            H N hN beta hbeta (b, (x, y))).toReal
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
          ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) := by
    simpa [one, periodicHypercubicEvenFullReflectedObservable,
      periodicHypercubicEvenBoundaryWeightedReflectedObservable,
      periodicHypercubicEvenBoundaryReflectedObservable] using hTransport
  calc
    (∫ b,
      (periodicHypercubicEvenBoundaryMarginalEffectiveDensity
        H N hN beta hbeta b).toReal
      ∂(periodicHypercubicEvenBoundaryHaarMeasure H N)) =
        ∫ b, ∫ x, ∫ y,
          (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
            H N hN beta hbeta (b, (x, y))).toReal
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
          ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun b =>
        periodicHypercubicEvenBoundaryMarginalEffectiveDensity_toReal_eq_openHalf_integrals
          H N hN beta hbeta b
    _ = 1 := hTriple.symm

/-- The ENNReal effective density has total mass exactly one. -/
theorem periodicHypercubicEvenBoundaryMarginalEffectiveDensity_lintegral_eq_one
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∫⁻ b,
      periodicHypercubicEvenBoundaryMarginalEffectiveDensity
        H N hN beta hbeta b
      ∂(periodicHypercubicEvenBoundaryHaarMeasure H N)) = 1 := by
  have hInt :=
    periodicHypercubicEvenBoundaryMarginalEffectiveDensity_toReal_integrable
      H N hN beta hbeta
  have hNonneg :
      ∀ᵐ b ∂(periodicHypercubicEvenBoundaryHaarMeasure H N),
        0 ≤ (periodicHypercubicEvenBoundaryMarginalEffectiveDensity
          H N hN beta hbeta b).toReal :=
    Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  have hBridge := ofReal_integral_eq_lintegral_ofReal hInt hNonneg
  rw [periodicHypercubicEvenBoundaryMarginalEffectiveDensity_integral_eq_one]
    at hBridge
  simpa only [ENNReal.ofReal_one] using hBridge.trans (by
    apply lintegral_congr
    intro b
    exact ENNReal.ofReal_toReal (by
      unfold periodicHypercubicEvenBoundaryMarginalEffectiveDensity
      exact ENNReal.ofReal_ne_top))

/-- The actual finite Wilson boundary marginal is a probability measure. -/
theorem periodicHypercubicEvenBoundaryMarginalMeasure_isProbabilityMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenBoundaryMarginalMeasure H N hN beta hbeta) := by
  constructor
  unfold periodicHypercubicEvenBoundaryMarginalMeasure
  rw [Measure.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact periodicHypercubicEvenBoundaryMarginalEffectiveDensity_lintegral_eq_one
    H N hN beta hbeta

local instance periodicHypercubicEvenBoundaryMarginalMeasureProbability
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenBoundaryMarginalMeasure H N hN beta hbeta) :=
  periodicHypercubicEvenBoundaryMarginalMeasure_isProbabilityMeasure
    H N hN beta hbeta

/-- In particular, the actual boundary marginal supplies the finite-measure
instance required by the generic positive-density power-Gram machinery. -/
theorem periodicHypercubicEvenBoundaryMarginalMeasure_isFiniteMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsFiniteMeasure
      (periodicHypercubicEvenBoundaryMarginalMeasure H N hN beta hbeta) := by
  infer_instance

end

end MathlibAnalytic
end MGAP4D