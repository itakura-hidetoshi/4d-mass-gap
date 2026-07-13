import MGAP4D.MathlibAnalytic.WightmanOSPVMCoordinateGraphFromObservableNormContinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Function Set Filter Topology MeasureTheory

noncomputable section

namespace EuclideanYangMillsOSPhysicalTimeTranslation

/-- The reflected Euclidean quadratic integrand of the translated-observable
increment.  Its integral is exactly the square of the OS observable norm of the
increment. -/
def osObservableDifferenceProduct
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (F : M.observables.PositiveTimeObservable)
    (t : ℝ)
    (ω : S.measurePackage.configurationSpace) : ℝ :=
  M.observables.realization (T.observableTranslate t F - F)
      (M.observables.timeReflection ω) *
    M.observables.realization (T.observableTranslate t F - F) ω

/-- The Euclidean integral of the reflected difference product is the exact
square of the OS observable norm. -/
theorem integral_osObservableDifferenceProduct_eq_norm_sq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (F : M.observables.PositiveTimeObservable)
    (t : ℝ) :
    (∫ ω, T.osObservableDifferenceProduct F t ω
      ∂S.measurePackage.euclideanMeasure) =
      ‖T.observableTranslate t F - F‖ ^ 2 := by
  unfold osObservableDifferenceProduct
  rw [← M.observables.osInner_eq_integral
    (T.observableTranslate t F - F)
    (T.observableTranslate t F - F)]
  exact real_inner_self_eq_norm_sq _

/-- Euclidean dominated-convergence input for every translated observable
increment.  All hypotheses are stated on the actual reflected realization
integrand and the actual continuum Euclidean measure. -/
structure ObservableDifferenceDominatedConvergence
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) where
  bound :
    M.observables.PositiveTimeObservable →
      S.measurePackage.configurationSpace → ℝ
  bound_integrable :
    ∀ F, Integrable (bound F) S.measurePackage.euclideanMeasure
  product_aestronglyMeasurable :
    ∀ F,
      ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ici 0),
        AEStronglyMeasurable
          (fun ω => T.osObservableDifferenceProduct F t ω)
          S.measurePackage.euclideanMeasure
  product_norm_le :
    ∀ F,
      ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ici 0),
        ∀ᵐ ω ∂S.measurePackage.euclideanMeasure,
          ‖T.osObservableDifferenceProduct F t ω‖ ≤ bound F ω
  product_tendsto_zero :
    ∀ F,
      ∀ᵐ ω ∂S.measurePackage.euclideanMeasure,
        Tendsto
          (fun t : ℝ => T.osObservableDifferenceProduct F t ω)
          (nhdsWithin 0 (Set.Ici 0))
          (nhds 0)

namespace ObservableDifferenceDominatedConvergence

/-- Mathlib's filter-form dominated convergence theorem sends the reflected
Euclidean difference products to zero in integral. -/
theorem integral_tendsto_zero
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (D : T.ObservableDifferenceDominatedConvergence)
    (F : M.observables.PositiveTimeObservable) :
    Tendsto
      (fun t : ℝ =>
        ∫ ω, T.osObservableDifferenceProduct F t ω
          ∂S.measurePackage.euclideanMeasure)
      (nhdsWithin 0 (Set.Ici 0))
      (nhds 0) := by
  have h :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (F := fun t ω => T.osObservableDifferenceProduct F t ω)
      (f := fun _ => (0 : ℝ))
      (D.bound F)
      (D.product_aestronglyMeasurable F)
      (D.product_norm_le F)
      (D.bound_integrable F)
      (D.product_tendsto_zero F)
  simpa using h

/-- Dominated convergence of the actual Euclidean reflected products implies
right continuity in the OS observable norm. -/
theorem observableTranslate_tendsto_zero
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (D : T.ObservableDifferenceDominatedConvergence)
    (F : M.observables.PositiveTimeObservable) :
    Tendsto
      (fun t : ℝ => T.observableTranslate t F)
      (nhdsWithin 0 (Set.Ici 0))
      (nhds F) := by
  have hIntegral := D.integral_tendsto_zero F
  have hSquare :
      Tendsto
        (fun t : ℝ => ‖T.observableTranslate t F - F‖ ^ 2)
        (nhdsWithin 0 (Set.Ici 0))
        (nhds 0) := by
    exact hIntegral.congr'
      (Eventually.of_forall fun t =>
        T.integral_osObservableDifferenceProduct_eq_norm_sq F t)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  rw [Metric.tendsto_nhds] at hSquare
  have hEventually := hSquare (ε ^ 2) hεsq
  filter_upwards [hEventually] with t ht
  have hsqLt : ‖T.observableTranslate t F - F‖ ^ 2 < ε ^ 2 := by
    simpa [Real.dist_eq, abs_of_nonneg (sq_nonneg _)] using ht
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (T.observableTranslate t F - F)]

/-- The dominated Euclidean realization package supplies the observable-norm
strong continuity input used by the OS Hilbert reconstruction. -/
noncomputable def toStrongContinuityOnObservableNorm
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (D : T.ObservableDifferenceDominatedConvergence) :
    T.StrongContinuityOnObservableNorm where
  tendsto_zero_on_observable := D.observableTranslate_tendsto_zero

end ObservableDifferenceDominatedConvergence

/-- The pure-PVM gap route now consumes Euclidean dominated-convergence data on
the reflected realization integrands.  Observable-norm continuity, represented
state continuity, and full-Hilbert strong continuity are all theorem-generated. -/
noncomputable def toCanonicalPVMCoordinateGraphOfLaplaceExchangeGapDominatedContinuityAndDerivative
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M.toExplicitModel)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M.toExplicitModel)
    {m : ℝ} (hGap : M.toExplicitModel.HasMassGap m)
    (L : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      M.toExplicitModel A.toScalarSpectralRealization T.toEuclideanTimeSemigroup)
    (D : T.ObservableDifferenceDominatedConvergence)
    (hDerivative : T.RightDerivativeOnHamiltonianDomain)
    (hExchange : T.ReflectionTimeTranslationExchange) :
    ExplicitWightmanOSCanonicalRestrictedPVMCoordinateGraph M.toExplicitModel :=
  T.toCanonicalPVMCoordinateGraphOfLaplaceExchangeGapObservableNormContinuityAndDerivative
    A B hGap L D.toStrongContinuityOnObservableNorm hDerivative hExchange

end EuclideanYangMillsOSPhysicalTimeTranslation

end

end MathlibAnalytic
end MGAP4D
