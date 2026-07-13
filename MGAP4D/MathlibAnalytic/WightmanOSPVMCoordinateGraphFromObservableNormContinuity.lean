import MGAP4D.MathlibAnalytic.WightmanOSPVMCoordinateGraphFromObservableStrongContinuity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Function Set Filter Topology

noncomputable section

namespace EuclideanYangMillsOSPositiveTimeObservableConstruction

/-- The canonical OS represented-state map preserves distance exactly.  This is
proved from the reflected Euclidean inner-product identity and therefore avoids
exposing or transporting any of the intentionally opaque completion instances. -/
theorem dist_physicalState_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S)
    (F G : P.PositiveTimeObservable) :
    dist (P.physicalState F) (P.physicalState G) = dist F G := by
  rw [dist_eq_norm, dist_eq_norm]
  have hsq :
      ‖P.physicalState F - P.physicalState G‖ ^ 2 = ‖F - G‖ ^ 2 := by
    calc
      ‖P.physicalState F - P.physicalState G‖ ^ 2 =
          inner ℝ (P.physicalState F - P.physicalState G)
            (P.physicalState F - P.physicalState G) := by
        symm
        exact real_inner_self_eq_norm_sq _
      _ = inner ℝ (F - G) (F - G) := by
        simp only [inner_sub_left, inner_sub_right,
          P.inner_physicalState_physicalState]
      _ = ‖F - G‖ ^ 2 := real_inner_self_eq_norm_sq _
  nlinarith [norm_nonneg (P.physicalState F - P.physicalState G),
    norm_nonneg (F - G)]

/-- The actual map from Euclidean positive-time observables to their completed
OS physical states is a Mathlib isometry. -/
theorem physicalState_isometry
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) :
    Isometry P.physicalState := by
  intro F G
  exact P.dist_physicalState_eq F G

end EuclideanYangMillsOSPositiveTimeObservableConstruction

namespace EuclideanYangMillsOSPhysicalTimeTranslation

/-- Minimal continuity input on the actual Euclidean observable carrier: each
positive-time observable converges to itself in the OS observable norm as the
translation time tends to zero from the right. -/
structure StrongContinuityOnObservableNorm
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) : Prop where
  tendsto_zero_on_observable :
    ∀ F : M.observables.PositiveTimeObservable,
      Tendsto
        (fun t : ℝ => T.observableTranslate t F)
        (nhdsWithin 0 (Set.Ici 0))
        (nhds F)

namespace StrongContinuityOnObservableNorm

/-- Observable-norm continuity passes through the canonical OS state isometry,
yielding continuity on represented physical states. -/
noncomputable def toStrongContinuityOnObservableStates
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (hT : T.StrongContinuityOnObservableNorm) :
    T.StrongContinuityOnObservableStates where
  tendsto_zero_on_physicalState := by
    intro F
    have hState :
        Tendsto
          (fun t : ℝ =>
            M.observables.physicalState (T.observableTranslate t F))
          (nhdsWithin 0 (Set.Ici 0))
          (nhds (M.observables.physicalState F)) :=
      M.observables.physicalState_isometry.continuous.tendsto F
        |>.comp (hT.tendsto_zero_on_observable F)
    have hEventually :
        (fun t : ℝ => T.operator t (M.observables.physicalState F)) =ᶠ[
          nhdsWithin 0 (Set.Ici 0)]
        (fun t : ℝ =>
          M.observables.physicalState (T.observableTranslate t F)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact T.operator_on_dense_state t F (by simpa using ht)
    exact hState.congr' hEventually.symm

end StrongContinuityOnObservableNorm

/-- The pure-PVM gap route now consumes observable-norm continuity directly;
continuity on represented physical states and on the full Hilbert completion are
both theorem-generated. -/
noncomputable def toCanonicalPVMCoordinateGraphOfLaplaceExchangeGapObservableNormContinuityAndDerivative
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M.toExplicitModel)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M.toExplicitModel)
    {m : ℝ} (hGap : M.toExplicitModel.HasMassGap m)
    (L : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      M.toExplicitModel A.toScalarSpectralRealization T.toEuclideanTimeSemigroup)
    (hContinuous : T.StrongContinuityOnObservableNorm)
    (hDerivative : T.RightDerivativeOnHamiltonianDomain)
    (hExchange : T.ReflectionTimeTranslationExchange) :
    ExplicitWightmanOSCanonicalRestrictedPVMCoordinateGraph M.toExplicitModel :=
  T.toCanonicalPVMCoordinateGraphOfLaplaceExchangeGapObservableContinuityAndDerivative
    A B hGap L hContinuous.toStrongContinuityOnObservableStates hDerivative
    hExchange

end EuclideanYangMillsOSPhysicalTimeTranslation

end

end MathlibAnalytic
end MGAP4D
