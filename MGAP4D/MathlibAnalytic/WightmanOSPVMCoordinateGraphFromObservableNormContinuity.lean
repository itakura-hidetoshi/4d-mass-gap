import MGAP4D.MathlibAnalytic.WightmanOSPVMCoordinateGraphFromObservableStrongContinuity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Function Set Filter Topology

noncomputable section

namespace EuclideanYangMillsOSPositiveTimeObservableConstruction

/-- The Osterwalder--Schrader separation quotient map, bundled as a real-linear
map on the actual positive-time observable carrier. -/
def osClassLinearMap
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) :
    P.PositiveTimeObservable →ₗ[ℝ] P.OSSeparatedPreHilbert where
  toFun := P.osClass
  map_add' := by
    intro F G
    exact SeparationQuotient.mk_add F G
  map_smul' := by
    intro r F
    exact SeparationQuotient.mk_smul r F

@[simp] theorem osClassLinearMap_apply
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S)
    (F : P.PositiveTimeObservable) :
    P.osClassLinearMap F = P.osClass F :=
  rfl

/-- The represented physical-state map, bundled as the composition of the OS
separation quotient with Mathlib's canonical completion isometry. -/
noncomputable def physicalStateLinearMap
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) :
    P.PositiveTimeObservable →ₗ[ℝ] P.PhysicalHilbert := by
  change P.PositiveTimeObservable →ₗ[ℝ]
    UniformSpace.Completion P.OSSeparatedPreHilbert
  exact
    (UniformSpace.Completion.toComplₗᵢ
      (𝕜 := ℝ) (E := P.OSSeparatedPreHilbert)).toLinearMap.comp
      P.osClassLinearMap

@[simp] theorem physicalStateLinearMap_apply
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S)
    (F : P.PositiveTimeObservable) :
    P.physicalStateLinearMap F = P.physicalState F := by
  change
    ((P.osClass F : P.OSSeparatedPreHilbert) :
      UniformSpace.Completion P.OSSeparatedPreHilbert) =
    ((P.osClass F : P.OSSeparatedPreHilbert) :
      UniformSpace.Completion P.OSSeparatedPreHilbert)
  rfl

/-- The OS quotient followed by Hilbert completion preserves the observable
seminorm exactly. -/
@[simp] theorem norm_physicalState_eq_observableNorm
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S)
    (F : P.PositiveTimeObservable) :
    ‖P.physicalState F‖ = ‖F‖ := by
  have hsq : ‖P.physicalState F‖ ^ 2 = ‖F‖ ^ 2 := by
    calc
      ‖P.physicalState F‖ ^ 2 =
          inner ℝ (P.physicalState F) (P.physicalState F) := by
            symm
            exact real_inner_self_eq_norm_sq _
      _ = inner ℝ F F := P.inner_physicalState_physicalState F F
      _ = ‖F‖ ^ 2 := real_inner_self_eq_norm_sq F
  nlinarith [norm_nonneg (P.physicalState F), norm_nonneg F]

/-- The canonical represented-state map is an actual real-linear isometry from
the observable seminormed carrier into the completed OS Hilbert space. -/
noncomputable def physicalStateLinearIsometry
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) :
    P.PositiveTimeObservable →ₗᵢ[ℝ] P.PhysicalHilbert where
  toLinearMap := P.physicalStateLinearMap
  norm_map' := P.norm_physicalState_eq_observableNorm

@[simp] theorem physicalStateLinearIsometry_apply
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S)
    (F : P.PositiveTimeObservable) :
    P.physicalStateLinearIsometry F = P.physicalState F :=
  P.physicalStateLinearMap_apply F

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

/-- Observable-norm continuity passes through the canonical OS quotient and
completion isometry, yielding continuity on represented physical states. -/
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
          (nhds (M.observables.physicalState F)) := by
      have hMap :=
        M.observables.physicalStateLinearIsometry.continuous.tendsto F
      simpa using hMap.comp (hT.tendsto_zero_on_observable F)
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
