import MGAP4D.MathlibAnalytic.WightmanOSPVMCoordinateGraphFromStrongContinuityCore
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Function Set Filter Topology

noncomputable section

namespace EuclideanYangMillsOSPositiveTimeObservableConstruction

/-- The canonical real-linear projection from positive-time observables to the
separated Osterwalder--Schrader pre-Hilbert quotient. -/
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

/-- Every separated OS class has a positive-time observable representative. -/
theorem osClassLinearMap_surjective
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) :
    Function.Surjective P.osClassLinearMap := by
  intro x
  rcases SeparationQuotient.surjective_mk x with ⟨F, rfl⟩
  exact ⟨F, rfl⟩

/-- Positive-time observables represented in the completed physical Hilbert
space, bundled as a real-linear map. -/
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

/-- Positive-time observables represent a dense linear family in the completed
OS physical Hilbert space. -/
theorem physicalStateLinearMap_denseRange
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) :
    DenseRange P.physicalStateLinearMap := by
  intro x
  exact closure_mono
    (by
      rintro y ⟨q, rfl⟩
      rcases SeparationQuotient.surjective_mk q with ⟨F, rfl⟩
      refine ⟨F, ?_⟩
      exact P.physicalStateLinearMap_apply F)
    ((os_preHilbert_dense_in_physical P) x)

end EuclideanYangMillsOSPositiveTimeObservableConstruction

namespace EuclideanYangMillsOSPhysicalTimeTranslation

/-- Minimal strong-continuity input stated only on actual represented
positive-time observables. -/
structure StrongContinuityOnObservableStates
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) : Prop where
  tendsto_zero_on_physicalState :
    ∀ F : M.observables.PositiveTimeObservable,
      Tendsto
        (fun t : ℝ => T.operator t (M.observables.physicalState F))
        (nhdsWithin 0 (Set.Ici 0))
        (nhds (M.observables.physicalState F))

namespace StrongContinuityOnObservableStates

/-- Contractivity and density transfer continuity at time zero from represented
OS observable states to every vector of the completed physical Hilbert space. -/
theorem stronglyContinuousAtZero
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (hT : T.StrongContinuityOnObservableStates)
    (psi : M.observables.PhysicalHilbert) :
    Tendsto (fun t : ℝ => T.operator t psi)
      (nhdsWithin 0 (Set.Ici 0)) (nhds psi) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hepsilon3 : 0 < epsilon / 3 := by positivity
  obtain ⟨F, hF⟩ :=
    M.observables.physicalStateLinearMap_denseRange.exists_dist_lt
      psi hepsilon3
  have hpsiF :
      dist psi (M.observables.physicalState F) < epsilon / 3 := by
    simpa using hF
  have hFpsi :
      dist (M.observables.physicalState F) psi < epsilon / 3 := by
    simpa [dist_comm] using hpsiF
  have hDense := hT.tendsto_zero_on_physicalState F
  rw [Metric.tendsto_nhds] at hDense
  have hEventually := hDense (epsilon / 3) hepsilon3
  have hNonnegative :
      ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ici 0), t ∈ Set.Ici 0 :=
    self_mem_nhdsWithin
  filter_upwards [hEventually, hNonnegative] with t ht htNonnegative
  have ht0 : 0 ≤ t := htNonnegative
  have hleft :
      dist (T.operator t psi)
          (T.operator t (M.observables.physicalState F)) ≤
        dist psi (M.observables.physicalState F) := by
    simpa only [dist_eq_norm, map_sub] using
      T.contraction t ht0 (psi - M.observables.physicalState F)
  calc
    dist (T.operator t psi) psi ≤
        dist (T.operator t psi)
            (T.operator t (M.observables.physicalState F)) +
          dist (T.operator t (M.observables.physicalState F))
            (M.observables.physicalState F) +
          dist (M.observables.physicalState F) psi :=
      dist_triangle4 _ _ _ _
    _ < epsilon := by linarith

end StrongContinuityOnObservableStates

/-- The remaining derivative datum after strong continuity has been generated
from dense observable states. -/
structure RightDerivativeOnHamiltonianDomain
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) : Prop where
  rightDerivativeLimit :
    ∀ x : M.hamiltonian.domain,
      Tendsto
        (fun t : ℝ =>
          t⁻¹ •
            (T.operator t (x : M.observables.PhysicalHilbert) -
              (x : M.observables.PhysicalHilbert)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (-(M.hamiltonian x)))

/-- Observable-state continuity plus the Hamiltonian-domain right derivative
construct the complete strong-continuity core. -/
noncomputable def toStrongContinuityCoreOfObservableStates
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (hContinuous : T.StrongContinuityOnObservableStates)
    (hDerivative : T.RightDerivativeOnHamiltonianDomain) :
    EuclideanYangMillsOSPhysicalStrongContinuityCore T.toCore where
  stronglyContinuousAtZero := by
    intro psi
    simpa [EuclideanYangMillsOSPhysicalTimeTranslation.toCore] using
      hContinuous.stronglyContinuousAtZero psi
  rightDerivativeLimit := by
    intro x
    simpa [EuclideanYangMillsOSPhysicalTimeTranslation.toCore] using
      hDerivative.rightDerivativeLimit x

/-- The pure-PVM mass-gap route therefore needs continuity only on represented
Euclidean observables, together with the actual Hamiltonian-domain derivative. -/
noncomputable def toCanonicalPVMCoordinateGraphOfLaplaceExchangeGapObservableContinuityAndDerivative
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M.toExplicitModel)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M.toExplicitModel)
    {m : ℝ} (hGap : M.toExplicitModel.HasMassGap m)
    (L : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      M.toExplicitModel A.toScalarSpectralRealization T.toEuclideanTimeSemigroup)
    (hContinuous : T.StrongContinuityOnObservableStates)
    (hDerivative : T.RightDerivativeOnHamiltonianDomain)
    (hExchange : T.ReflectionTimeTranslationExchange) :
    ExplicitWightmanOSCanonicalRestrictedPVMCoordinateGraph M.toExplicitModel :=
  T.toCanonicalPVMCoordinateGraphOfLaplaceExchangeGapAndStrongContinuity
    A B hGap L
    (T.toStrongContinuityCoreOfObservableStates hContinuous hDerivative)
    hExchange

end EuclideanYangMillsOSPhysicalTimeTranslation

end

end MathlibAnalytic
end MGAP4D
