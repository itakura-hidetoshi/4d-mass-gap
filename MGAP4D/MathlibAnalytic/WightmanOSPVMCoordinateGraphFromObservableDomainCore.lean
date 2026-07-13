import MGAP4D.MathlibAnalytic.WightmanOSPVMCoordinateGraphFromObservableNormContinuity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Function Set Filter Topology

noncomputable section

namespace EuclideanYangMillsOSPositiveTimeObservableConstruction

/-- The canonical represented-state map respects the scalar multiple of a
difference.  The proof uses only the public OS inner-product identity, so the
opaque completion and its transported instances remain sealed. -/
theorem physicalState_smul_sub
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S)
    (r : ℝ) (F G : P.PositiveTimeObservable) :
    P.physicalState (r • (F - G)) =
      r • (P.physicalState F - P.physicalState G) := by
  have hsq :
      ‖P.physicalState (r • (F - G)) -
          r • (P.physicalState F - P.physicalState G)‖ ^ 2 = 0 := by
    calc
      ‖P.physicalState (r • (F - G)) -
          r • (P.physicalState F - P.physicalState G)‖ ^ 2 =
          inner ℝ
            (P.physicalState (r • (F - G)) -
              r • (P.physicalState F - P.physicalState G))
            (P.physicalState (r • (F - G)) -
              r • (P.physicalState F - P.physicalState G)) := by
        symm
        exact real_inner_self_eq_norm_sq _
      _ = 0 := by
        simp_rw [inner_sub_left, inner_sub_right, inner_smul_left,
          inner_smul_right]
        simp_rw [P.inner_physicalState_physicalState]
        ring_nf
  have hnorm :
      ‖P.physicalState (r • (F - G)) -
          r • (P.physicalState F - P.physicalState G)‖ = 0 := by
    nlinarith [norm_nonneg
      (P.physicalState (r • (F - G)) -
        r • (P.physicalState F - P.physicalState G))]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end EuclideanYangMillsOSPositiveTimeObservableConstruction

namespace EuclideanYangMillsOSPhysicalTimeTranslation

/-- An observable graph core for the physical Hamiltonian.

The core supplies actual Euclidean observables, their observable-norm right
derivatives, and the identification of those derivatives with `-H` on the
represented states.  Graph-density is stated directly in the two coordinates
of the Hamiltonian graph.  The final field is the uniform graph estimate needed
to pass difference quotients from the core to the full closed Hamiltonian
domain; it is strictly weaker data than postulating the derivative limit on
every domain vector. -/
structure RightDerivativeOnObservableDomainCore
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) where
  CoreObservable : Type
  observable : CoreObservable → M.observables.PositiveTimeObservable
  domain_mem :
    ∀ F : CoreObservable,
      M.observables.physicalState (observable F) ∈ M.hamiltonian.domain
  derivativeObservable :
    CoreObservable → M.observables.PositiveTimeObservable
  observableDerivativeLimit :
    ∀ F : CoreObservable,
      Tendsto
        (fun t : ℝ =>
          t⁻¹ • (T.observableTranslate t (observable F) - observable F))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (derivativeObservable F))
  derivativeState_eq_neg_hamiltonian :
    ∀ F : CoreObservable,
      M.observables.physicalState (derivativeObservable F) =
        -(M.hamiltonian
          ⟨M.observables.physicalState (observable F), domain_mem F⟩)
  graphDense :
    ∀ (x : M.hamiltonian.domain) (ε : ℝ), 0 < ε →
      ∃ F : CoreObservable,
        dist (M.observables.physicalState (observable F))
            (x : M.observables.PhysicalHilbert) < ε ∧
          dist
            (M.hamiltonian
              ⟨M.observables.physicalState (observable F), domain_mem F⟩)
            (M.hamiltonian x) < ε
  differenceQuotient_graph_nonexpansive :
    ∀ (t : ℝ), 0 < t → ∀ x y : M.hamiltonian.domain,
      dist
          (t⁻¹ •
            (T.operator t (x : M.observables.PhysicalHilbert) -
              (x : M.observables.PhysicalHilbert)))
          (t⁻¹ •
            (T.operator t (y : M.observables.PhysicalHilbert) -
              (y : M.observables.PhysicalHilbert))) ≤
        dist (x : M.observables.PhysicalHilbert)
            (y : M.observables.PhysicalHilbert) +
          dist (M.hamiltonian x) (M.hamiltonian y)

namespace RightDerivativeOnObservableDomainCore

/-- Observable-norm differentiation passes through the canonical OS isometry
and the dense-state semigroup identity.  This proves the physical right
derivative formula on every represented member of the observable core. -/
theorem rightDerivativeLimit_on_representedCore
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (hD : T.RightDerivativeOnObservableDomainCore)
    (F : hD.CoreObservable) :
    Tendsto
      (fun t : ℝ =>
        t⁻¹ •
          (T.operator t
              (M.observables.physicalState (hD.observable F)) -
            M.observables.physicalState (hD.observable F)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (-(M.hamiltonian
          ⟨M.observables.physicalState (hD.observable F),
            hD.domain_mem F⟩))) := by
  have hMapped :
      Tendsto
        (fun t : ℝ =>
          M.observables.physicalState
            (t⁻¹ •
              (T.observableTranslate t (hD.observable F) -
                hD.observable F)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (M.observables.physicalState (hD.derivativeObservable F))) :=
    M.observables.physicalState_isometry.continuous.tendsto
      (hD.derivativeObservable F)
      |>.comp (hD.observableDerivativeLimit F)
  have hLinear :
      Tendsto
        (fun t : ℝ =>
          t⁻¹ •
            (M.observables.physicalState
                (T.observableTranslate t (hD.observable F)) -
              M.observables.physicalState (hD.observable F)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (M.observables.physicalState (hD.derivativeObservable F))) := by
    simpa only [M.observables.physicalState_smul_sub] using hMapped
  have hEventually :
      (fun t : ℝ =>
        t⁻¹ •
          (T.operator t
              (M.observables.physicalState (hD.observable F)) -
            M.observables.physicalState (hD.observable F))) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        t⁻¹ •
          (M.observables.physicalState
              (T.observableTranslate t (hD.observable F)) -
            M.observables.physicalState (hD.observable F))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [T.operator_on_dense_state t (hD.observable F) (le_of_lt ht)]
  simpa only [hD.derivativeState_eq_neg_hamiltonian F] using
    hLinear.congr' hEventually.symm

/-- Graph-density plus the graph-nonexpansive difference-quotient estimate
extends the represented-core derivative to every vector in the Hamiltonian
domain.  This is the actual closure step replacing the former independent
`RightDerivativeOnHamiltonianDomain` input. -/
theorem rightDerivativeLimit
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (hD : T.RightDerivativeOnObservableDomainCore)
    (x : M.hamiltonian.domain) :
    Tendsto
      (fun t : ℝ =>
        t⁻¹ •
          (T.operator t (x : M.observables.PhysicalHilbert) -
            (x : M.observables.PhysicalHilbert)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-(M.hamiltonian x))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε6 : 0 < ε / 6 := by positivity
  obtain ⟨F, hState, hHamiltonian⟩ := hD.graphDense x (ε / 6) hε6
  have hCore := hD.rightDerivativeLimit_on_representedCore F
  rw [Metric.tendsto_nhds] at hCore
  have hε3 : 0 < ε / 3 := by positivity
  have hEventuallyCore := hCore (ε / 3) hε3
  filter_upwards [hEventuallyCore, self_mem_nhdsWithin] with t ht htPositive
  let y : M.hamiltonian.domain :=
    ⟨M.observables.physicalState (hD.observable F), hD.domain_mem F⟩
  have hGraphBound :=
    hD.differenceQuotient_graph_nonexpansive t htPositive x y
  have hState' :
      dist (x : M.observables.PhysicalHilbert)
          (y : M.observables.PhysicalHilbert) < ε / 6 := by
    simpa [y, dist_comm] using hState
  have hHamiltonian' :
      dist (M.hamiltonian x) (M.hamiltonian y) < ε / 6 := by
    simpa [y, dist_comm] using hHamiltonian
  have hNegHamiltonian :
      dist (-(M.hamiltonian y)) (-(M.hamiltonian x)) < ε / 6 := by
    simpa [y] using hHamiltonian
  calc
    dist
        (t⁻¹ •
          (T.operator t (x : M.observables.PhysicalHilbert) -
            (x : M.observables.PhysicalHilbert)))
        (-(M.hamiltonian x)) ≤
      dist
          (t⁻¹ •
            (T.operator t (x : M.observables.PhysicalHilbert) -
              (x : M.observables.PhysicalHilbert)))
          (t⁻¹ •
            (T.operator t (y : M.observables.PhysicalHilbert) -
              (y : M.observables.PhysicalHilbert))) +
        dist
          (t⁻¹ •
            (T.operator t (y : M.observables.PhysicalHilbert) -
              (y : M.observables.PhysicalHilbert)))
          (-(M.hamiltonian y)) +
        dist (-(M.hamiltonian y)) (-(M.hamiltonian x)) :=
      dist_triangle4 _ _ _ _
    _ < ε := by
      have hGraphSmall :
          dist
              (t⁻¹ •
                (T.operator t (x : M.observables.PhysicalHilbert) -
                  (x : M.observables.PhysicalHilbert)))
              (t⁻¹ •
                (T.operator t (y : M.observables.PhysicalHilbert) -
                  (y : M.observables.PhysicalHilbert))) < ε / 3 := by
        linarith
      have hCore' :
          dist
              (t⁻¹ •
                (T.operator t (y : M.observables.PhysicalHilbert) -
                  (y : M.observables.PhysicalHilbert)))
              (-(M.hamiltonian y)) < ε / 3 := by
        simpa [y] using ht
      linarith

/-- Package the graph-core closure theorem in the pre-existing derivative
interface consumed by the physical strong-continuity core. -/
noncomputable def toRightDerivativeOnHamiltonianDomain
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (hD : T.RightDerivativeOnObservableDomainCore) :
    T.RightDerivativeOnHamiltonianDomain where
  rightDerivativeLimit := hD.rightDerivativeLimit

end RightDerivativeOnObservableDomainCore

/-- The canonical pure-PVM coordinate graph now consumes observable-norm
continuity and an observable Hamiltonian graph core.  The Hamiltonian-domain
right derivative is theorem-generated rather than supplied independently. -/
noncomputable def toCanonicalPVMCoordinateGraphOfLaplaceExchangeGapObservableNormContinuityAndDomainCore
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M.toExplicitModel)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M.toExplicitModel)
    {m : ℝ} (hGap : M.toExplicitModel.HasMassGap m)
    (L : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      M.toExplicitModel A.toScalarSpectralRealization T.toEuclideanTimeSemigroup)
    (hContinuous : T.StrongContinuityOnObservableNorm)
    (hDerivativeCore : T.RightDerivativeOnObservableDomainCore)
    (hExchange : T.ReflectionTimeTranslationExchange) :
    ExplicitWightmanOSCanonicalRestrictedPVMCoordinateGraph M.toExplicitModel :=
  T.toCanonicalPVMCoordinateGraphOfLaplaceExchangeGapObservableNormContinuityAndDerivative
    A B hGap L hContinuous hDerivativeCore.toRightDerivativeOnHamiltonianDomain
    hExchange

end EuclideanYangMillsOSPhysicalTimeTranslation

end

end MathlibAnalytic
end MGAP4D
