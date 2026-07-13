import MGAP4D.MathlibAnalytic.WightmanOSPVMCoordinateGraphFromObservableDomainCore
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Function Set Filter Topology

noncomputable section

namespace EuclideanYangMillsOSPhysicalTimeTranslation

/-- Observable Hamiltonian core stated in the canonical graph norm.

Compared with `RightDerivativeOnObservableDomainCore`, graph approximation is
supplied as one intrinsic estimate

`dist state x + dist (H state) (H x) < ε`

rather than as two independent coordinate fields. -/
structure ObservableHamiltonianGraphNormCore
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
  graphNormDense :
    ∀ (x : M.hamiltonian.domain) (ε : ℝ), 0 < ε →
      ∃ F : CoreObservable,
        dist (M.observables.physicalState (observable F))
            (x : M.observables.PhysicalHilbert) +
          dist
            (M.hamiltonian
              ⟨M.observables.physicalState (observable F), domain_mem F⟩)
            (M.hamiltonian x) < ε

namespace ObservableHamiltonianGraphNormCore

/-- Density in the summed Hamiltonian graph norm implies density in each graph
coordinate. -/
theorem graphDense
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (C : T.ObservableHamiltonianGraphNormCore)
    (x : M.hamiltonian.domain) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : C.CoreObservable,
      dist (M.observables.physicalState (C.observable F))
          (x : M.observables.PhysicalHilbert) < ε ∧
        dist
          (M.hamiltonian
            ⟨M.observables.physicalState (C.observable F), C.domain_mem F⟩)
          (M.hamiltonian x) < ε := by
  obtain ⟨F, hF⟩ := C.graphNormDense x ε hε
  refine ⟨F, ?_, ?_⟩
  · have hNonneg :
        0 ≤ dist
          (M.hamiltonian
            ⟨M.observables.physicalState (C.observable F), C.domain_mem F⟩)
          (M.hamiltonian x) := dist_nonneg
    linarith
  · have hNonneg :
        0 ≤ dist (M.observables.physicalState (C.observable F))
          (x : M.observables.PhysicalHilbert) := dist_nonneg
    linarith

end ObservableHamiltonianGraphNormCore

/-- Factorization of the physical difference quotient through a contractive
bounded average acting on the Hamiltonian value.

For a contraction semigroup this average is canonically
`(1/t) ∫₀ᵗ T_s ds`.  Keeping the average as a bounded operator isolates exactly
the semigroup estimate needed by the graph-core closure theorem, without
postulating the derivative limit itself. -/
structure DifferenceQuotientGeneratorFactorization
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) where
  generatorAverage :
    ℝ → M.observables.PhysicalHilbert →L[ℝ] M.observables.PhysicalHilbert
  generatorAverage_contraction :
    ∀ (t : ℝ), 0 < t → ∀ ψ : M.observables.PhysicalHilbert,
      ‖generatorAverage t ψ‖ ≤ ‖ψ‖
  quotient_eq_neg_generatorAverage :
    ∀ (t : ℝ), 0 < t → ∀ x : M.hamiltonian.domain,
      t⁻¹ •
          (T.operator t (x : M.observables.PhysicalHilbert) -
            (x : M.observables.PhysicalHilbert)) =
        -(generatorAverage t (M.hamiltonian x))

namespace DifferenceQuotientGeneratorFactorization

/-- Contractivity of the generator average gives the sharp pairwise graph
estimate: the physical difference quotient is one-Lipschitz in the Hamiltonian
coordinate. -/
theorem differenceQuotient_dist_le_hamiltonian_dist
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (Q : T.DifferenceQuotientGeneratorFactorization)
    (t : ℝ) (ht : 0 < t) (x y : M.hamiltonian.domain) :
    dist
        (t⁻¹ •
          (T.operator t (x : M.observables.PhysicalHilbert) -
            (x : M.observables.PhysicalHilbert)))
        (t⁻¹ •
          (T.operator t (y : M.observables.PhysicalHilbert) -
            (y : M.observables.PhysicalHilbert))) ≤
      dist (M.hamiltonian x) (M.hamiltonian y) := by
  rw [Q.quotient_eq_neg_generatorAverage t ht x,
    Q.quotient_eq_neg_generatorAverage t ht y]
  rw [dist_neg_neg]
  calc
    dist (Q.generatorAverage t (M.hamiltonian x))
        (Q.generatorAverage t (M.hamiltonian y)) =
      ‖Q.generatorAverage t (M.hamiltonian x - M.hamiltonian y)‖ := by
        rw [dist_eq_norm, map_sub]
    _ ≤ ‖M.hamiltonian x - M.hamiltonian y‖ :=
      Q.generatorAverage_contraction t ht _
    _ = dist (M.hamiltonian x) (M.hamiltonian y) := by
      rw [dist_eq_norm]

/-- The sharp Hamiltonian-coordinate estimate implies the weaker summed graph
estimate consumed by `RightDerivativeOnObservableDomainCore`. -/
theorem differenceQuotient_graph_nonexpansive
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (Q : T.DifferenceQuotientGeneratorFactorization)
    (t : ℝ) (ht : 0 < t) (x y : M.hamiltonian.domain) :
    dist
        (t⁻¹ •
          (T.operator t (x : M.observables.PhysicalHilbert) -
            (x : M.observables.PhysicalHilbert)))
        (t⁻¹ •
          (T.operator t (y : M.observables.PhysicalHilbert) -
            (y : M.observables.PhysicalHilbert))) ≤
      dist (x : M.observables.PhysicalHilbert)
          (y : M.observables.PhysicalHilbert) +
        dist (M.hamiltonian x) (M.hamiltonian y) := by
  exact (Q.differenceQuotient_dist_le_hamiltonian_dist t ht x y).trans
    (le_add_of_nonneg_left dist_nonneg)

end DifferenceQuotientGeneratorFactorization

/-- Graph-norm density and the contractive generator-average factorization
construct the complete observable-domain derivative core used by PR #828. -/
noncomputable def ObservableHamiltonianGraphNormCore.toRightDerivativeOnObservableDomainCore
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (C : T.ObservableHamiltonianGraphNormCore)
    (Q : T.DifferenceQuotientGeneratorFactorization) :
    T.RightDerivativeOnObservableDomainCore where
  CoreObservable := C.CoreObservable
  observable := C.observable
  domain_mem := C.domain_mem
  derivativeObservable := C.derivativeObservable
  observableDerivativeLimit := C.observableDerivativeLimit
  derivativeState_eq_neg_hamiltonian := C.derivativeState_eq_neg_hamiltonian
  graphDense := C.graphDense
  differenceQuotient_graph_nonexpansive :=
    Q.differenceQuotient_graph_nonexpansive

/-- The canonical pure-PVM coordinate graph now consumes intrinsic graph-norm
core density and a contractive generator-average factorization instead of the
two raw closure fields. -/
noncomputable def toCanonicalPVMCoordinateGraphOfLaplaceExchangeGapObservableGraphNormCore
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M.toExplicitModel)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M.toExplicitModel)
    {m : ℝ} (hGap : M.toExplicitModel.HasMassGap m)
    (L : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      M.toExplicitModel A.toScalarSpectralRealization T.toEuclideanTimeSemigroup)
    (hContinuous : T.StrongContinuityOnObservableNorm)
    (C : T.ObservableHamiltonianGraphNormCore)
    (Q : T.DifferenceQuotientGeneratorFactorization)
    (hExchange : T.ReflectionTimeTranslationExchange) :
    ExplicitWightmanOSCanonicalRestrictedPVMCoordinateGraph M.toExplicitModel :=
  T.toCanonicalPVMCoordinateGraphOfLaplaceExchangeGapObservableNormContinuityAndDomainCore
    A B hGap L hContinuous C.toRightDerivativeOnObservableDomainCore Q hExchange

end EuclideanYangMillsOSPhysicalTimeTranslation

end

end MathlibAnalytic
end MGAP4D
