import MGAP4D.MathlibAnalytic.ConfluentCauchyKernelFiniteEvaluationLinearIndependence
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Sequences
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped LinearPMap

universe u v

/-- A finite family of pairwise distinct nonzero eigenvectors in the domain of
one closed partially defined real-linear operator. -/
structure FiniteDistinctClosedEigenpairData
    {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →ₗ.[ℝ] E)
    (witnessCount : ℕ) where
  SpectralIndex : Type v
  [spectralFintype : Fintype SpectralIndex]
  spectralValue : SpectralIndex → ℝ
  spectralValue_injective : Function.Injective spectralValue
  spectralCard : Fintype.card SpectralIndex = witnessCount
  spectralVector : SpectralIndex → A.domain
  spectralVector_ne_zero : ∀ k, (spectralVector k : E) ≠ 0
  apply_spectralVector :
    ∀ k, A (spectralVector k) = spectralValue k • (spectralVector k : E)

attribute [instance] FiniteDistinctClosedEigenpairData.spectralFintype

/-- Exact domain eigenpairs above a threshold separate every finite confluent
Cauchy window whose nodes lie strictly below that threshold. -/
theorem FiniteDistinctClosedEigenpairData.confluentCauchyEvaluationLinearIndependent
    {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E →ₗ.[ℝ] E}
    {witnessCount : ℕ}
    (D : FiniteDistinctClosedEigenpairData A witnessCount)
    {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ)
    (orderCap : ℕ)
    (threshold : ℝ)
    (hValueInjective : Function.Injective value)
    (hValueBelow : ∀ i, value i < threshold)
    (hSpectralAbove : ∀ k, threshold ≤ D.spectralValue k)
    (hCard : witnessCount = Fintype.card ι * orderCap) :
    LinearIndependent ℝ
      (fun p : ι × Fin orderCap => fun k : D.SpectralIndex =>
        ((D.spectralValue k - value p.1)⁻¹ ^ (p.2.1 + 1))) := by
  apply ContinuousLinearMap.confluentCauchyKernel_linearIndependent
    value orderCap D.spectralValue
    hValueInjective D.spectralValue_injective
  · calc
      Fintype.card D.SpectralIndex = witnessCount := D.spectralCard
      _ = Fintype.card ι * orderCap := hCard
  · intro k i
    exact ne_of_gt (lt_of_lt_of_le (hValueBelow i) (hSpectralAbove k))

/-- Finite approximate eigenpairs for a partially defined operator, together
with strong limits of their values and vectors and a vanishing graph residual.

The approximating vectors already lie in the target operator domain.  In an
actual finite-volume application they are supplied by a graph-compatible lift
of finite-volume eigenvectors into the common continuum carrier. -/
structure ClosedLinearPMapFiniteApproximateEigenpairStrongLimitData
    {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →ₗ.[ℝ] E)
    (witnessCount : ℕ) where
  SpectralIndex : Type v
  [spectralFintype : Fintype SpectralIndex]
  approximateValue : ℕ → SpectralIndex → ℝ
  spectralValue : SpectralIndex → ℝ
  spectralValue_injective : Function.Injective spectralValue
  spectralCard : Fintype.card SpectralIndex = witnessCount
  approximateVector : ℕ → SpectralIndex → A.domain
  spectralVector : SpectralIndex → E
  spectralVector_ne_zero : ∀ k, spectralVector k ≠ 0
  approximateValue_tendsto :
    ∀ k,
      Tendsto (fun n => approximateValue n k) atTop
        (nhds (spectralValue k))
  approximateVector_tendsto :
    ∀ k,
      Tendsto (fun n => (approximateVector n k : E)) atTop
        (nhds (spectralVector k))
  residual_tendsto_zero :
    ∀ k,
      Tendsto
        (fun n =>
          A (approximateVector n k) -
            approximateValue n k • (approximateVector n k : E))
        atTop (nhds 0)

attribute [instance]
  ClosedLinearPMapFiniteApproximateEigenpairStrongLimitData.spectralFintype

namespace ClosedLinearPMapFiniteApproximateEigenpairStrongLimitData

variable {E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : E →ₗ.[ℝ] E}
variable {witnessCount : ℕ}

/-- Vanishing residual, scalar convergence, and vector convergence imply
convergence of the operator images to the limiting eigenvalue action. -/
theorem apply_approximateVector_tendsto
    (D : ClosedLinearPMapFiniteApproximateEigenpairStrongLimitData
      A witnessCount)
    (k : D.SpectralIndex) :
    Tendsto (fun n => A (D.approximateVector n k)) atTop
      (nhds (D.spectralValue k • D.spectralVector k)) := by
  have hsmul :
      Tendsto
        (fun n => D.approximateValue n k •
          (D.approximateVector n k : E))
        atTop
        (nhds (D.spectralValue k • D.spectralVector k)) :=
    (D.approximateValue_tendsto k).smul
      (D.approximateVector_tendsto k)
  simpa only [sub_add_cancel, zero_add] using
    (D.residual_tendsto_zero k).add hsmul

/-- The limiting vector-value pair lies in the graph of every closed target
operator. -/
theorem limit_pair_mem_graph
    (D : ClosedLinearPMapFiniteApproximateEigenpairStrongLimitData
      A witnessCount)
    (hClosed : A.IsClosed)
    (k : D.SpectralIndex) :
    (D.spectralVector k, D.spectralValue k • D.spectralVector k) ∈ A.graph := by
  have hPairTendsto :
      Tendsto
        (fun n =>
          ((D.approximateVector n k : E),
            A (D.approximateVector n k)))
        atTop
        (nhds
          (D.spectralVector k,
            D.spectralValue k • D.spectralVector k)) := by
    simpa only [nhds_prod_eq] using
      (D.approximateVector_tendsto k).prodMk
        (D.apply_approximateVector_tendsto k)
  have hGraphClosed : _root_.IsClosed (A.graph : Set (E × E)) := hClosed
  exact hGraphClosed.mem_of_tendsto hPairTendsto
    (Eventually.of_forall fun n => A.mem_graph (D.approximateVector n k))

/-- The limiting vector, now equipped with the domain proof obtained from graph
closedness. -/
noncomputable def spectralDomainVector
    (D : ClosedLinearPMapFiniteApproximateEigenpairStrongLimitData
      A witnessCount)
    (hClosed : A.IsClosed)
    (k : D.SpectralIndex) : A.domain :=
  Classical.choose
    ((A.mem_graph_iff).mp (D.limit_pair_mem_graph hClosed k))

/-- The domain representative chosen from the closed graph has the prescribed
ambient limiting vector. -/
@[simp] theorem coe_spectralDomainVector
    (D : ClosedLinearPMapFiniteApproximateEigenpairStrongLimitData
      A witnessCount)
    (hClosed : A.IsClosed)
    (k : D.SpectralIndex) :
    (D.spectralDomainVector hClosed k : E) = D.spectralVector k :=
  (Classical.choose_spec
    ((A.mem_graph_iff).mp (D.limit_pair_mem_graph hClosed k))).1

/-- Closedness upgrades every strong approximate eigenpair limit to an exact
eigenpair of the target operator. -/
theorem apply_spectralDomainVector
    (D : ClosedLinearPMapFiniteApproximateEigenpairStrongLimitData
      A witnessCount)
    (hClosed : A.IsClosed)
    (k : D.SpectralIndex) :
    A (D.spectralDomainVector hClosed k) =
      D.spectralValue k • (D.spectralDomainVector hClosed k : E) := by
  have hValue :=
    (Classical.choose_spec
      ((A.mem_graph_iff).mp (D.limit_pair_mem_graph hClosed k))).2
  simpa only [D.coe_spectralDomainVector hClosed k] using hValue

/-- The strong approximate-eigenpair package canonically produces exact finite
domain eigenpairs for a closed target operator. -/
noncomputable def toFiniteDistinctClosedEigenpairData
    (D : ClosedLinearPMapFiniteApproximateEigenpairStrongLimitData
      A witnessCount)
    (hClosed : A.IsClosed) :
    FiniteDistinctClosedEigenpairData A witnessCount :=
  { SpectralIndex := D.SpectralIndex
    spectralFintype := D.spectralFintype
    spectralValue := D.spectralValue
    spectralValue_injective := D.spectralValue_injective
    spectralCard := D.spectralCard
    spectralVector := D.spectralDomainVector hClosed
    spectralVector_ne_zero := by
      intro k
      simpa only [D.coe_spectralDomainVector hClosed k] using
        D.spectralVector_ne_zero k
    apply_spectralVector := D.apply_spectralDomainVector hClosed }

/-- Closed approximate eigenpair limits directly supply arbitrary-order
confluent Cauchy spectral separation. -/
theorem confluentCauchyEvaluationLinearIndependent
    (D : ClosedLinearPMapFiniteApproximateEigenpairStrongLimitData
      A witnessCount)
    (hClosed : A.IsClosed)
    {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ)
    (orderCap : ℕ)
    (threshold : ℝ)
    (hValueInjective : Function.Injective value)
    (hValueBelow : ∀ i, value i < threshold)
    (hSpectralAbove : ∀ k, threshold ≤ D.spectralValue k)
    (hCard : witnessCount = Fintype.card ι * orderCap) :
    LinearIndependent ℝ
      (fun p : ι × Fin orderCap => fun k : D.SpectralIndex =>
        ((D.spectralValue k - value p.1)⁻¹ ^ (p.2.1 + 1))) :=
  (D.toFiniteDistinctClosedEigenpairData hClosed)
    |>.confluentCauchyEvaluationLinearIndependent
      value orderCap threshold hValueInjective hValueBelow hSpectralAbove hCard

end ClosedLinearPMapFiniteApproximateEigenpairStrongLimitData

end

end MathlibAnalytic
end MGAP4D
