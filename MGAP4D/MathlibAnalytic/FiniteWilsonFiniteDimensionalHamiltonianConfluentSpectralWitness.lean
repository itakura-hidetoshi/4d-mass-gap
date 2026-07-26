import MGAP4D.MathlibAnalytic.FiniteDimensionalSymmetricSelectedEigenbasisSpectralWitness
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set

universe u

/-- A selected finite family of pairwise distinct eigenvalues from the
finite-dimensional symmetric Hamiltonian at one Wilson scale. -/
abbrev FiniteWilsonSelectedDistinctHamiltonianEigenbasisData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W)
    (n : ℕ)
    (witnessCount : ℕ) :=
  FiniteDimensionalSymmetricEigenbasisSelectionData
    (D.hamiltonian n)
    (D.hamiltonianSymmetric n)
    D.StateDimension
    witnessCount
    D.stateFinrank

/-- Finite Wilson spectral witnesses for one finite node-order window.  The
selected Hamiltonian eigenvalues are required to be pairwise distinct, while
non-pole separation follows from the existing exact-gap lower bound. -/
structure FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {α : Type u}
    [DecidableEq α]
    (D : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W)
    (n : ℕ)
    (value : α → ℝ)
    (nodes : Finset α)
    (orderCap : ℕ) where
  selection :
    FiniteWilsonSelectedDistinctHamiltonianEigenbasisData
      D n (nodes.card * orderCap)
  valueInjectiveOnNodes : Set.InjOn value nodes
  value_lt_exactGapOnNodes :
    ∀ a ∈ nodes, value a < exactGapValueReal

namespace FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable {α : Type u} [DecidableEq α]
variable {D : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W}
variable {n : ℕ}
variable {value : α → ℝ}
variable {nodes : Finset α}
variable {orderCap : ℕ}

/-- The selected finite spectral index type. -/
abbrev SpectralIndex
    (R : FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
      D n value nodes orderCap) :=
  R.selection.SpectralIndex

/-- The selected finite-volume Hamiltonian energy. -/
def spectralValue
    (R : FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
      D n value nodes orderCap)
    (k : R.SpectralIndex) : ℝ :=
  R.selection.spectralValue k

/-- The selected finite-volume Hamiltonian eigenvector. -/
def spectralVector
    (R : FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
      D n value nodes orderCap)
    (k : R.SpectralIndex) : D.StateSpace :=
  R.selection.spectralVector k

/-- Selected finite-volume Hamiltonian energies are pairwise distinct. -/
theorem spectralValue_injective
    (R : FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
      D n value nodes orderCap) :
    Function.Injective R.spectralValue := by
  simpa [spectralValue] using R.selection.spectralValue_injective

/-- The witness count is exactly the node count times the positive-power cap. -/
theorem spectralCard
    (R : FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
      D n value nodes orderCap) :
    Fintype.card R.SpectralIndex = nodes.card * orderCap := by
  simpa [SpectralIndex] using R.selection.spectralCard

/-- Every selected finite-volume eigenbasis vector is nonzero. -/
theorem spectralVector_ne_zero
    (R : FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
      D n value nodes orderCap)
    (k : R.SpectralIndex) :
    R.spectralVector k ≠ 0 := by
  simpa [spectralVector] using R.selection.spectralVector_ne_zero k

/-- Every selected vector satisfies the finite-volume Hamiltonian eigenvalue
equation. -/
theorem hamiltonian_apply_spectralVector
    (R : FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
      D n value nodes orderCap)
    (k : R.SpectralIndex) :
    D.hamiltonian n (R.spectralVector k) =
      R.spectralValue k • R.spectralVector k := by
  simpa [spectralVector, spectralValue] using
    R.selection.apply_spectralVector k

/-- Every selected finite-volume energy lies above the public exact gap. -/
theorem spectralValue_ge_exactGap
    (R : FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
      D n value nodes orderCap)
    (k : R.SpectralIndex) :
    exactGapValueReal ≤ R.spectralValue k := by
  simpa [spectralValue,
    FiniteDimensionalSymmetricEigenbasisSelectionData.spectralValue] using
    D.hamiltonianEigenvalues_ge_exactGap n k.1

/-- The requested node-order witness count cannot exceed the finite transfer
state dimension. -/
theorem requiredDimension_le
    (R : FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
      D n value nodes orderCap) :
    nodes.card * orderCap ≤ D.StateDimension := by
  simpa using R.selection.witnessCount_le_dimension

/-- The selected finite-volume Hamiltonian eigenvalues automatically separate
all inverse-power Cauchy columns in the requested below-gap window. -/
theorem scalarEvaluationLinearIndependent
    (R : FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
      D n value nodes orderCap) :
    LinearIndependent ℝ
      (fun p : nodes × Fin orderCap => fun k : R.SpectralIndex =>
        ((R.spectralValue k - value p.1.1)⁻¹ ^ (p.2.1 + 1))) := by
  classical
  have hNodeInjective : Function.Injective
      (fun a : nodes => value a.1) := by
    intro left right hvalue
    apply Subtype.ext
    exact R.valueInjectiveOnNodes left.2 right.2 hvalue
  have hNodeBelow : ∀ a : nodes,
      value a.1 < exactGapValueReal := by
    intro a
    exact R.value_lt_exactGapOnNodes a.1 a.2
  have hSpectralAbove : ∀ k : R.selection.SpectralIndex,
      exactGapValueReal ≤ R.selection.spectralValue k := by
    intro k
    simpa [FiniteDimensionalSymmetricEigenbasisSelectionData.spectralValue] using
      D.hamiltonianEigenvalues_ge_exactGap n k.1
  have hSeparated :=
    R.selection.confluentCauchyEvaluationLinearIndependent
      (fun a : nodes => value a.1)
      orderCap
      exactGapValueReal
      hNodeInjective
      hNodeBelow
      hSpectralAbove
      (by simp)
  simpa [spectralValue, SpectralIndex] using hSeparated

/-- Forget the finite Wilson presentation and retain a transport-ready family of
pairwise distinct finite-volume Hamiltonian eigenpairs. -/
noncomputable def toFiniteDistinctEigenpairData
    (R : FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
      D n value nodes orderCap) :
    FiniteDistinctEigenpairData
      (D.hamiltonian n) (nodes.card * orderCap) :=
  R.selection.toFiniteDistinctEigenpairData

end FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData

end

end MathlibAnalytic
end MGAP4D