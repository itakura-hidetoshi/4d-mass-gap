import MGAP4D.MathlibAnalytic.ConfluentCauchyKernelFiniteEvaluationLinearIndependence
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set

universe u v

/-- A finite family of pairwise spectrally distinct nonzero eigenvectors of one
real linear operator.  This is the transport-ready package produced below from
a selected part of a finite-dimensional symmetric eigenbasis. -/
structure FiniteDistinctEigenpairData
    {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →ₗ[ℝ] E)
    (witnessCount : ℕ) where
  SpectralIndex : Type v
  [spectralFintype : Fintype SpectralIndex]
  spectralValue : SpectralIndex → ℝ
  spectralValue_injective : Function.Injective spectralValue
  spectralCard : Fintype.card SpectralIndex = witnessCount
  spectralVector : SpectralIndex → E
  spectralVector_ne_zero : ∀ k, spectralVector k ≠ 0
  apply_spectralVector :
    ∀ k, A (spectralVector k) = spectralValue k • spectralVector k

attribute [instance] FiniteDistinctEigenpairData.spectralFintype

/-- Spectrally distinct eigenpairs above a threshold separate every finite
confluent Cauchy window whose nodes lie strictly below that threshold. -/
theorem FiniteDistinctEigenpairData.confluentCauchyEvaluationLinearIndependent
    {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A : E →ₗ[ℝ] E}
    {witnessCount : ℕ}
    (D : FiniteDistinctEigenpairData A witnessCount)
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

/-- A finite selection of eigenbasis indices on which the ordered eigenvalue
function is injective.  Finite-dimensionality alone does not imply a simple
spectrum, so this records exactly the minimal distinct-eigenvalue selection. -/
structure FiniteDimensionalSymmetricEigenbasisSelectionData
    {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E)
    (hA : A.IsSymmetric)
    (dimension witnessCount : ℕ)
    (hFinrank : Module.finrank ℝ E = dimension) where
  indices : Finset (Fin dimension)
  eigenvalues_injOn :
    Set.InjOn (hA.eigenvalues hFinrank) indices
  card_indices : indices.card = witnessCount

namespace FiniteDimensionalSymmetricEigenbasisSelectionData

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {A : E →ₗ[ℝ] E}
variable {hA : A.IsSymmetric}
variable {dimension witnessCount : ℕ}
variable {hFinrank : Module.finrank ℝ E = dimension}

/-- The selected finite spectral index type. -/
abbrev SpectralIndex
    (D : FiniteDimensionalSymmetricEigenbasisSelectionData
      A hA dimension witnessCount hFinrank) :=
  D.indices

/-- The selected ordered eigenvalue. -/
def spectralValue
    (D : FiniteDimensionalSymmetricEigenbasisSelectionData
      A hA dimension witnessCount hFinrank)
    (k : D.SpectralIndex) : ℝ :=
  hA.eigenvalues hFinrank k.1

/-- The corresponding vector in Mathlib's orthonormal eigenbasis. -/
def spectralVector
    (D : FiniteDimensionalSymmetricEigenbasisSelectionData
      A hA dimension witnessCount hFinrank)
    (k : D.SpectralIndex) : E :=
  hA.eigenvectorBasis hFinrank k.1

/-- The selected eigenvalues remain injective after passing to the subtype. -/
theorem spectralValue_injective
    (D : FiniteDimensionalSymmetricEigenbasisSelectionData
      A hA dimension witnessCount hFinrank) :
    Function.Injective D.spectralValue := by
  intro left right hvalue
  apply Subtype.ext
  exact D.eigenvalues_injOn left.2 right.2 hvalue

/-- The selected spectral index has the prescribed witness cardinality. -/
theorem spectralCard
    (D : FiniteDimensionalSymmetricEigenbasisSelectionData
      A hA dimension witnessCount hFinrank) :
    Fintype.card D.SpectralIndex = witnessCount := by
  simpa [SpectralIndex] using D.card_indices

/-- Every selected eigenbasis vector is nonzero. -/
theorem spectralVector_ne_zero
    (D : FiniteDimensionalSymmetricEigenbasisSelectionData
      A hA dimension witnessCount hFinrank)
    (k : D.SpectralIndex) :
    D.spectralVector k ≠ 0 := by
  have hnorm : ‖D.spectralVector k‖ = 1 := by
    exact (hA.eigenvectorBasis hFinrank).orthonormal.norm_eq_one k.1
  intro hzero
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- Every selected vector satisfies the corresponding eigenvalue equation. -/
theorem apply_spectralVector
    (D : FiniteDimensionalSymmetricEigenbasisSelectionData
      A hA dimension witnessCount hFinrank)
    (k : D.SpectralIndex) :
    A (D.spectralVector k) = D.spectralValue k • D.spectralVector k := by
  simpa [spectralVector, spectralValue] using
    hA.apply_eigenvectorBasis hFinrank k.1

/-- A distinct selected eigenbasis family cannot contain more vectors than the
ambient finite dimension. -/
theorem witnessCount_le_dimension
    (D : FiniteDimensionalSymmetricEigenbasisSelectionData
      A hA dimension witnessCount hFinrank) :
    witnessCount ≤ dimension := by
  rw [← D.card_indices]
  simpa using D.indices.card_le_univ

/-- Forget the finite-dimensional eigenbasis origin and retain exactly the
finite distinct-eigenpair package needed for later spectral transport. -/
noncomputable def toFiniteDistinctEigenpairData
    (D : FiniteDimensionalSymmetricEigenbasisSelectionData
      A hA dimension witnessCount hFinrank) :
    FiniteDistinctEigenpairData A witnessCount :=
  { SpectralIndex := D.SpectralIndex
    spectralFintype := inferInstance
    spectralValue := D.spectralValue
    spectralValue_injective := D.spectralValue_injective
    spectralCard := D.spectralCard
    spectralVector := D.spectralVector
    spectralVector_ne_zero := D.spectralVector_ne_zero
    apply_spectralVector := D.apply_spectralVector }

/-- The finite-dimensional selected eigenbasis directly supplies confluent
Cauchy spectral separation under threshold and cardinality hypotheses. -/
theorem confluentCauchyEvaluationLinearIndependent
    (D : FiniteDimensionalSymmetricEigenbasisSelectionData
      A hA dimension witnessCount hFinrank)
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
  D.toFiniteDistinctEigenpairData.confluentCauchyEvaluationLinearIndependent
    value orderCap threshold hValueInjective hValueBelow hSpectralAbove hCard

end FiniteDimensionalSymmetricEigenbasisSelectionData

end

end MathlibAnalytic
end MGAP4D