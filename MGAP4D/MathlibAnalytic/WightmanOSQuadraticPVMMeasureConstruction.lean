import MGAP4D.MathlibAnalytic.WightmanOSEuclideanTimeSemigroupLaplaceBridge
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Real

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The quadratic PVM weight associated with a Hilbert vector on a measurable
energy set.  The measurable-set proof is intentionally ignored by the value. -/
def ExplicitWightmanOSReconstructedModel.quadraticPVMWeight
    (M : ExplicitWightmanOSReconstructedModel)
    (ψ : M.H) (s : Set ℝ) (_hs : MeasurableSet s) : ENNReal :=
  ENNReal.ofReal (‖M.spectralPVM.projection s ψ‖ ^ 2)

/-- The single missing measure-theoretic law needed to turn the quadratic PVM
weights into genuine scalar spectral measures.

For each Hilbert vector, squared projection norms are countably additive on
pairwise disjoint measurable energy sets.  Empty-set vanishing is already a
consequence of the existing PVM `empty_apply` law and therefore is not repeated
as an independent field. -/
structure ExplicitWightmanOSQuadraticPVMCountableAdditivity
    (M : ExplicitWightmanOSReconstructedModel) where
  iUnion :
    ∀ (ψ : M.H) {f : ℕ → Set ℝ}
      (hf : ∀ i : ℕ, MeasurableSet (f i)),
      Pairwise (Function.onFun Disjoint f) →
        M.quadraticPVMWeight ψ (⋃ i : ℕ, f i)
          (MeasurableSet.iUnion hf) =
        ∑' i : ℕ, M.quadraticPVMWeight ψ (f i) (hf i)

/-- The quadratic PVM weight vanishes on the empty set. -/
theorem quadraticPVMWeight_empty
    (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H) :
    M.quadraticPVMWeight ψ ∅ MeasurableSet.empty = 0 := by
  unfold ExplicitWightmanOSReconstructedModel.quadraticPVMWeight
  rw [M.spectralPVM.empty_apply]
  simp

/-- Construct the scalar spectral measure of a Hilbert vector from quadratic PVM
countable additivity. -/
def ExplicitWightmanOSQuadraticPVMCountableAdditivity.scalarMeasure
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (ψ : M.H) : Measure ℝ :=
  Measure.ofMeasurable
    (M.quadraticPVMWeight ψ)
    (quadraticPVMWeight_empty M ψ)
    (by
      intro f hf hDisjoint
      exact A.iUnion ψ hf hDisjoint)

/-- On every measurable set, the constructed measure has exactly the prescribed
quadratic PVM mass. -/
theorem quadraticPVM_scalarMeasure_apply
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (ψ : M.H) (s : Set ℝ) (hs : MeasurableSet s) :
    A.scalarMeasure ψ s =
      ENNReal.ofReal (‖M.spectralPVM.projection s ψ‖ ^ 2) := by
  unfold ExplicitWightmanOSQuadraticPVMCountableAdditivity.scalarMeasure
  rw [Measure.ofMeasurable_apply s hs]
  rfl

/-- The real-valued mass of the constructed measure is the squared PVM projection
norm.  Finiteness is automatic because the defining ENNReal value is `ofReal`. -/
theorem quadraticPVM_scalarMeasure_real_apply
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (ψ : M.H) (s : Set ℝ) (hs : MeasurableSet s) :
    (A.scalarMeasure ψ).real s =
      ‖M.spectralPVM.projection s ψ‖ ^ 2 := by
  change (A.scalarMeasure ψ s).toReal = _
  rw [quadraticPVM_scalarMeasure_apply A ψ s hs]
  exact ENNReal.toReal_ofReal (sq_nonneg _)

/-- The countable-additivity law therefore constructs the full scalar-measure
upgrade used by the independent OS/Laplace route. -/
def ExplicitWightmanOSQuadraticPVMCountableAdditivity.toCountablyAdditiveScalarMeasure
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M) :
    ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M :=
  { scalarMeasure := A.scalarMeasure
    scalarMeasure_real_eq_projectionNormSq := by
      intro ψ s hs
      exact quadraticPVM_scalarMeasure_real_apply A ψ s hs }

/-- The corresponding coherent vector-indexed scalar spectral realization is now
constructed rather than separately assumed. -/
def ExplicitWightmanOSQuadraticPVMCountableAdditivity.toScalarSpectralRealization
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M) :
    ExplicitWightmanOSScalarSpectralMeasureRealization M :=
  A.toCountablyAdditiveScalarMeasure.toScalarSpectralRealization

/-- A nonzero singleton projection yields positive mass in the measure constructed
from the quadratic countable-additivity law. -/
theorem quadraticPVM_scalarMeasure_singleton_pos
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (ψ : M.H) (E : ℝ)
    (hProjection : M.spectralPVM.projection ({E} : Set ℝ) ψ ≠ 0) :
    0 < (A.scalarMeasure ψ).real ({E} : Set ℝ) := by
  rw [quadraticPVM_scalarMeasure_real_apply A ψ ({E} : Set ℝ)
    (MeasurableSet.singleton E)]
  exact sq_pos_of_pos (norm_pos_iff.mpr hProjection)

/-- Hamiltonian mass gap with the scalar spectral measure now constructed from
one explicit quadratic PVM countable-additivity law. -/
theorem euclidean_quadratic_pvm_semigroup_clustering_mass_gap
    (C : EuclideanYangMillsConnectedObservableCore)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity C.explicitModel)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel)
    (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
    (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      C.explicitModel A.toScalarSpectralRealization T)
    (X : EuclideanYangMillsExponentialClusteringEstimate C) :
    HasHamiltonianMassGap
      C.explicitModel.hamiltonianEnergySpectrum exactGapValueReal := by
  exact euclidean_semigroup_spectral_formula_clustering_mass_gap
    C A.toCountablyAdditiveScalarMeasure T E S X

/-- Exact physical gap through the constructed scalar spectral measures. -/
theorem euclidean_quadratic_pvm_semigroup_clustering_exact_gap
    (C : EuclideanYangMillsConnectedObservableCore)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity C.explicitModel)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel)
    (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
    (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      C.explicitModel A.toScalarSpectralRealization T)
    (X : EuclideanYangMillsExponentialClusteringEstimate C)
    (hExactSpectrum :
      exactGapValueReal ∈ C.explicitModel.hamiltonianEnergySpectrum) :
    let L :=
      euclideanYangMillsOSLaplaceSemigroupIdentificationOfMatrixCoefficients E S
    0 < exactGapValueReal ∧
      ((C.assemble L.toOSSpectralLaplace X).vacuumOrthogonalSpectrum
        ((C.assemble L.toOSSpectralLaplace X).exactEnergy
          hExactSpectrum)).restrictedSpectrum ⊆
        Set.Ici exactGapValueReal ∧
      sInf
        ((C.assemble L.toOSSpectralLaplace X).vacuumOrthogonalSpectrum
          ((C.assemble L.toOSSpectralLaplace X).exactEnergy
            hExactSpectrum)).restrictedSpectrum =
        exactGapValueReal := by
  exact euclidean_semigroup_spectral_formula_clustering_exact_gap
    C A.toCountablyAdditiveScalarMeasure T E S X hExactSpectrum

end

end MathlibAnalytic
end MGAP4D
