import MGAP4D.MathlibAnalytic.WightmanOSQuadraticPVMMeasureConstruction
import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianSpectralSupport
import Mathlib.MeasureTheory.Measure.Support

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A full scalar spectral-measure realization records the quadratic PVM formula
on every measurable energy set, not only on singletons. -/
structure ExplicitWightmanOSFullScalarSpectralMeasureRealization
    (M : ExplicitWightmanOSReconstructedModel) where
  scalarMeasure : M.H → Measure ℝ
  measurableMass_eq_projectionNormSq :
    ∀ (ψ : M.H) (s : Set ℝ), MeasurableSet s →
      scalarMeasure ψ s =
        ENNReal.ofReal (‖M.spectralPVM.projection s ψ‖ ^ 2)

/-- Forgetting the full measurable-set formula yields the previous singleton
scalar spectral realization. -/
def ExplicitWightmanOSFullScalarSpectralMeasureRealization.toScalarSpectralRealization
    {M : ExplicitWightmanOSReconstructedModel}
    (F : ExplicitWightmanOSFullScalarSpectralMeasureRealization M) :
    ExplicitWightmanOSScalarSpectralMeasureRealization M :=
  { scalarMeasure := F.scalarMeasure
    singletonMass_eq_squaredProjectionNorm := by
      intro ψ E
      change (F.scalarMeasure ψ ({E} : Set ℝ)).toReal = _
      rw [F.measurableMass_eq_projectionNormSq ψ ({E} : Set ℝ)
        (MeasurableSet.singleton E)]
      exact ENNReal.toReal_ofReal (sq_nonneg _) }

/-- Quadratic PVM countable additivity constructs the full realization. -/
def ExplicitWightmanOSQuadraticPVMCountableAdditivity.toFullScalarSpectralMeasureRealization
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M) :
    ExplicitWightmanOSFullScalarSpectralMeasureRealization M :=
  { scalarMeasure := A.scalarMeasure
    measurableMass_eq_projectionNormSq := by
      intro ψ s hs
      exact quadraticPVM_scalarMeasure_apply A ψ s hs }

/-- A point belongs to a scalar spectral measure's support exactly when every
open neighborhood has nonzero PVM projection on the vector. -/
theorem full_scalar_spectral_measure_mem_support_iff
    {M : ExplicitWightmanOSReconstructedModel}
    (F : ExplicitWightmanOSFullScalarSpectralMeasureRealization M)
    (ψ : M.H) (E : ℝ) :
    E ∈ (F.scalarMeasure ψ).support ↔
      ∀ U : Set ℝ, E ∈ U → IsOpen U →
        M.spectralPVM.projection U ψ ≠ 0 := by
  rw [Measure.support_eq_forall_isOpen]
  constructor
  · intro h U hEU hU hProjectionZero
    have hPositive : 0 < F.scalarMeasure ψ U := h U hEU hU
    rw [F.measurableMass_eq_projectionNormSq ψ U hU.measurableSet]
      at hPositive
    simpa [hProjectionZero] using hPositive
  · intro h U hEU hU
    rw [F.measurableMass_eq_projectionNormSq ψ U hU.measurableSet]
    exact ENNReal.ofReal_pos.mpr
      (sq_pos_of_pos (norm_pos_iff.mpr (h U hEU hU)))

/-- Pure PVM description of the spectral support seen by the physical
vacuum-orthogonal sector. -/
def ExplicitWightmanOSReconstructedModel.vacuumOrthogonalPVMOpenSupport
    (M : ExplicitWightmanOSReconstructedModel) : Set ℝ :=
  {E | ∃ ψ : M.VacuumOrthogonalHilbert,
    ∀ U : Set ℝ, E ∈ U → IsOpen U →
      M.spectralPVM.projection U (ψ : M.H) ≠ 0}

/-- The union of scalar-measure supports is exactly the open-neighborhood PVM
support. -/
theorem full_scalar_vacuumOrthogonal_support_eq_pvmOpenSupport
    {M : ExplicitWightmanOSReconstructedModel}
    (F : ExplicitWightmanOSFullScalarSpectralMeasureRealization M) :
    M.canonicalVacuumOrthogonalSpectralSupport
        F.toScalarSpectralRealization =
      M.vacuumOrthogonalPVMOpenSupport := by
  ext E
  simp only [ExplicitWightmanOSReconstructedModel.canonicalVacuumOrthogonalSpectralSupport,
    ExplicitWightmanOSReconstructedModel.vacuumOrthogonalPVMOpenSupport,
    Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ψ, hψ⟩
    exact ⟨ψ,
      (full_scalar_spectral_measure_mem_support_iff
        F (ψ : M.H) E).mp hψ⟩
  · rintro ⟨ψ, hψ⟩
    exact ⟨ψ,
      (full_scalar_spectral_measure_mem_support_iff
        F (ψ : M.H) E).mpr hψ⟩

/-- Operator/PVM identification input after the measure-support layer has been
discharged: only equality of the pure open-neighborhood PVM support with the
physical non-vacuum spectrum remains. -/
structure ExplicitWightmanOSCanonicalPVMOpenSupportBridge
    (M : ExplicitWightmanOSReconstructedModel) extends
      ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge M where
  pvmOpenSupport_eq_restrictedSpectrum :
    M.vacuumOrthogonalPVMOpenSupport = restrictedSpectrum

/-- A pure PVM support bridge automatically supplies the scalar-measure support
bridge for every full scalar realization. -/
def ExplicitWightmanOSCanonicalPVMOpenSupportBridge.toCanonicalSpectralSupportBridge
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M)
    (F : ExplicitWightmanOSFullScalarSpectralMeasureRealization M) :
    ExplicitWightmanOSCanonicalSpectralSupportBridge
      M F.toScalarSpectralRealization :=
  { toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge :=
      B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge
    spectralSupport_eq_restrictedSpectrum := by
      rw [full_scalar_vacuumOrthogonal_support_eq_pvmOpenSupport F]
      exact B.pvmOpenSupport_eq_restrictedSpectrum }

/-- Euclidean clustering bounds the full PVM open support, including continuous
spectral support. -/
theorem euclidean_clustering_pvmOpenSupport_lower_bound
    (C : EuclideanYangMillsConnectedObservableCore)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity C.explicitModel)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel)
    (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
    (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      C.explicitModel A.toScalarSpectralRealization T)
    (X : EuclideanYangMillsExponentialClusteringEstimate C)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge C.explicitModel) :
    0 < exactGapValueReal ∧
      C.explicitModel.vacuumOrthogonalPVMOpenSupport ⊆
        Set.Ici exactGapValueReal := by
  have hGap : C.explicitModel.HasMassGap exactGapValueReal :=
    euclidean_quadratic_pvm_semigroup_clustering_mass_gap C A T E S X
  rw [B.pvmOpenSupport_eq_restrictedSpectrum]
  exact ⟨hGap.1,
    vacuum_orthogonal_restrictedSpectrum_subset_Ici
      B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge.toExplicitWightmanOSVacuumOrthogonalSpectrumBridge
      hGap⟩

end

end MathlibAnalytic
end MGAP4D
