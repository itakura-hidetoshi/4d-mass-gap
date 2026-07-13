import MGAP4D.MathlibAnalytic.WightmanOSPVMPositiveSemigroupStrongLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

/-- Simple-function PVM integration on the restricted vacuum-orthogonal sector
agrees, after inclusion, with ambient simple-function PVM integration. -/
theorem ExplicitWightmanOSReconstructedModel.pvmSimpleFuncSpectralIntegralOperator_vacuumOrthogonal_coe
    (M : ExplicitWightmanOSReconstructedModel)
    (f : SimpleFunc ℝ ℝ)
    (ψ : M.VacuumOrthogonalHilbert) :
    ((pvmSimpleFuncSpectralIntegralOperator
          M.vacuumOrthogonalSpectralPVM f ψ :
        M.VacuumOrthogonalHilbert) : M.H) =
      pvmSimpleFuncSpectralIntegralOperator
        M.spectralPVM f (ψ : M.H) := by
  rw [pvmSimpleFuncSpectralIntegralOperator_apply,
    pvmSimpleFuncSpectralIntegralOperator_apply]
  unfold pvmFiniteSimpleSpectralIntegral
  change M.vacuumOrthogonal.subtype
      (∑ c, (c : ℝ) •
        M.vacuumOrthogonalSpectralPVM.projection
          (pvmSimpleFuncFiber f c) ψ) =
    ∑ c, (c : ℝ) •
      M.spectralPVM.projection (pvmSimpleFuncFiber f c) (ψ : M.H)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [map_smul]
  rfl

/-- Completed bounded-Borel PVM integration on `Ω⊥` is exactly the ambient
completed integral after inclusion into the reconstructed Hilbert space. -/
theorem ExplicitWightmanOSReconstructedModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_coe
    (M : ExplicitWightmanOSReconstructedModel)
    (F : PVMBoundedBorelRealFunction)
    (ψ : M.VacuumOrthogonalHilbert) :
    ((M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral F ψ :
        M.VacuumOrthogonalHilbert) : M.H) =
      pvmBoundedBorelSpectralIntegralOperator
        M.spectralPVM F (ψ : M.H) := by
  let A := explicitBoundedBorelCanonicalSimpleUniformApproximation F
  have hSubtype :=
    A.tendsto_completedOperator_apply M.vacuumOrthogonalSpectralPVM ψ
  have hSubtypeAmbient :
      Tendsto
        (fun n : ℕ =>
          ((pvmSimpleFuncSpectralIntegralOperator
              M.vacuumOrthogonalSpectralPVM (A.simple n) ψ :
            M.VacuumOrthogonalHilbert) : M.H))
        atTop
        (𝓝 (((A.completedOperator M.vacuumOrthogonalSpectralPVM ψ :
            M.VacuumOrthogonalHilbert) : M.H))) :=
    (continuous_subtype_val.tendsto _).comp hSubtype
  have hAmbient :=
    A.tendsto_completedOperator_apply M.spectralPVM (ψ : M.H)
  have hTerm : ∀ n : ℕ,
      ((pvmSimpleFuncSpectralIntegralOperator
          M.vacuumOrthogonalSpectralPVM (A.simple n) ψ :
        M.VacuumOrthogonalHilbert) : M.H) =
        pvmSimpleFuncSpectralIntegralOperator
          M.spectralPVM (A.simple n) (ψ : M.H) := by
    intro n
    exact M.pvmSimpleFuncSpectralIntegralOperator_vacuumOrthogonal_coe
      (A.simple n) ψ
  have hCompleted :
      ((A.completedOperator M.vacuumOrthogonalSpectralPVM ψ :
          M.VacuumOrthogonalHilbert) : M.H) =
        A.completedOperator M.spectralPVM (ψ : M.H) := by
    apply tendsto_nhds_unique hSubtypeAmbient
    simpa only [hTerm] using hAmbient
  simpa [A,
    ExplicitWightmanOSReconstructedModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral,
    pvmBoundedBorelSpectralIntegralOperator] using hCompleted

/-- The physical nonnegative-energy support property for the reconstructed PVM.
It is deliberately isolated from the analytic strong-limit theorem. -/
structure ExplicitWightmanOSPositiveSpectralSupport
    (M : ExplicitWightmanOSReconstructedModel) where
  negativeProjection_zero :
    ∀ ψ : M.H,
      M.spectralPVM.projection (Set.Iio (0 : ℝ)) ψ = 0

/-- Positive spectral support makes the nonnegative half-line projection the
identity. -/
theorem ExplicitWightmanOSPositiveSpectralSupport.projection_Ici_zero_apply
    {M : ExplicitWightmanOSReconstructedModel}
    (S : ExplicitWightmanOSPositiveSpectralSupport M)
    (ψ : M.H) :
    M.spectralPVM.projection (Set.Ici (0 : ℝ)) ψ = ψ := by
  have hDisjoint :
      Disjoint (Set.Iio (0 : ℝ)) (Set.Ici (0 : ℝ)) := by
    rw [Set.disjoint_left]
    intro energy hneg hnonneg
    have hlt : energy < 0 := by simpa using hneg
    have hge : 0 ≤ energy := by simpa using hnonneg
    exact (not_lt_of_ge hge) hlt
  have hUnion :
      Set.Iio (0 : ℝ) ∪ Set.Ici (0 : ℝ) = Set.univ := by
    ext energy
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Ici, Set.mem_univ,
      iff_true]
    exact lt_or_ge energy 0
  have hAdd :=
    M.spectralPVM.disjoint_additive
      (Set.Iio (0 : ℝ)) (Set.Ici (0 : ℝ)) hDisjoint ψ
  rw [hUnion, M.spectralPVM.univ_apply,
    S.negativeProjection_zero ψ, zero_add] at hAdd
  exact hAdd.symm

/-- Under positive spectral support, restricting a bounded multiplier to
nonnegative energy does not change its ambient completed PVM integral. -/
theorem ExplicitWightmanOSPositiveSpectralSupport.ambientIntegral_positiveEnergyRestrict_apply
    {M : ExplicitWightmanOSReconstructedModel}
    (S : ExplicitWightmanOSPositiveSpectralSupport M)
    (F : PVMBoundedBorelRealFunction)
    (ψ : M.H) :
    pvmBoundedBorelSpectralIntegralOperator M.spectralPVM
        (pvmPositiveEnergyRestrict F) ψ =
      pvmBoundedBorelSpectralIntegralOperator M.spectralPVM F ψ := by
  rw [pvmPositiveEnergyRestrict,
    pvmBoundedBorelSpectralIntegralOperator_restrict_apply]
  rw [S.projection_Ici_zero_apply]

/-- The same positive-support identity on the canonical vacuum-orthogonal
completed integral. -/
theorem ExplicitWightmanOSPositiveSpectralSupport.canonicalIntegral_positiveEnergyRestrict_apply
    {M : ExplicitWightmanOSReconstructedModel}
    (S : ExplicitWightmanOSPositiveSpectralSupport M)
    (F : PVMBoundedBorelRealFunction)
    (ψ : M.VacuumOrthogonalHilbert) :
    M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
        (pvmPositiveEnergyRestrict F) ψ =
      M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral F ψ := by
  apply Subtype.ext
  change
    ((M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
        (pvmPositiveEnergyRestrict F) ψ :
      M.VacuumOrthogonalHilbert) : M.H) =
      ((M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral F ψ :
        M.VacuumOrthogonalHilbert) : M.H)
  rw [M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_coe,
    M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_coe]
  exact S.ambientIntegral_positiveEnergyRestrict_apply F (ψ : M.H)

/-- The remaining physical spectral-action data after the scalar and PVM
analysis have been constructed.  The quotient formula is stated in the ambient
Hilbert space, where PR #813 supplies the actual strong limit. -/
structure EuclideanYangMillsOSPhysicalPositiveSemigroupSpectralAction
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) where
  quadraticPVMCountableAdditivity :
    ExplicitWightmanOSQuadraticPVMCountableAdditivity M.toExplicitModel
  positiveSpectralSupport :
    ExplicitWightmanOSPositiveSpectralSupport M.toExplicitModel
  rightDifferenceQuotient_eq_ambientSpectralIntegral :
    ∀ (t : ℝ), 0 < t →
      ∀ (f h : PVMBoundedBorelRealFunction)
        (hCoordinate : ∀ energy : ℝ,
          h.toFun energy = energy * f.toFun energy)
        (ψ : M.toExplicitModel.VacuumOrthogonalHilbert),
      T.rightHamiltonianDifferenceQuotient
          (((M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
              f ψ : M.toExplicitModel.VacuumOrthogonalHilbert) :
            M.toExplicitModel.H)) t =
        pvmBoundedBorelSpectralIntegralOperator
          M.toExplicitModel.spectralPVM
          (pvmPositiveSemigroupDifferenceQuotientMultiplier
            t f h hCoordinate)
          (ψ : M.toExplicitModel.H)

/-- The actual ambient strong-limit theorem, the ambient/restricted completion
identity, positive spectral support, and the semigroup spectral-action formula
construct the physical spectral right-Hamiltonian value package. -/
noncomputable def EuclideanYangMillsOSPhysicalPositiveSemigroupSpectralAction.toSpectralRightHamiltonianValue
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (D : EuclideanYangMillsOSPhysicalPositiveSemigroupSpectralAction T) :
    EuclideanYangMillsOSPhysicalSpectralRightHamiltonianValue T where
  spectralIntegral_hasRightHamiltonianValue := by
    intro f h hCoordinate ψ
    unfold EuclideanYangMillsOSPhysicalTimeTranslation.HasRightHamiltonianValue
    have hAmbientLimit :=
      pvmPositiveSemigroupDifferenceQuotientSpectralIntegral_tendsto
        D.quadraticPVMCountableAdditivity f h hCoordinate
        (ψ : M.toExplicitModel.H)
    have hTarget :
        pvmBoundedBorelSpectralIntegralOperator M.toExplicitModel.spectralPVM
            (pvmPositiveEnergyRestrict h) (ψ : M.toExplicitModel.H) =
          (((M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
              h ψ : M.toExplicitModel.VacuumOrthogonalHilbert) :
            M.toExplicitModel.H)) := by
      calc
        pvmBoundedBorelSpectralIntegralOperator M.toExplicitModel.spectralPVM
            (pvmPositiveEnergyRestrict h) (ψ : M.toExplicitModel.H) =
          pvmBoundedBorelSpectralIntegralOperator M.toExplicitModel.spectralPVM
            h (ψ : M.toExplicitModel.H) :=
          D.positiveSpectralSupport.ambientIntegral_positiveEnergyRestrict_apply
            h (ψ : M.toExplicitModel.H)
        _ =
          (((M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
              h ψ : M.toExplicitModel.VacuumOrthogonalHilbert) :
            M.toExplicitModel.H)) :=
          (M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_coe
            h ψ).symm
    have hLimit :
        Tendsto
          (fun t : ℝ =>
            pvmBoundedBorelSpectralIntegralOperator
              M.toExplicitModel.spectralPVM
              (pvmPositiveSemigroupDifferenceQuotientMultiplier
                t f h hCoordinate)
              (ψ : M.toExplicitModel.H))
          (nhdsWithin 0 (Set.Ioi 0))
          (𝓝 (((M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
              h ψ : M.toExplicitModel.VacuumOrthogonalHilbert) :
            M.toExplicitModel.H))) := by
      simpa only [hTarget] using hAmbientLimit
    have hEventually :
        (fun t : ℝ =>
          T.rightHamiltonianDifferenceQuotient
            (((M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
                f ψ : M.toExplicitModel.VacuumOrthogonalHilbert) :
              M.toExplicitModel.H)) t) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun t : ℝ =>
          pvmBoundedBorelSpectralIntegralOperator
            M.toExplicitModel.spectralPVM
            (pvmPositiveSemigroupDifferenceQuotientMultiplier
              t f h hCoordinate)
            (ψ : M.toExplicitModel.H)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact D.rightDifferenceQuotient_eq_ambientSpectralIntegral
        t (by simpa using ht) f h hCoordinate ψ
    exact hLimit.congr' hEventually.symm

/-- Downstream constructor: the physical generator and OS exchange now consume
only the minimal positive-semigroup spectral-action package. -/
noncomputable def EuclideanYangMillsOSPhysicalPositiveSemigroupSpectralAction.toCoordinateGraph
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (D : EuclideanYangMillsOSPhysicalPositiveSemigroupSpectralAction T)
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (hExchange : T.ReflectionTimeTranslationExchange) :
    ExplicitWightmanOSCanonicalRestrictedPVMCoordinateGraph M.toExplicitModel :=
  D.toSpectralRightHamiltonianValue
    |>.toCoordinateGraphOfReflectionTimeTranslationExchange G hExchange

end

end MathlibAnalytic
end MGAP4D
