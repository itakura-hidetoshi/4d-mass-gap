import MGAP4D.MathlibAnalytic.WightmanOSPVMPhysicalSemigroupRightHamiltonianValue
import MGAP4D.MathlibAnalytic.ExplicitWightmanOSScalarSupportToPVMOpenSupport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace

noncomputable section

/-- A positive lower bound on the physical vacuum-orthogonal spectral support
forces the ambient reconstructed PVM to vanish on the negative energy half-line.

Indeed, a hypothetical nonzero vector `P((−∞,0)) ψ` lies in `Ω⊥` because the
negative half-line is disjoint from the vacuum singleton.  Its quadratic scalar
spectral measure has positive mass on the same negative half-line, hence that
open set meets its support.  This contradicts the positive support lower bound. -/
noncomputable def
    ExplicitWightmanOSCanonicalSpectralSupportBridge.toPositiveSpectralSupport
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (B : ExplicitWightmanOSCanonicalSpectralSupportBridge
      M A.toScalarSpectralRealization)
    {m : ℝ} (hGap : M.HasMassGap m) :
    ExplicitWightmanOSPositiveSpectralSupport M where
  negativeProjection_zero := by
    intro ψ
    let s : Set ℝ := Set.Iio (0 : ℝ)
    let y : M.H := M.spectralPVM.projection s ψ
    change y = 0
    by_contra hy
    have hsMeasurable : MeasurableSet s := by
      simpa [s] using (measurableSet_Iio : MeasurableSet (Set.Iio (0 : ℝ)))
    have hDisjoint : Disjoint ({0} : Set ℝ) s := by
      rw [Set.disjoint_left]
      intro energy henergyZero henergyNeg
      have hzero : energy = 0 := by simpa using henergyZero
      have hneg : energy < 0 := by simpa [s] using henergyNeg
      linarith
    have hZeroProjection :
        M.spectralPVM.projection ({0} : Set ℝ) y = 0 := by
      dsimp [y]
      exact M.spectralPVM.disjoint_projection_comp_apply_eq_zero hDisjoint ψ
    have hyOrthogonal : y ∈ M.vacuumOrthogonal := by
      rw [explicit_wightman_os_mem_vacuumOrthogonal_iff]
      calc
        inner ℝ M.vacuum y =
            inner ℝ
              (M.spectralPVM.projection ({0} : Set ℝ) M.vacuum) y := by
          rw [M.vacuumSpectralProjection]
        _ = inner ℝ M.vacuum
              (M.spectralPVM.projection ({0} : Set ℝ) y) :=
          M.spectralPVM.selfAdjoint ({0} : Set ℝ) M.vacuum y
        _ = 0 := by rw [hZeroProjection]; simp
    let yOrthogonal : M.VacuumOrthogonalHilbert := ⟨y, hyOrthogonal⟩
    have hIdempotent : M.spectralPVM.projection s y = y := by
      dsimp [y]
      exact M.spectralPVM.idempotent s ψ
    have hMassPositive : 0 < A.scalarMeasure y s := by
      rw [quadraticPVM_scalarMeasure_apply A y s hsMeasurable, hIdempotent]
      exact ENNReal.ofReal_pos.mpr
        (sq_pos_of_pos (norm_pos_iff.mpr hy))
    obtain ⟨energy, henergyS, henergySupport⟩ :=
      Measure.nonempty_inter_support_of_pos hMassPositive
    have henergyCanonical :
        energy ∈ M.canonicalVacuumOrthogonalSpectralSupport
          A.toScalarSpectralRealization := by
      rw [mem_canonical_vacuum_orthogonal_spectralSupport_iff]
      exact ⟨yOrthogonal, henergySupport⟩
    have hLower : m ≤ energy :=
      (canonical_vacuum_orthogonal_spectralSupport_lower_bound B hGap)
        henergyCanonical
    have hNegative : energy < 0 := by simpa [s] using henergyS
    linarith [hGap.1]

/-- Pure PVM open-support data generates the same ambient positive spectral
support after passing through the quadratic scalar realization. -/
noncomputable def
    ExplicitWightmanOSCanonicalPVMOpenSupportBridge.toPositiveSpectralSupport
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M)
    {m : ℝ} (hGap : M.HasMassGap m) :
    ExplicitWightmanOSPositiveSpectralSupport M :=
  (B.toCanonicalSpectralSupportBridge
      A.toFullScalarSpectralMeasureRealization).toPositiveSpectralSupport
    A hGap

end

end MathlibAnalytic
end MGAP4D
