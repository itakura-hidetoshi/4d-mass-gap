import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateBoundaryProjection
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Representative-level ground-state transform `f / Ω`.  Total inversion is
harmless because the canonical top vacuum is strictly positive Haar-a.e. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumFunction
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  f A /
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta).1 A)

/-- The representative `f / Ω` belongs to the vacuum-weighted `L²` space.
The key cancellation is the a.e. identity `Ω² (f / Ω)² = f²`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumFunction_memLp
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumFunction
        H N hN beta hbeta f)
      2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  let omega : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun A => (Ω.1 : Lp ℝ 2 μ) A
  let u : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun A => f A / omega A
  let rho : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ENNReal :=
    fun A => ENNReal.ofReal (omega A ^ 2)
  have huStrongμ : AEStronglyMeasurable u μ := by
    exact (Lp.aestronglyMeasurable f).div₀
      (Lp.aestronglyMeasurable (Ω.1 : Lp ℝ 2 μ))
  have hrhoAE : AEMeasurable rho μ := by
    exact ((Lp.aestronglyMeasurable (Ω.1 : Lp ℝ 2 μ)).pow 2).aemeasurable.ennreal_ofReal
  have hrhoTop : ∀ᵐ A ∂μ, rho A < (⊤ : ENNReal) := by
    filter_upwards with A
    simp [rho]
  have hνac : μ.withDensity rho ≪ μ := withDensity_absolutelyContinuous _ _
  have huStrongν : AEStronglyMeasurable u (μ.withDensity rho) :=
    huStrongμ.mono_ac hνac
  have hΩpos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_pos
      H N hN beta hbeta
  have huSqInt : Integrable (fun A => u A ^ 2) (μ.withDensity rho) := by
    rw [integrable_withDensity_iff_integrable_smul₀' hrhoAE hrhoTop]
    apply (Lp.memLp f).integrable_sq.congr
    filter_upwards [hΩpos] with A hpos
    have hne : omega A ≠ 0 := by
      dsimp [omega, Ω]
      exact ne_of_gt hpos
    simp only [smul_eq_mul]
    dsimp [rho, u]
    rw [ENNReal.toReal_ofReal (sq_nonneg (omega A))]
    field_simp [hne]
  change MemLp
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumFunction
      H N hN beta hbeta f) 2 (μ.withDensity rho)
  have huMem : MemLp u 2 (μ.withDensity rho) :=
    (memLp_two_iff_integrable_sq huStrongν).2 huSqInt
  simpa [u, omega, Ω,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumFunction,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure, rho] using huMem

/-- The ground-state transform as a genuine vacuum-weighted `L²` vector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumFunction_memLp
    H N hN beta hbeta f).toLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumFunction
        H N hN beta hbeta f)

/-- The `L²` transform has the expected representative. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_coeFn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
        H N hN beta hbeta f =ᵐ[
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
            H N hN beta hbeta]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumFunction
        H N hN beta hbeta f := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumFunction_memLp
      H N hN beta hbeta f).coeFn_toLp

/-- The weighted ground-state transform preserves the squared `L²` norm. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_norm_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
        H N hN beta hbeta f‖ ^ 2 = ‖f‖ ^ 2 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  let omega : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun A => (Ω.1 : Lp ℝ 2 μ) A
  let u : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun A => f A / omega A
  let rho : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ENNReal :=
    fun A => ENNReal.ofReal (omega A ^ 2)
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
    H N hN beta hbeta f
  have hUrep :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_coeFn
      H N hN beta hbeta f
  have hrhoAE : AEMeasurable rho μ := by
    exact ((Lp.aestronglyMeasurable (Ω.1 : Lp ℝ 2 μ)).pow 2).aemeasurable.ennreal_ofReal
  have hrhoTop : ∀ᵐ A ∂μ, rho A < (⊤ : ENNReal) := by
    filter_upwards with A
    simp [rho]
  have hΩpos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_pos
      H N hN beta hbeta
  have hInt :
      (∫ A, ‖U A‖ ^ 2 ∂(μ.withDensity rho)) = ∫ A, ‖f A‖ ^ 2 ∂μ := by
    calc
      (∫ A, ‖U A‖ ^ 2 ∂(μ.withDensity rho)) =
          ∫ A, u A ^ 2 ∂(μ.withDensity rho) := by
        apply integral_congr_ae
        have hrep : U =ᵐ[μ.withDensity rho] u := by
          simpa [U, u, omega, Ω,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure, rho,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumFunction] using hUrep
        filter_upwards [hrep] with A hA
        rw [hA]
        simp [Real.norm_eq_abs, sq_abs]
      _ = ∫ A, (rho A).toReal • (u A ^ 2) ∂μ := by
        exact integral_withDensity_eq_integral_toReal_smul₀ hrhoAE hrhoTop _
      _ = ∫ A, ‖f A‖ ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hΩpos] with A hpos
        have hne : omega A ≠ 0 := by
          dsimp [omega, Ω]
          exact ne_of_gt hpos
        simp only [smul_eq_mul]
        dsimp [rho, u]
        rw [ENNReal.toReal_ofReal (sq_nonneg (omega A))]
        field_simp [hne]
        simp [Real.norm_eq_abs, sq_abs]
  rw [realL2_norm_sq_eq_integral_norm_sq U,
    realL2_norm_sq_eq_integral_norm_sq f]
  change (∫ A, ‖U A‖ ^ 2 ∂(μ.withDensity rho)) = ∫ A, ‖f A‖ ^ 2 ∂μ
  exact hInt

end

end MathlibAnalytic
end MGAP4D