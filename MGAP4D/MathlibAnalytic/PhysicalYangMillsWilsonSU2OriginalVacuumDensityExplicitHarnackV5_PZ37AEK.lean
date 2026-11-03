import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTransferExplicitKernelFloorV5_PZ37AEJ
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumKernelHarnack
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEK — original continuous vacuum quantitative global Harnack

The genuine Wilson kernel has the explicit finite-volume uniform interval
  k = exp (-beta * actionBudget H) <= K(A,B) <= 1.
The true continuous Perron vacuum Omega is represented by the original
nonnegative normalized physical top eigenvector. Its exact pointwise
Perron equation and original normalized Haar measure imply
  k * Omega(A) <= Omega(B) for all original spatial boundaries A,B.
The L2 norm-one identity then converts global comparability into explicit
absolute pointwise vacuum bounds.

This module adds genuine original SU(2) joint sqrt-density bounds, without
proxy densities, numerical net hypotheses or continuum mass-gap claims.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AEK_group (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2PZ37AEK_compact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2PZ37AEK_countable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2PZ37AEK_measurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2PZ37AEK_borel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4Q2PZ37AEK_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Genuine global pointwise comparability of the original continuous
Perron vacuum by the literal positive Wilson action floor. -/
theorem p4Q2PZ37AEK_originalContinuousVacuum_globalKernelRatio
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H beta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta B ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta C := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let V := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
  let Omega := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H N hN beta hbeta
  let lambda := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  let k := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H beta
  have hk : 0 ≤ k :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos
      H beta).le
  have hlam : 0 < lambda :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta
  have hNonneg :
      ∀ᵐ A ∂μ, 0 ≤ V.1 A := by
    simpa only [V, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
        H N hN beta hbeta
  have hInt (D : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
      Integrable (fun A => V.1 A * K A D) μ := by
    simpa only [V, K, μ] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
        H N hN beta hbeta
        ((V : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
          Lp ℝ 2 μ) D
  have hKernel (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
      k * K A B ≤ K A C := by
    calc
      k * K A B ≤ k * 1 :=
        mul_le_mul_of_nonneg_left
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_le_one
            H N hN beta hbeta A B) hk
      _ = k := mul_one k
      _ ≤ K A C :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_kernel
          H N hN beta hbeta A C
  have hPointwise : ∀ᵐ A ∂μ, k * (V.1 A * K A B) ≤ V.1 A * K A C := by
    filter_upwards [hNonneg] with A hA
    calc
      k * (V.1 A * K A B) = V.1 A * (k * K A B) := by ring
      _ ≤ V.1 A * K A C :=
        mul_le_mul_of_nonneg_left (hKernel A) hA
  have hIntegral :
      k * (∫ A, V.1 A * K A B ∂μ) ≤
        ∫ A, V.1 A * K A C ∂μ := by
    calc
      k * (∫ A, V.1 A * K A B ∂μ) =
          ∫ A, k * (V.1 A * K A B) ∂μ :=
        (integral_const_mul k _).symm
      _ ≤ ∫ A, V.1 A * K A C ∂μ :=
        integral_mono_ae ((hInt B).const_mul k) (hInt C) hPointwise
  have hPerron (D : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
      lambda * Omega D = ∫ A, V.1 A * K A D ∂μ := by
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_topNorm_mul_eq_integral_kernel
      H N hN beta hbeta D
  have hScaled : lambda * (k * Omega B) ≤ lambda * Omega C := by
    calc
      lambda * (k * Omega B) = k * (lambda * Omega B) := by ring
      _ = k * (∫ A, V.1 A * K A B ∂μ) := by rw [hPerron B]
      _ ≤ ∫ A, V.1 A * K A C ∂μ := hIntegral
      _ = lambda * Omega C := (hPerron C).symm
  exact (mul_le_mul_left hlam).mp hScaled

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEK_originalContinuousVacuum_globalKernelRatio
