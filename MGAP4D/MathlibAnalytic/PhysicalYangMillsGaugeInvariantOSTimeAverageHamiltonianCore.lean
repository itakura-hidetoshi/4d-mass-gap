import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSTimeAverageGeneratorDomain
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianLinearPMapClosure
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalCore
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSemigroupSymmetry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- A positive-time average bundled in the canonical right-Hamiltonian core. -/
noncomputable def timeAverageRightHamiltonianDomain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    T.rightHamiltonianLinearPMap.domain :=
  ⟨T.timeAverage h psi, by
    simpa only [T.rightHamiltonianLinearPMap_domain] using
      T.timeAverage_mem_rightGeneratorDomain h psi⟩

@[simp] theorem timeAverageRightHamiltonianDomain_coe
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    (T.timeAverageRightHamiltonianDomain h psi : P.PhysicalHilbert) =
      T.timeAverage h psi :=
  rfl

/-- The infinitesimal generator acts on a time average by the endpoint
finite-difference quotient. -/
theorem rightGenerator_timeAverageRightHamiltonianDomain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    T.rightGenerator (T.timeAverageRightHamiltonianDomain h psi) =
      (h : ℝ)⁻¹ •
        (T.toPhysicalSemigroup.operator h psi - psi) := by
  apply T.hasRightGeneratorValue_unique
    (T.rightGenerator_hasRightGeneratorValue
      (T.timeAverageRightHamiltonianDomain h psi))
  exact T.hasRightGeneratorValue_timeAverage h psi

/-- The right Hamiltonian acts on a time average by the signed semigroup
difference quotient. -/
@[simp] theorem rightHamiltonianLinearPMap_timeAverageRightHamiltonianDomain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    T.rightHamiltonianLinearPMap
        (T.timeAverageRightHamiltonianDomain h psi) =
      T.rightHamiltonianDifferenceQuotient psi h := by
  rw [T.rightHamiltonianLinearPMap_apply, T.rightHamiltonian_apply,
    T.rightGenerator_timeAverageRightHamiltonianDomain]
  simp only [rightHamiltonianDifferenceQuotient]
  module

/-- A symmetric vacuum-fixing semigroup preserves vacuum orthogonality under
Bochner time averaging. -/
theorem timeAverage_mem_vacuumOrthogonal
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (h : NNReal) {psi : P.PhysicalHilbert}
    (hpsi : psi ∈ P.vacuumOrthogonal) :
    T.timeAverage h psi ∈ P.vacuumOrthogonal := by
  rw [P.mem_vacuumOrthogonal_iff] at hpsi ⊢
  have hpsiRight : inner ℝ psi P.vacuum = 0 := by
    rw [real_inner_comm]
    exact hpsi
  unfold timeAverage
  rw [real_inner_smul_right]
  suffices hIntegral : inner ℝ P.vacuum (T.timeIntegral h psi) = 0 by
    rw [hIntegral, mul_zero]
  unfold timeIntegral
  change (innerSL ℝ P.vacuum)
      (∫ s in (0 : ℝ)..(h : ℝ), T.realPhysicalOrbit psi s) = 0
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm
    (innerSL ℝ P.vacuum)
    (T.realPhysicalOrbit_intervalIntegrable psi 0 (h : ℝ))]
  calc
    (∫ s in (0 : ℝ)..(h : ℝ),
        (innerSL ℝ P.vacuum) (T.realPhysicalOrbit psi s)) =
        ∫ _s in (0 : ℝ)..(h : ℝ), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      change inner ℝ P.vacuum
          (T.toPhysicalSemigroup.operator s.toNNReal psi) = 0
      calc
        inner ℝ P.vacuum
            (T.toPhysicalSemigroup.operator s.toNNReal psi) =
            inner ℝ (T.toPhysicalSemigroup.operator s.toNNReal psi)
              P.vacuum := real_inner_comm _ _
        _ = inner ℝ psi
            (T.toPhysicalSemigroup.operator s.toNNReal P.vacuum) :=
          hInnerSymmetric s.toNNReal psi P.vacuum
        _ = inner ℝ psi P.vacuum := by
          rw [T.toPhysicalSemigroup.fixes_vacuum]
        _ = 0 := hpsiRight
    _ = 0 := by simp

/-- If vectors converge strongly while positive averaging widths converge to
zero, their moving time averages converge to the same strong limit. -/
theorem timeAverage_tendsto_of_width_tendsto_zero_of_vector_tendsto
    (T : P.StronglyContinuousPhysicalSemigroup)
    {width : ℕ → NNReal}
    (hwidth_pos : ∀ n, 0 < width n)
    (hwidth : Tendsto width atTop (nhdsWithin 0 (Ioi 0)))
    {psiSeq : ℕ → P.PhysicalHilbert} {psi : P.PhysicalHilbert}
    (hpsi : Tendsto psiSeq atTop (nhds psi)) :
    Tendsto (fun n => T.timeAverage (width n) (psiSeq n))
      atTop (nhds psi) := by
  have hfixed :
      Tendsto (fun n => T.timeAverage (width n) psi)
        atTop (nhds psi) :=
    (T.timeAverage_tendsto_zero psi).comp hwidth
  have hdiff :
      Tendsto
        (fun n => T.timeAverage (width n) (psiSeq n - psi))
        atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    rcases (Metric.tendsto_atTop.1 hpsi epsilon hepsilon) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    rw [dist_zero_right]
    calc
      ‖T.timeAverage (width n) (psiSeq n - psi)‖ ≤
          ‖psiSeq n - psi‖ :=
        T.timeAverage_norm_le (hwidth_pos n) (psiSeq n - psi)
      _ = dist (psiSeq n) psi := by rw [dist_eq_norm]
      _ < epsilon := hN n hn
  have hsum := hdiff.add hfixed
  convert hsum using 1 <;> simp [← T.timeAverage_add]

/-- Moving time averages differ negligibly from the convergent unsmoothed
vectors. -/
theorem timeAverage_sub_tendsto_zero_of_width_tendsto_zero_of_vector_tendsto
    (T : P.StronglyContinuousPhysicalSemigroup)
    {width : ℕ → NNReal}
    (hwidth_pos : ∀ n, 0 < width n)
    (hwidth : Tendsto width atTop (nhdsWithin 0 (Ioi 0)))
    {psiSeq : ℕ → P.PhysicalHilbert} {psi : P.PhysicalHilbert}
    (hpsi : Tendsto psiSeq atTop (nhds psi)) :
    Tendsto
      (fun n => T.timeAverage (width n) (psiSeq n) - psiSeq n)
      atTop (nhds 0) := by
  simpa only [sub_self] using
    (T.timeAverage_tendsto_of_width_tendsto_zero_of_vector_tendsto
      hwidth_pos hwidth hpsi).sub hpsi

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
