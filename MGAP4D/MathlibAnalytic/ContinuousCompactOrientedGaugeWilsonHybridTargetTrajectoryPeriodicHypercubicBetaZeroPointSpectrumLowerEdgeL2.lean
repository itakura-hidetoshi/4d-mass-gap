import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRayleighInfimumAttainmentL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

/-- The real point spectrum of the native finite-volume heat-bath Hamiltonian:
`lam` belongs when a nonzero Gibbs `L²` vector satisfies `H_HB f = lam • f`. -/
def ContinuousCompactOrientedGaugeWilsonSystem.heatBathPointSpectrumL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) : Set ℝ :=
  {lam | ∃ f : Lp ℝ 2 C.gibbsMeasure,
    f ≠ 0 ∧ C.heatBathHamiltonianL2 f = lam • f}

/-- The normalized Gibbs vacuum supplies the zero point-spectrum value for every
continuous compact oriented Wilson system. -/
theorem continuous_compact_oriented_zero_mem_heatBathPointSpectrumL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    (0 : ℝ) ∈ C.heatBathPointSpectrumL2 := by
  change ∃ f : Lp ℝ 2 C.gibbsMeasure,
    f ≠ 0 ∧ C.heatBathHamiltonianL2 f = (0 : ℝ) • f
  refine ⟨C.gibbsVacuumL2, ?_, ?_⟩
  · intro hZero
    have hNorm := continuous_compact_oriented_gibbsVacuumL2_norm C
    rw [hZero, norm_zero] at hNorm
    norm_num at hNorm
  · rw [continuous_compact_oriented_heatBathHamiltonianL2_vacuum, zero_smul]

/-- Any nonzero-eigenvalue eigenvector is automatically orthogonal to the Gibbs
vacuum, by pairing symmetry and zero vacuum energy. -/
theorem continuous_compact_oriented_heatBathEigenvector_inner_vacuum_eq_zero_of_eigenvalue_ne_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    {lam : ℝ}
    {f : Lp ℝ 2 C.gibbsMeasure}
    (hlam : lam ≠ 0)
    (hEigen : C.heatBathHamiltonianL2 f = lam • f) :
    inner ℝ C.gibbsVacuumL2 f = 0 := by
  have hSymm :=
    continuous_compact_oriented_heatBathHamiltonianL2_inner_symm
      C C.gibbsVacuumL2 f
  rw [continuous_compact_oriented_heatBathHamiltonianL2_vacuum,
    inner_zero_left, hEigen, real_inner_smul_right] at hSymm
  have hProduct : lam * inner ℝ C.gibbsVacuumL2 f = 0 := hSymm.symm
  exact (mul_eq_zero.mp hProduct).resolve_left hlam

/-- A Poincare inequality with constant one bounds every nonzero point-spectrum
value below by one.  No compact-resolvent or full-spectrum assertion is used. -/
theorem continuous_compact_oriented_heatBathPointSpectrumL2_nonzero_lower_bound
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hPoincare : C.HeatBathPoincareL2 1)
    {lam : ℝ}
    (hlamMem : lam ∈ C.heatBathPointSpectrumL2)
    (hlam : lam ≠ 0) :
    1 ≤ lam := by
  change ∃ f : Lp ℝ 2 C.gibbsMeasure,
    f ≠ 0 ∧ C.heatBathHamiltonianL2 f = lam • f at hlamMem
  rcases hlamMem with ⟨f, hf, hEigen⟩
  have hOrth : inner ℝ C.gibbsVacuumL2 f = 0 :=
    continuous_compact_oriented_heatBathEigenvector_inner_vacuum_eq_zero_of_eigenvalue_ne_zero
      C hlam hEigen
  have hGap :=
    continuous_compact_oriented_heatBathHamiltonianL2_gap_on_vacuumOrthogonal
      C 1 hPoincare f hOrth
  rw [hEigen, real_inner_smul_left, real_inner_self_eq_norm_sq] at hGap
  have hNormPos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hNormSqPos : 0 < ‖f‖ ^ 2 := by positivity
  nlinarith

/-- The explicit normalized one-link fluctuation places eigenvalue one in the
actual beta-zero heat-bath point spectrum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_one_mem_heatBathPointSpectrumL2 :
    (1 : ℝ) ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 := by
  change ∃ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f =
        (1 : ℝ) • f
  refine ⟨periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2,
    ?_, ?_⟩
  · intro hZero
    have hNorm :=
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_norm_eq_one
    rw [hZero, norm_zero] at hNorm
    norm_num at hNorm
  · simpa using
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_hamiltonian_eq_self

/-- Every nonzero point-spectrum value of the actual beta-zero endpoint system
is at least one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_nonzero_lower_bound
    {lam : ℝ}
    (hlamMem : lam ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2)
    (hlam : lam ≠ 0) :
    1 ≤ lam :=
  continuous_compact_oriented_heatBathPointSpectrumL2_nonzero_lower_bound
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_heatBathPoincareL2_one
    hlamMem hlam

/-- Eigenvalue one lies in the nonzero point spectrum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_one_mem_nonzero_heatBathPointSpectrumL2 :
    (1 : ℝ) ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 \
        ({0} : Set ℝ) := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_one_mem_heatBathPointSpectrumL2,
    by norm_num⟩

/-- One is the least nonzero point-spectrum value of the actual beta-zero
finite-volume heat-bath Hamiltonian. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_nonzero_heatBathPointSpectrumL2_isLeast_one :
    IsLeast
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 \
        ({0} : Set ℝ))
      (1 : ℝ) := by
  refine ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_one_mem_nonzero_heatBathPointSpectrumL2,
    ?_⟩
  intro lam hlamMem
  apply
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_nonzero_lower_bound
      hlamMem.1
  intro hZero
  apply hlamMem.2
  simpa [hZero]

/-- The infimum of the actual nonzero point spectrum is exactly one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_nonzero_heatBathPointSpectrumL2_sInf_eq_one :
    sInf
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 \
        ({0} : Set ℝ)) = (1 : ℝ) := by
  let S : Set ℝ :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 \
      ({0} : Set ℝ)
  have hLeast : IsLeast S (1 : ℝ) :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_nonzero_heatBathPointSpectrumL2_isLeast_one
  have hBdd : BddBelow S := ⟨1, fun _ hlam => hLeast.2 hlam⟩
  have hNonempty : S.Nonempty := ⟨1, hLeast.1⟩
  apply le_antisymm
  · exact csInf_le hBdd hLeast.1
  · exact le_csInf hNonempty (fun _ hlam => hLeast.2 hlam)

/-- At beta zero, the actual Hamiltonian zero eigenspace is exactly the Gibbs
vacuum line. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_zero_iff_eq_inner_smul_vacuum
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f = 0 ↔
      f = inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 f •
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 :=
  continuous_compact_oriented_heatBathHamiltonianL2_eq_zero_iff_eq_inner_smul_vacuum
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
    1 zero_lt_one
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_heatBathPoincareL2_one
    f

/-- Compact receipt for the actual finite-volume beta-zero point-spectrum lower
edge.  This closes the point-spectrum statement only; it does not assert that
the full operator spectrum is discrete or that compact resolvent holds. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroPointSpectrumLowerEdgeL2Receipt : Prop :=
  (0 : ℝ) ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 ∧
    IsLeast
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 \
        ({0} : Set ℝ))
      (1 : ℝ) ∧
    sInf
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 \
        ({0} : Set ℝ)) = (1 : ℝ) ∧
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 ∧
    ∀ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f = 0 ↔
        f = inner ℝ
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 f •
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2

/-- The actual beta-zero point-spectrum lower-edge receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroPointSpectrumLowerEdgeL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroPointSpectrumLowerEdgeL2Receipt := by
  exact ⟨
    continuous_compact_oriented_zero_mem_heatBathPointSpectrumL2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_nonzero_heatBathPointSpectrumL2_isLeast_one,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_nonzero_heatBathPointSpectrumL2_sInf_eq_one,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_hamiltonian_eq_self,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_zero_iff_eq_inner_smul_vacuum⟩

end

end MathlibAnalytic
end MGAP4D
