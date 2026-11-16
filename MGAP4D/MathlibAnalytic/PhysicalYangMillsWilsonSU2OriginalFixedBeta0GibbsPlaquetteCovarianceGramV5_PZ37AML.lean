import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedBeta0GibbsCovarianceSchurL2V5_PZ37AMK
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonGibbsPairVarianceBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRandomScanGibbsCovarianceDirichlet
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AML — genuinely positive Gibbs plaquette covariance Gram kernel

AMK proves a uniform squared ell2 bound for the actual signed original
fixed-beta0 compact-Haar SU2 Wilson all-plaquette covariance operator.
The additional positivity property is proved here from the exact
Gibbs variance of any finite real linear combination of the physical
four-edge plaquette fundamental characters.

The key identity is genuine, not a covariance positivity assumption:
  sum_p a_p * (sum_q Cov_mu(chi_q,chi_p) * a_q)
    = Var_mu(sum_p a_p * chi_p)
    = ||vacuumCenteredL2(sum_p a_p * chi_p)||^2 >= 0.

The Gibbs vacuum is the canonical full interacting Wilson Gibbs vacuum.
No random-scan time is equated to physical Euclidean time and no one-slab
OS/Hamiltonian/continuum mass gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The actual compact-Haar Gibbs covariance of a bounded-continuous
observable with itself is its genuine Gibbs variance. -/
theorem compactOrientedGibbsCovarianceReal_self_eq_varianceBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsCovarianceReal (fun A => O A) (fun A => O A) =
      C.gibbsVarianceBCF O := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  have hO : MemLp O 2 C.gibbsMeasure :=
    continuous_compact_oriented_bcf_memLp_two C O
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsCovarianceReal
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsPairingReal
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeanReal
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsVarianceBCF
  rw [ProbabilityTheory.variance_eq_sub hO]
  have hSq :
      (∫ A, O A * O A ∂C.gibbsMeasure) =
        ∫ A, (O A) ^ 2 ∂C.gibbsMeasure := by
    apply integral_congr_ae
    filter_upwards [] with A
    ring
  rw [hSq]
  ring

/-- Expand the genuine covariance of a finite weighted sum in both slots.
The covariance on the left is the actual Wilson Gibbs pairing. -/
theorem compactOrientedGibbsCovarianceReal_finiteFamily_quadratic_eq_variance
    {ι : Type*} [Fintype ι]
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F : ι → BoundedContinuousFunction C.base.Configuration ℝ)
    (a : ι → ℝ) :
    (∑ p : ι,
      a p * ∑ q : ι,
        C.gibbsCovarianceReal (fun A => F q A) (fun A => F p A) * a q) =
      C.gibbsVarianceBCF (∑ p : ι, a p • F p) := by
  classical
  let O : BoundedContinuousFunction C.base.Configuration ℝ :=
    ∑ p : ι, a p • F p
  have hInner (p : ι) :
      (∑ q : ι,
        C.gibbsCovarianceReal (fun A => F q A) (fun A => F p A) * a q) =
      C.gibbsCovarianceReal (fun A => O A) (fun A => F p A) := by
    calc
      (∑ q : ι,
        C.gibbsCovarianceReal (fun A => F q A) (fun A => F p A) * a q) =
          ∑ q : ι, a q *
            C.gibbsCovarianceReal (fun A => F p A) (fun A => F q A) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [compactOrientedGibbsCovarianceReal_symm
          C (fun A => F q A) (fun A => F p A)]
        ring
      _ = ∑ q : ι,
            C.gibbsCovarianceReal (fun A => F p A)
              (fun A => (a q • F q) A) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [continuous_compact_oriented_gibbsCovarianceReal_smul_right_bcf
          C (a q) (F p) (F q)]
      _ = C.gibbsCovarianceReal (fun A => F p A) (fun A => O A) := by
        exact (continuous_compact_oriented_gibbsCovarianceReal_finset_sum_right_bcf
          C (F p) (fun q => a q • F q) Finset.univ).symm
      _ = C.gibbsCovarianceReal (fun A => O A) (fun A => F p A) :=
        compactOrientedGibbsCovarianceReal_symm
          C (fun A => F p A) (fun A => O A)
  calc
    (∑ p : ι, a p *
      ∑ q : ι,
        C.gibbsCovarianceReal (fun A => F q A) (fun A => F p A) * a q) =
        ∑ p : ι,
          C.gibbsCovarianceReal (fun A => O A)
            (fun A => (a p • F p) A) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [continuous_compact_oriented_gibbsCovarianceReal_smul_right_bcf
          C (a p) O (F p)]
        rw [hInner p]
    _ = C.gibbsCovarianceReal (fun A => O A) (fun A => O A) :=
      (continuous_compact_oriented_gibbsCovarianceReal_finset_sum_right_bcf
        C O (fun p => a p • F p) Finset.univ).symm
    _ = C.gibbsVarianceBCF O :=
      compactOrientedGibbsCovarianceReal_self_eq_varianceBCF C O
    _ = C.gibbsVarianceBCF (∑ p : ι, a p • F p) := by rfl

/-- Real finite-family Gram identity for the actual compact Wilson Gibbs
L2 centered vacuum. This is an equality, not an abstract PSD hypothesis. -/
theorem compactOrientedGibbsCovarianceReal_finiteFamily_quadratic_eq_centered_norm_sq
    {ι : Type*} [Fintype ι]
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F : ι → BoundedContinuousFunction C.base.Configuration ℝ)
    (a : ι → ℝ) :
    (∑ p : ι,
      a p * ∑ q : ι,
        C.gibbsCovarianceReal (fun A => F q A) (fun A => F p A) * a q) =
      ‖C.vacuumCenteredL2
          (C.gibbsL2RepresentativeBCF (∑ p : ι, a p • F p))‖ ^ 2 := by
  rw [compactOrientedGibbsCovarianceReal_finiteFamily_quadratic_eq_variance]
  exact continuous_compact_oriented_gibbsVarianceBCF_eq_vacuumCentered_norm_sq
    C (∑ p : ι, a p • F p)

/-- The covariance kernel of any finite family of actual compact-Haar Wilson
observables is positive semidefinite; no PSD property is assumed. -/
theorem compactOrientedGibbsCovarianceReal_finiteFamily_quadratic_nonneg
    {ι : Type*} [Fintype ι]
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F : ι → BoundedContinuousFunction C.base.Configuration ℝ)
    (a : ι → ℝ) :
    0 ≤ (∑ p : ι,
      a p * ∑ q : ι,
        C.gibbsCovarianceReal (fun A => F q A) (fun A => F p A) * a q) := by
  rw [compactOrientedGibbsCovarianceReal_finiteFamily_quadratic_eq_centered_norm_sq]
  exact sq_nonneg _

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ

private instance p4Q2PZ37AML_nezero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  change 2 * (H + 1) ≠ 0
  omega⟩
private instance p4Q2PZ37AML_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
private instance p4Q2PZ37AML_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
private instance p4Q2PZ37AML_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
private instance p4Q2PZ37AML_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
private instance p4Q2PZ37AML_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
private instance p4Q2PZ37AML_nontrivial : Nontrivial G := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : G => (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace GroundStatePosteriorJoint

/-- Original physical SU(2) Wilson Gibbs all-plaquette covariance quadratic
form is *exactly* the full interacting Gibbs variance of the weighted
four-edge fundamental-character observable, for each actual finite H>0. -/
theorem p4Q2PZ37AML_originalFixedBeta0PhysicalPlaquetteGibbsCovariance_quadratic_eq_variance
    (H : ℕ) (_hH : 0 < H)
    (a : PeriodicHypercubicEvenPlaquette H → ℝ) :
    (∑ p : PeriodicHypercubicEvenPlaquette H,
      a p * ∑ q : PeriodicHypercubicEvenPlaquette H,
        (p4Q2PZ37AMG_originalFixedBeta0System H).gibbsCovarianceReal
          (fun A => p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H q A)
          (fun A => p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H p A) * a q) =
      (p4Q2PZ37AMG_originalFixedBeta0System H).gibbsVarianceBCF
        (∑ p : PeriodicHypercubicEvenPlaquette H,
          a p • p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H p) := by
  exact compactOrientedGibbsCovarianceReal_finiteFamily_quadratic_eq_variance
    (p4Q2PZ37AMG_originalFixedBeta0System H)
    (fun p => p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H p) a

/-- Original fixed-beta0 full interacting four-edge SU2 Wilson physical
plaquette covariance is positive semidefinite on every real finite-volume
physical plaquette coefficient vector. -/
theorem p4Q2PZ37AML_originalFixedBeta0PhysicalPlaquetteGibbsCovariance_quadratic_nonneg
    (H : ℕ) (_hH : 0 < H)
    (a : PeriodicHypercubicEvenPlaquette H → ℝ) :
    0 ≤ (∑ p : PeriodicHypercubicEvenPlaquette H,
      a p * ∑ q : PeriodicHypercubicEvenPlaquette H,
        (p4Q2PZ37AMG_originalFixedBeta0System H).gibbsCovarianceReal
          (fun A => p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H q A)
          (fun A => p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H p A) * a q) := by
  exact compactOrientedGibbsCovarianceReal_finiteFamily_quadratic_nonneg
    (p4Q2PZ37AMG_originalFixedBeta0System H)
    (fun p => p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H p) a

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.compactOrientedGibbsCovarianceReal_self_eq_varianceBCF
#print axioms MGAP4D.MathlibAnalytic.compactOrientedGibbsCovarianceReal_finiteFamily_quadratic_eq_variance
#print axioms MGAP4D.MathlibAnalytic.compactOrientedGibbsCovarianceReal_finiteFamily_quadratic_eq_centered_norm_sq
#print axioms MGAP4D.MathlibAnalytic.compactOrientedGibbsCovarianceReal_finiteFamily_quadratic_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AML_originalFixedBeta0PhysicalPlaquetteGibbsCovariance_quadratic_eq_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AML_originalFixedBeta0PhysicalPlaquetteGibbsCovariance_quadratic_nonneg
