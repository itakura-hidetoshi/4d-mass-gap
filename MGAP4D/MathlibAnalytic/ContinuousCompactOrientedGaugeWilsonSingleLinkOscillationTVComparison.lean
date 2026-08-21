import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkExpectationTVComparison
import Mathlib.Tactic

/-!
# One-link conditional expectation oscillation bounds

The preceding current compact-Haar layer controls a bounded continuous one-link
test by twice its absolute bound times conditional total variation.  For
Dobrushin comparison the natural seminorm is instead oscillation: constants
must cancel between two normalized conditional laws.

This file uses the already-canonical exact density normalizations to center a
test at an arbitrary real constant.  Thus

`|phi - c| <= R  ->  |E_A phi - E_B phi| <= 2 R TV(A,B)`.

As a corollary, if `a <= phi <= b`, then

`|E_A phi - E_B phi| <= (b-a) TV(A,B)`.

The final theorems specialize both statements to the actual periodic compact
`SU(N)` Wilson source and its sparse influence certificate.  These remain
finite-volume static Gibbs estimates; no heat-bath/update time is identified
with physical OS Euclidean time and no factorial-continuum small-coupling
hypothesis is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Centering a bounded continuous test improves the generic half-`L1`
comparison from an absolute sup bound to a radius about any constant center. -/
theorem continuous_probabilityDensity_centeredBoundedTest_expectation_sub_abs_le_halfL1
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (phi p q : X → ℝ)
    (hphi : Continuous phi)
    (hp : Continuous p)
    (hq : Continuous q)
    (hp_int : ∫ x, p x ∂mu = 1)
    (hq_int : ∫ x, q x ∂mu = 1)
    (c R : ℝ)
    (hR : 0 ≤ R)
    (hphi_center : ∀ x, |phi x - c| ≤ R) :
    |(∫ x, phi x * p x ∂mu) - (∫ x, phi x * q x ∂mu)| ≤
      2 * R * ((2 : ℝ)⁻¹ * ∫ x, |p x - q x| ∂mu) := by
  let psi : X → ℝ := fun x => phi x - c
  have hpsi : Continuous psi := hphi.sub continuous_const
  have hpsi_bound : ∀ x, |psi x| ≤ R := by
    intro x
    exact hphi_center x
  have hpInt : Integrable p mu :=
    hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace p)
  have hqInt : Integrable q mu :=
    hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace q)
  have hphiPInt : Integrable (fun x => phi x * p x) mu :=
    (hphi.mul hp).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hphiQInt : Integrable (fun x => phi x * q x) mu :=
    (hphi.mul hq).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcPInt : Integrable (fun x => c * p x) mu :=
    (continuous_const.mul hp).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcQInt : Integrable (fun x => c * q x) mu :=
    (continuous_const.mul hq).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcenterP :
      (∫ x, psi x * p x ∂mu) = (∫ x, phi x * p x ∂mu) - c := by
    calc
      (∫ x, psi x * p x ∂mu) =
          ∫ x, (phi x * p x - c * p x) ∂mu := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          dsimp [psi]
          ring
      _ = (∫ x, phi x * p x ∂mu) - (∫ x, c * p x ∂mu) := by
        rw [integral_sub hphiPInt hcPInt]
      _ = (∫ x, phi x * p x ∂mu) - c * (∫ x, p x ∂mu) := by
        rw [integral_const_mul]
      _ = (∫ x, phi x * p x ∂mu) - c := by
        rw [hp_int]
        ring
  have hcenterQ :
      (∫ x, psi x * q x ∂mu) = (∫ x, phi x * q x ∂mu) - c := by
    calc
      (∫ x, psi x * q x ∂mu) =
          ∫ x, (phi x * q x - c * q x) ∂mu := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          dsimp [psi]
          ring
      _ = (∫ x, phi x * q x ∂mu) - (∫ x, c * q x ∂mu) := by
        rw [integral_sub hphiQInt hcQInt]
      _ = (∫ x, phi x * q x ∂mu) - c * (∫ x, q x ∂mu) := by
        rw [integral_const_mul]
      _ = (∫ x, phi x * q x ∂mu) - c := by
        rw [hq_int]
        ring
  have hbound :=
    continuous_probabilityDensity_boundedTest_expectation_sub_abs_le_halfL1
      mu psi p q hpsi hp hq R hR hpsi_bound
  rw [hcenterP, hcenterQ] at hbound
  have hcancel :
      (∫ x, phi x * p x ∂mu) - (∫ x, phi x * q x ∂mu) =
        ((∫ x, phi x * p x ∂mu) - c) -
          ((∫ x, phi x * q x ∂mu) - c) := by
    ring
  rw [hcancel]
  exact hbound

/-- Exact compact-Wilson centered-test comparison by conditional total
variation. -/
theorem continuous_compact_oriented_singleLinkConditionalGaugeExpectation_sub_abs_le_totalVariation_of_center
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (phi : C.base.Gauge → ℝ)
    (hphi : Continuous phi)
    (c R : ℝ)
    (hR : 0 ≤ R)
    (hphi_center : ∀ g, |phi g - c| ≤ R)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    |C.singleLinkConditionalGaugeExpectation phi A target -
        C.singleLinkConditionalGaugeExpectation phi B target| ≤
      2 * R * C.singleLinkConditionalTotalVariation A B target := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalGaugeExpectation
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalTotalVariation
  exact
    continuous_probabilityDensity_centeredBoundedTest_expectation_sub_abs_le_halfL1
      (normalizedCompactHaar C.base.Gauge)
      phi
      (C.singleLinkRealConditionalDensity A target)
      (C.singleLinkRealConditionalDensity B target)
      hphi
      (continuous_compact_oriented_singleLinkRealConditionalDensity C A target)
      (continuous_compact_oriented_singleLinkRealConditionalDensity C B target)
      (continuous_compact_oriented_integral_singleLinkRealConditionalDensity C A target)
      (continuous_compact_oriented_integral_singleLinkRealConditionalDensity C B target)
      c R hR hphi_center

/-- Interval form of the exact compact-Wilson comparison.  Its coefficient is
the oscillation width `b-a`, rather than twice an absolute sup bound. -/
theorem continuous_compact_oriented_singleLinkConditionalGaugeExpectation_sub_abs_le_totalVariation_of_interval
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (phi : C.base.Gauge → ℝ)
    (hphi : Continuous phi)
    (a b : ℝ)
    (hab : a ≤ b)
    (hlo : ∀ g, a ≤ phi g)
    (hhi : ∀ g, phi g ≤ b)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    |C.singleLinkConditionalGaugeExpectation phi A target -
        C.singleLinkConditionalGaugeExpectation phi B target| ≤
      (b - a) * C.singleLinkConditionalTotalVariation A B target := by
  let c : ℝ := (a + b) / 2
  let R : ℝ := (b - a) / 2
  have hR : 0 ≤ R := by
    unfold R
    exact div_nonneg (sub_nonneg.mpr hab) (by norm_num)
  have hcenter : ∀ g, |phi g - c| ≤ R := by
    intro g
    unfold c R
    rw [abs_le]
    constructor <;> linarith [hlo g, hhi g]
  have h :=
    continuous_compact_oriented_singleLinkConditionalGaugeExpectation_sub_abs_le_totalVariation_of_center
      C phi hphi c R hR hcenter A B target
  convert h using 1 <;> ring

/-- Periodic `SU(N)` centered-test specialization using the canonical sparse
one-link influence certificate. -/
theorem periodicHypercubicSpecialUnitary_singleLinkConditionalGaugeExpectation_sub_abs_le_sparseInfluence_of_center
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : Continuous phi)
    (c R : ℝ)
    (hR : 0 ≤ R)
    (hphi_center : ∀ g, |phi g - c| ≤ R)
    (A B : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.Configuration)
    (target source : PeriodicHypercubicEdge n)
    (hAgree : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.AgreeOffLink A B source) :
    |(periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).singleLinkConditionalGaugeExpectation phi A target -
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).singleLinkConditionalGaugeExpectation phi B target| ≤
      2 * R * periodicHypercubicSpecialUnitarySparseActiveTVInfluence
        n beta target source := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta hBeta
  have hExpectation :=
    continuous_compact_oriented_singleLinkConditionalGaugeExpectation_sub_abs_le_totalVariation_of_center
      C phi hphi c R hR hphi_center A B target
  have hTV :=
    periodicHypercubicSpecialUnitary_singleLinkConditionalTotalVariation_le_sparseInfluence
      n N hn hN beta hBeta A B target source hAgree
  exact le_trans hExpectation
    (mul_le_mul_of_nonneg_left hTV (mul_nonneg (by norm_num) hR))

/-- Periodic `SU(N)` interval/oscillation specialization. -/
theorem periodicHypercubicSpecialUnitary_singleLinkConditionalGaugeExpectation_sub_abs_le_sparseInfluence_of_interval
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : Continuous phi)
    (a b : ℝ)
    (hab : a ≤ b)
    (hlo : ∀ g, a ≤ phi g)
    (hhi : ∀ g, phi g ≤ b)
    (A B : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.Configuration)
    (target source : PeriodicHypercubicEdge n)
    (hAgree : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.AgreeOffLink A B source) :
    |(periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).singleLinkConditionalGaugeExpectation phi A target -
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).singleLinkConditionalGaugeExpectation phi B target| ≤
      (b - a) * periodicHypercubicSpecialUnitarySparseActiveTVInfluence
        n beta target source := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta hBeta
  have hExpectation :=
    continuous_compact_oriented_singleLinkConditionalGaugeExpectation_sub_abs_le_totalVariation_of_interval
      C phi hphi a b hab hlo hhi A B target
  have hTV :=
    periodicHypercubicSpecialUnitary_singleLinkConditionalTotalVariation_le_sparseInfluence
      n N hn hN beta hBeta A B target source hAgree
  exact le_trans hExpectation
    (mul_le_mul_of_nonneg_left hTV (sub_nonneg.mpr hab))

end

end MathlibAnalytic
end MGAP4D
