import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicPositiveClosureTimeOneL2V5_PZ37AND
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANE — simultaneous true-Gibbs and product-Haar time-one L2 classes

AND gives the real L2 class of the original full-periodic interacting Gibbs
positive-closure time-one two-mode Wilson cylinder.  ANB and ANC give mutual
absolute continuity of that EXACT marginal and the unmodified product Haar
on the SAME boundary/open-positive-half configuration space.

This module constructs the literal *same* bounded time-one cylinder also in
the real L2 space over the original product Haar and proves that the two
coefficient-to-L2 assignments have identical zero classes.  A single pair of
original physical top-eigenspace-orthogonal coefficients then gives nonzero
real L2 classes for both measures.

This is ordinary L2 zero-class compatibility only.  It proves neither
equivalence of L2 norms nor equality of OS reflection-positive null spaces,
nor an OS physical Hilbert embedding, nor a Wilson one-slab intertwiner or a
continuum Yang-Mills spectral gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANE_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37ANE_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANE_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANE_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANE_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANE_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

/-- Original boundary/open-half product Haar on the exact same positive
closure carrier as the original Gibbs pushforward used by AND. -/
noncomputable def p4Q2PZ37ANE_originalPositiveClosureHaarMeasure
    (H : ℕ) :
    Measure (PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :=
  (periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
    (periodicHypercubicEvenOpenHalfHaarMeasure H 2)

/-- The unmodified compact product Haar is finite.  No equality to the
original Gibbs law or uniform density estimate is invoked. -/
local instance p4Q2PZ37ANE_originalPositiveClosureHaarFinite (H : ℕ) :
    IsFiniteMeasure (p4Q2PZ37ANE_originalPositiveClosureHaarMeasure H) := by
  letI : IsFiniteMeasure (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
    dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
    infer_instance
  letI : IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
    dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  dsimp [p4Q2PZ37ANE_originalPositiveClosureHaarMeasure]
  infer_instance

/-- Every original time-one physical two-mode cylinder is L2 for unchanged
closure Haar, by the same global pointwise bound used in AND. -/
theorem p4Q2PZ37ANE_timeOneOriginalHaar_memLp
    (H : ℕ) (c0 c1 : ℝ) :
    MemLp (p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable H c0 c1)
      2 (p4Q2PZ37ANE_originalPositiveClosureHaarMeasure H) := by
  exact MemLp.of_bound
    (p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable_measurable
      H c0 c1).aestronglyMeasurable
    (|c0| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0‖ +
      |c1| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1‖)
    (Filter.Eventually.of_forall
      (p4Q2PZ37AND_timeOnePositiveClosureObservable_norm_le H c0 c1))

/-- Product-Haar real L2 class of the literal ANC positive-closure time-one
Wilson cylinder, with unchanged coefficients and positive-time index. -/
noncomputable def p4Q2PZ37ANE_timeOneOriginalHaarL2
    (H : ℕ) (c0 c1 : ℝ) :
    Lp ℝ 2 (p4Q2PZ37ANE_originalPositiveClosureHaarMeasure H) :=
  (p4Q2PZ37ANE_timeOneOriginalHaar_memLp H c0 c1).toLp
    (p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable H c0 c1)

/-- The original time-one function is the exact a.e. representative of its
product-Haar L2 class. -/
theorem p4Q2PZ37ANE_timeOneOriginalHaarL2_coeFn
    (H : ℕ) (c0 c1 : ℝ) :
    p4Q2PZ37ANE_timeOneOriginalHaarL2 H c0 c1
      =ᵐ[p4Q2PZ37ANE_originalPositiveClosureHaarMeasure H]
        p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable H c0 c1 := by
  exact (p4Q2PZ37ANE_timeOneOriginalHaar_memLp H c0 c1).coeFn_toLp

/-- For ALL original physical two-mode coefficients, the true periodic
interacting Gibbs L2 class vanishes exactly when the original product-Haar
L2 class vanishes.  This is equality of the two coefficient kernels, NOT
an isometry or an OS-null-space statement. -/
theorem p4Q2PZ37ANE_timeOneGibbsL2_eq_zero_iff_HaarL2_eq_zero
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) :
    p4Q2PZ37AND_truePeriodicTimeOnePositiveClosureL2 H beta hbeta c0 c1 = 0 ↔
      p4Q2PZ37ANE_timeOneOriginalHaarL2 H c0 c1 = 0 := by
  let μ := p4Q2PZ37AND_originalPeriodicPositiveClosureMeasure H beta hbeta
  let λ := p4Q2PZ37ANE_originalPositiveClosureHaarMeasure H
  let F := p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable H c0 c1
  let ψG : Lp ℝ 2 μ :=
    p4Q2PZ37AND_truePeriodicTimeOnePositiveClosureL2 H beta hbeta c0 c1
  let ψH : Lp ℝ 2 λ := p4Q2PZ37ANE_timeOneOriginalHaarL2 H c0 c1
  have hRepG : ψG =ᵐ[μ] F := by
    simpa [ψG, μ, F] using
      p4Q2PZ37AND_truePeriodicTimeOnePositiveClosureL2_coeFn
        H beta hbeta c0 c1
  have hRepH : ψH =ᵐ[λ] F := by
    simpa [ψH, λ, F] using
      p4Q2PZ37ANE_timeOneOriginalHaarL2_coeFn H c0 c1
  have hZeroG : ψG = 0 ↔ F =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    constructor
    · intro hz
      have hψzero : ψG =ᵐ[μ] (fun _ => (0 : ℝ)) := by
        rw [hz]
        simpa only [Pi.zero_apply] using (Lp.coeFn_zero ℝ 2 μ)
      exact hRepG.symm.trans hψzero
    · intro hfz
      apply Lp.ext
      have hψzero : ψG =ᵐ[μ] (fun _ => (0 : ℝ)) :=
        hRepG.trans hfz
      have h0 : (0 : Lp ℝ 2 μ) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
        simpa only [Pi.zero_apply] using (Lp.coeFn_zero ℝ 2 μ)
      exact hψzero.trans h0.symm
  have hZeroH : ψH = 0 ↔ F =ᵐ[λ] (fun _ => (0 : ℝ)) := by
    constructor
    · intro hz
      have hψzero : ψH =ᵐ[λ] (fun _ => (0 : ℝ)) := by
        rw [hz]
        simpa only [Pi.zero_apply] using (Lp.coeFn_zero ℝ 2 λ)
      exact hRepH.symm.trans hψzero
    · intro hfz
      apply Lp.ext
      have hψzero : ψH =ᵐ[λ] (fun _ => (0 : ℝ)) :=
        hRepH.trans hfz
      have h0 : (0 : Lp ℝ 2 λ) =ᵐ[λ] (fun _ => (0 : ℝ)) := by
        simpa only [Pi.zero_apply] using (Lp.coeFn_zero ℝ 2 λ)
      exact hψzero.trans h0.symm
  have hAEzero : (F =ᵐ[μ] (fun _ => (0 : ℝ))) ↔
      (F =ᵐ[λ] (fun _ => (0 : ℝ))) := by
    simpa [μ, λ, p4Q2PZ37AND_originalPeriodicPositiveClosureMeasure,
      p4Q2PZ37ANE_originalPositiveClosureHaarMeasure, F] using
      (p4Q2PZ37ANC_fullPeriodicPositiveClosure_ae_zero_iff_productHaar
        H beta hbeta F)
  change ψG = 0 ↔ ψH = 0
  exact hZeroG.trans (hAEzero.trans hZeroH.symm)

/-- The SAME originally top-orthogonal pair of physical two-mode
coefficients supplies genuinely nonzero ordinary real L2 classes for both
the true periodic Gibbs marginal and unmodified product Haar.  It does not
imply a nonzero class in any OS quotient. -/
theorem p4Q2PZ37ANE_exists_common_nonzero_originalTimeOneGibbsAndHaarL2
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ c0 c1 : ℝ,
      (c0 • p4Q2PZ37AMU_actualPhysicalGaussMode H 0 +
        c1 • p4Q2PZ37AMU_actualPhysicalGaussMode H 1) ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            H 2 (by norm_num) beta hbeta ∧
      ∃ ψG : Lp ℝ 2
          (p4Q2PZ37AND_originalPeriodicPositiveClosureMeasure H beta hbeta),
        ∃ ψH : Lp ℝ 2
          (p4Q2PZ37ANE_originalPositiveClosureHaarMeasure H),
          ψG ≠ 0 ∧ ψH ≠ 0 ∧
          ψG =ᵐ[p4Q2PZ37AND_originalPeriodicPositiveClosureMeasure H beta hbeta]
            p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable H c0 c1 ∧
          ψH =ᵐ[p4Q2PZ37ANE_originalPositiveClosureHaarMeasure H]
            p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable H c0 c1 := by
  obtain ⟨c0, c1, hTop, hFne⟩ :=
    p4Q2PZ37ANC_exists_nonzero_truePeriodicGibbsPositiveClosureTimeOneCylinder
      H beta hbeta
  let μ := p4Q2PZ37AND_originalPeriodicPositiveClosureMeasure H beta hbeta
  let ψG := p4Q2PZ37AND_truePeriodicTimeOnePositiveClosureL2
    H beta hbeta c0 c1
  let ψH := p4Q2PZ37ANE_timeOneOriginalHaarL2 H c0 c1
  have hRepG : ψG =ᵐ[μ]
      p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable H c0 c1 := by
    exact p4Q2PZ37AND_truePeriodicTimeOnePositiveClosureL2_coeFn
      H beta hbeta c0 c1
  have hGne : ψG ≠ 0 := by
    intro hz
    have hψzero : ψG =ᵐ[μ] (fun _ => (0 : ℝ)) := by
      rw [hz]
      simpa only [Pi.zero_apply] using (Lp.coeFn_zero ℝ 2 μ)
    exact hFne (hRepG.symm.trans hψzero)
  have hHne : ψH ≠ 0 := by
    intro hz
    have hGzero :=
      (p4Q2PZ37ANE_timeOneGibbsL2_eq_zero_iff_HaarL2_eq_zero
        H beta hbeta c0 c1).mpr hz
    exact hGne hGzero
  exact ⟨c0, c1, hTop, ψG, ψH, hGne, hHne,
    hRepG, p4Q2PZ37ANE_timeOneOriginalHaarL2_coeFn H c0 c1⟩

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANE_timeOneOriginalHaar_memLp
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANE_timeOneOriginalHaarL2_coeFn
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANE_timeOneGibbsL2_eq_zero_iff_HaarL2_eq_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANE_exists_common_nonzero_originalTimeOneGibbsAndHaarL2
