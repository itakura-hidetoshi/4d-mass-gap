import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalSourceGramComparison
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarBetaZeroRightKrylovCollapse
import Mathlib.Tactic

/-!
# P4-Q2-F: actual fine beta-zero uncentered source-Gram frame obstruction

The physical source Gram in PR #5341 retains the UN-CENTERED fine-right
Krylov family; it cannot have a coefficient-ell² frame constant uniform
in Krylov depth r without removing the common physical unit component.

The existing exact original fine-beta-zero theorem says that when
beta(n+1)=0, EVERY physical right Krylov mode R_{n,j} equals the same
normalized physical Haar constant unit u_H. Thus the TRUE fine physical
source Gram has ALL entries equal to 1, and its entire quadratic form is
  a*G_source*a = (sum_j a_j)^2.

Choosing coefficients a_j=1 yields
  a*G_source*a = (r+1)^2,   sum_j a_j^2 = r+1.
Hence no real C independent of r can satisfy a source-frame estimate
for all r. This is an unconditional EXACT no-go for the uncentered
source-frame sufficient condition from #5341 AT fine beta zero;
it is NOT a no-go for the original Wilson posterior Gram itself.
At frozen beta zero, that posterior residual Gram can vanish even
though the physical source Gram is rank one.

The frozen beta(n) is not modified or assumed equal to fine beta(n+1).
No Dobrushin, new posterior, sorry/admit or novel axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4SourceNoGoTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4SourceNoGoCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4SourceNoGoSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4SourceNoGoMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4SourceNoGoBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace GroundStatePosteriorJoint

/-- At genuine fine beta(n+1)=0 the ACTUAL source Gram is the
all-ones matrix, since every physical right orbit mode is the same
unit constant. The distinct frozen beta(n) is unrestricted. -/
theorem fineRightKrylovOriginalPhysicalSourceGram_entry_eq_one_of_fine_beta_zero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (hzero : beta (n + 1) = 0) (i j : Fin (r + 1)) :
    (fineRightKrylovOriginalPhysicalSourceGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r) i j = 1 := by
  change inner ℝ
    (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (i : ℕ))
    (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ)) = 1
  rw [fineRightFactor_eq_constantUnit_of_fine_beta_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (i : ℕ) hzero,
    fineRightFactor_eq_constantUnit_of_fine_beta_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ) hzero,
    real_inner_self_eq_norm_sq,
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm]
  norm_num

/-- Every signed fine-right source combination collapses to the same
physical normalized unit times the SUM of its real coefficients. -/
theorem fineRightKrylovOriginalSignedPhysicalSource_eq_sum_smul_unit_of_fine_beta_zero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (hzero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ) :
    fineRightKrylovOriginalSignedPhysicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a =
      (∑ j : Fin (r + 1), a j) •
        periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
          (halfExtent (n + 1)) 2 := by
  classical
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
    (halfExtent (n + 1)) 2
  change
    (∑ j : Fin (r + 1), a j •
      physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j : ℕ)) =
      (∑ j : Fin (r + 1), a j) • u
  calc
    (∑ j : Fin (r + 1), a j •
      physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j : ℕ)) =
      ∑ j : Fin (r + 1), a j • u := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [fineRightFactor_eq_constantUnit_of_fine_beta_zero
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ) hzero]
    _ = (∑ j : Fin (r + 1), a j) • u := by rw [Finset.sum_smul]

/-- Exact rank-one source Gram Rayleigh at fine beta zero, for every
signed coefficient vector and every Krylov truncation depth. -/
theorem fineRightKrylovOriginalPhysicalSourceGram_rayleigh_eq_sum_sq_of_fine_beta_zero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (hzero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovOriginalPhysicalSourceGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) =
      (∑ j : Fin (r + 1), a j) ^ 2 := by
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
    (halfExtent (n + 1)) 2
  have hF :=
    fineRightKrylovOriginalSignedPhysicalSource_eq_sum_smul_unit_of_fine_beta_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hzero a
  have hu : ‖u‖ = (1 : ℝ) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm
      (halfExtent (n + 1)) 2
  calc
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovOriginalPhysicalSourceGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) =
      ‖fineRightKrylovOriginalSignedPhysicalSource
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a‖ ^ 2 :=
        fineRightKrylovOriginalPhysicalSourceGram_rayleigh_eq_sourceNorm_sq
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r a
    _ = ‖(∑ j : Fin (r + 1), a j) • u‖ ^ 2 := by rw [hF]
    _ = (∑ j : Fin (r + 1), a j) ^ 2 := by
      rw [norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]

/-- The all-one source coefficients have a Rayleigh quotient exactly
r+1 at fine beta zero: the eigenvalue is NOT bounded independently
of Krylov depth, though the posterior Gram may separately vanish. -/
theorem fineRightKrylovOriginalPhysicalSourceGram_ones_rayleigh_of_fine_beta_zero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (hzero : beta (n + 1) = 0) :
    star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
      (Matrix.mulVec
        (fineRightKrylovOriginalPhysicalSourceGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r)
        (fun _ : Fin (r + 1) => (1 : ℝ))) =
      ((r + 1 : ℕ) : ℝ) ^ 2 := by
  have h :=
    fineRightKrylovOriginalPhysicalSourceGram_rayleigh_eq_sum_sq_of_fine_beta_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hzero (fun _ : Fin (r + 1) => (1 : ℝ))
  simpa using h

/-- Rigorous no-go for an r-independent real source-frame constant
on the ACTUAL uncentered fine-right Krylov family at fine beta zero.
This says NOTHING against volume-uniformity of a posterior Gram that
annihilates the common unit direction. -/
theorem fineRightKrylovOriginalPhysicalSourceGram_noUniformFrame_of_fine_beta_zero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n : ℕ) (hzero : beta (n + 1) = 0) :
    ¬ ∃ C : ℝ, ∀ r : ℕ,
      star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovOriginalPhysicalSourceGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r)
          (fun _ : Fin (r + 1) => (1 : ℝ))) ≤
        C * (∑ _j : Fin (r + 1), (1 : ℝ) ^ 2) := by
  rintro ⟨C, hFrame⟩
  obtain ⟨r, hr⟩ := exists_nat_gt C
  have hRay :=
    fineRightKrylovOriginalPhysicalSourceGram_ones_rayleigh_of_fine_beta_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hzero
  have hCount :
      (∑ _j : Fin (r + 1), (1 : ℝ) ^ 2) = ((r + 1 : ℕ) : ℝ) := by
    simp
  have hBound := hFrame r
  rw [hRay, hCount] at hBound
  have hLt : C < ((r + 1 : ℕ) : ℝ) := by
    have hr' : C < (r : ℝ) := hr
    have hmore : (r : ℝ) < ((r + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self r
    exact lt_trans hr' hmore
  have hPos : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  nlinarith

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
