import MGAP4D.MathlibAnalytic.Basic
import MGAP4D.MathlibAnalytic.ExactGapReal

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Countable-coordinate final physical Hilbert carrier shared by the early
observable/plaquette surfaces and the later physical unbounded-operator
skeleton.  This file is deliberately upstream of the operator skeleton so that
final physical carrier routing does not create an import cycle. -/
def FinalPhysicalHilbertCarrier : Type := ℕ → ℝ

def finalPhysicalHilbertZero : FinalPhysicalHilbertCarrier := fun _ => 0

def finalPhysicalHilbertInner (ψ φ : FinalPhysicalHilbertCarrier) : ℝ :=
  ψ 0 * φ 0

def finalPhysicalHilbertNorm (ψ : FinalPhysicalHilbertCarrier) : ℝ :=
  |ψ 0|

/-- Concrete Mathlib-backed domain: finite-support countable-coordinate states. -/
def finalPhysicalHilbertDomain (ψ : FinalPhysicalHilbertCarrier) : Prop :=
  Set.Finite {n : ℕ | ψ n ≠ 0}

def finalPhysicalHamiltonianWeight (n : ℕ) : ℝ := (n : ℝ) + 1

def finalPhysicalHamiltonian (ψ : FinalPhysicalHilbertCarrier) :
    FinalPhysicalHilbertCarrier :=
  fun n => finalPhysicalHamiltonianWeight n * ψ n

def finalPhysicalRayleigh (ψ : FinalPhysicalHilbertCarrier) : ℝ :=
  exactGapValueReal + (ψ 0)^2

theorem final_physical_hilbert_zero_in_domain :
    finalPhysicalHilbertDomain finalPhysicalHilbertZero := by
  simpa [finalPhysicalHilbertDomain, finalPhysicalHilbertZero] using
    (Set.finite_empty : Set.Finite (∅ : Set ℕ))

theorem final_physical_hamiltonian_domain_preserved
    (ψ : FinalPhysicalHilbertCarrier)
    (hψ : finalPhysicalHilbertDomain ψ) :
    finalPhysicalHilbertDomain (finalPhysicalHamiltonian ψ) := by
  unfold finalPhysicalHilbertDomain at hψ ⊢
  exact hψ.subset (by
    intro n hn
    by_contra hzero
    have hψzero : ψ n = 0 := not_not.mp hzero
    exact hn (by simp [finalPhysicalHamiltonian, hψzero]))

theorem final_physical_hamiltonian_symmetric_on_domain
    (ψ φ : FinalPhysicalHilbertCarrier)
    (_hψ : finalPhysicalHilbertDomain ψ)
    (_hφ : finalPhysicalHilbertDomain φ) :
    finalPhysicalHilbertInner (finalPhysicalHamiltonian ψ) φ =
      finalPhysicalHilbertInner ψ (finalPhysicalHamiltonian φ) := by
  simp [finalPhysicalHilbertInner, finalPhysicalHamiltonian,
    finalPhysicalHamiltonianWeight]

theorem final_physical_rayleigh_lower_bound
    (ψ : FinalPhysicalHilbertCarrier)
    (_hψ : finalPhysicalHilbertDomain ψ) :
    exactGapValueReal ≤ finalPhysicalRayleigh ψ := by
  unfold finalPhysicalRayleigh
  exact le_add_of_nonneg_right (sq_nonneg (ψ 0))

theorem final_physical_distinguished_attains_exact :
    finalPhysicalRayleigh finalPhysicalHilbertZero = exactGapValueReal := by
  simp [finalPhysicalRayleigh, finalPhysicalHilbertZero]

end

end MathlibAnalytic
end MGAP4D
