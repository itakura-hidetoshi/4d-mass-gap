import MGAP4D.MathlibAnalytic.Basic
import MGAP4D.MathlibAnalytic.ExactGapReal
import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalHilbertCompileSmoke

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Legacy countable-coordinate prototype retained for compatibility with the
early operator and audit skeletons.

This is **not** the physical Yang--Mills Hilbert space: its displayed pairing and
norm inspect only coordinate `0`.  The physical carrier is now constructed in
`EuclideanYangMillsOSPhysicalHilbertConstruction` as the completion of the OS
separation quotient of positive-time Euclidean observables. -/
def FinalPhysicalHilbertCarrier : Type := ℕ → ℝ

/-- Explicit compatibility name making the prototype status visible. -/
abbrev LegacyCountableCoordinateCarrier := FinalPhysicalHilbertCarrier

def finalPhysicalHilbertZero : FinalPhysicalHilbertCarrier := fun _ => 0

/-- Legacy prototype pairing.  It must not be used to identify the physical
Yang--Mills Hilbert inner product. -/
def finalPhysicalHilbertInner (ψ φ : FinalPhysicalHilbertCarrier) : ℝ :=
  ψ 0 * φ 0

/-- Legacy prototype seminorm.  The genuine physical norm is the completed OS
norm on reflected positive-time observables. -/
def finalPhysicalHilbertNorm (ψ : FinalPhysicalHilbertCarrier) : ℝ :=
  |ψ 0|

/-- Concrete prototype domain: finite-support countable-coordinate states. -/
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
