import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianNonnegative
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Sequential closability of the right infinitesimal generator.  If domain
vectors converge strongly to zero and their generator values converge strongly,
then the limiting generator value is zero.

The proof uses only dissipativity and density of the canonical generator domain.
For every domain vector `z` and real scalar `r`, dissipativity of `psi n + r • z`
is passed to the limit.  The resulting quadratic inequality in `r` forces the
limit vector to be orthogonal to the dense generator domain. -/
theorem rightGenerator_sequentially_closable
    (T : P.StronglyContinuousPhysicalSemigroup)
    {psi : ℕ → T.rightGeneratorDomain} {eta : P.PhysicalHilbert}
    (hpsi : Tendsto (fun n => (psi n : P.PhysicalHilbert)) atTop (nhds 0))
    (hgenerator : Tendsto (fun n => T.rightGenerator (psi n)) atTop (nhds eta)) :
    eta = 0 := by
  have horthogonal :
      ∀ z : T.rightGeneratorDomain,
        ⟪eta, (z : P.PhysicalHilbert)⟫_ℝ = 0 := by
    intro z
    have hperturbation (r : ℝ) :
        ⟪eta + r • T.rightGenerator z,
            r • (z : P.PhysicalHilbert)⟫_ℝ ≤ 0 := by
      have hleft :
          Tendsto
            (fun n => T.rightGenerator (psi n + r • z))
            atTop
            (nhds (eta + r • T.rightGenerator z)) := by
        have hconst :
            Tendsto (fun _ : ℕ => r • T.rightGenerator z) atTop
              (nhds (r • T.rightGenerator z)) :=
          tendsto_const_nhds
        simpa using hgenerator.add hconst
      have hright :
          Tendsto
            (fun n =>
              ((psi n + r • z : T.rightGeneratorDomain) : P.PhysicalHilbert))
            atTop
            (nhds (r • (z : P.PhysicalHilbert))) := by
        have hconst :
            Tendsto (fun _ : ℕ => r • (z : P.PhysicalHilbert)) atTop
              (nhds (r • (z : P.PhysicalHilbert))) :=
          tendsto_const_nhds
        simpa using hpsi.add hconst
      have hinner :
          Tendsto
            (fun n =>
              ⟪T.rightGenerator (psi n + r • z),
                ((psi n + r • z : T.rightGeneratorDomain) :
                  P.PhysicalHilbert)⟫_ℝ)
            atTop
            (nhds
              ⟪eta + r • T.rightGenerator z,
                r • (z : P.PhysicalHilbert)⟫_ℝ) :=
        hleft.inner hright
      apply le_of_tendsto_of_tendsto hinner tendsto_const_nhds
      exact Filter.Eventually.of_forall fun n =>
        T.rightGenerator_inner_nonpos (psi n + r • z)
    have hquadratic (r : ℝ) :
        r * ⟪eta, (z : P.PhysicalHilbert)⟫_ℝ +
            r ^ 2 *
              ⟪T.rightGenerator z, (z : P.PhysicalHilbert)⟫_ℝ ≤ 0 := by
      have h := hperturbation r
      simpa [inner_add_left, real_inner_smul_left,
        real_inner_smul_right, pow_two, mul_assoc] using h
    have hq :
        ⟪T.rightGenerator z, (z : P.PhysicalHilbert)⟫_ℝ ≤ 0 :=
      T.rightGenerator_inner_nonpos z
    by_contra hnonzero
    have hsquare :
        0 < ⟪eta, (z : P.PhysicalHilbert)⟫_ℝ ^ 2 :=
      sq_pos_of_ne_zero hnonzero
    have hdenominator :
        0 < 1 - ⟪T.rightGenerator z, (z : P.PhysicalHilbert)⟫_ℝ := by
      linarith
    have hchosen := hquadratic
      (⟪eta, (z : P.PhysicalHilbert)⟫_ℝ /
        (1 - ⟪T.rightGenerator z, (z : P.PhysicalHilbert)⟫_ℝ))
    have hidentity :
        (⟪eta, (z : P.PhysicalHilbert)⟫_ℝ /
              (1 - ⟪T.rightGenerator z, (z : P.PhysicalHilbert)⟫_ℝ)) *
            ⟪eta, (z : P.PhysicalHilbert)⟫_ℝ +
          (⟪eta, (z : P.PhysicalHilbert)⟫_ℝ /
              (1 - ⟪T.rightGenerator z, (z : P.PhysicalHilbert)⟫_ℝ)) ^ 2 *
            ⟪T.rightGenerator z, (z : P.PhysicalHilbert)⟫_ℝ =
          ⟪eta, (z : P.PhysicalHilbert)⟫_ℝ ^ 2 /
            (1 - ⟪T.rightGenerator z, (z : P.PhysicalHilbert)⟫_ℝ) ^ 2 := by
      field_simp [ne_of_gt hdenominator]
      <;> ring
    rw [hidentity] at hchosen
    have hpositive :
        0 < ⟪eta, (z : P.PhysicalHilbert)⟫_ℝ ^ 2 /
            (1 - ⟪T.rightGenerator z, (z : P.PhysicalHilbert)⟫_ℝ) ^ 2 :=
      div_pos hsquare (sq_pos_of_pos hdenominator)
    exact (not_lt_of_ge hchosen) hpositive
  have hclosed :
      IsClosed {z : P.PhysicalHilbert | ⟪eta, z⟫_ℝ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hsubset :
      (T.rightGeneratorDomain : Set P.PhysicalHilbert) ⊆
        {z : P.PhysicalHilbert | ⟪eta, z⟫_ℝ = 0} := by
    intro z hz
    exact horthogonal ⟨z, hz⟩
  have hetaClosure :
      eta ∈ closure (T.rightGeneratorDomain : Set P.PhysicalHilbert) := by
    rw [T.rightGeneratorDomain_dense.closure_eq]
    exact mem_univ eta
  have hetaInner : ⟪eta, eta⟫_ℝ = 0 :=
    (closure_minimal hsubset hclosed) hetaClosure
  have hnormSq : ‖eta‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hetaInner
  have hnorm : ‖eta‖ = 0 := by
    nlinarith [norm_nonneg eta]
  exact norm_eq_zero.mp hnorm

/-- Sequential closability of the right Hamiltonian.  This is the signed form of
`rightGenerator_sequentially_closable`, since `H = -A` on the common dense
domain. -/
theorem rightHamiltonian_sequentially_closable
    (T : P.StronglyContinuousPhysicalSemigroup)
    {psi : ℕ → T.rightGeneratorDomain} {eta : P.PhysicalHilbert}
    (hpsi : Tendsto (fun n => (psi n : P.PhysicalHilbert)) atTop (nhds 0))
    (hHamiltonian :
      Tendsto (fun n => T.rightHamiltonian (psi n)) atTop (nhds eta)) :
    eta = 0 := by
  have hgenerator :
      Tendsto (fun n => T.rightGenerator (psi n)) atTop (nhds (-eta)) := by
    simpa [T.rightHamiltonian_apply] using hHamiltonian.neg
  have hzero : -eta = 0 :=
    T.rightGenerator_sequentially_closable hpsi hgenerator
  exact neg_eq_zero.mp hzero

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
