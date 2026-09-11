import MGAP4D.MathlibAnalytic.OrthonormalDiagonalOperator
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExponentialGapSlope
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

/-- The continuous-time semigroup generated spectrally by a finite-dimensional
real symmetric Hamiltonian.  On the canonical orthonormal eigenbasis its
coefficient at time `t` is `exp (-energy * t)`. -/
noncomputable def finiteDimensionalSymmetricHamiltonianSpectralSemigroup
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E)
    (hH : H.IsSymmetric)
    (dimension : ℕ)
    (hDimension : Module.finrank ℝ E = dimension)
    (t : NNReal) : E →L[ℝ] E :=
  orthonormalDiagonalOperator
    (hH.eigenvectorBasis hDimension)
    (fun i : Fin dimension =>
      Real.exp (-(hH.eigenvalues hDimension i) * (t : ℝ)))

/-- The spectral semigroup has the expected exponential action on every
Hamiltonian eigenbasis vector. -/
@[simp] theorem finiteDimensionalSymmetricHamiltonianSpectralSemigroup_apply_eigenvectorBasis
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E)
    (hH : H.IsSymmetric)
    (dimension : ℕ)
    (hDimension : Module.finrank ℝ E = dimension)
    (t : NNReal)
    (i : Fin dimension) :
    finiteDimensionalSymmetricHamiltonianSpectralSemigroup
        H hH dimension hDimension t
        ((hH.eigenvectorBasis hDimension) i) =
      Real.exp (-(hH.eigenvalues hDimension i) * (t : ℝ)) •
        ((hH.eigenvectorBasis hDimension) i) := by
  exact orthonormalDiagonalOperator_apply_basis
    (hH.eigenvectorBasis hDimension)
    (fun j : Fin dimension =>
      Real.exp (-(hH.eigenvalues hDimension j) * (t : ℝ))) i

/-- The Hamiltonian itself has the canonical orthonormal eigenbasis expansion. -/
theorem finiteDimensionalSymmetricHamiltonian_apply_eq_sum
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E)
    (hH : H.IsSymmetric)
    (dimension : ℕ)
    (hDimension : Module.finrank ℝ E = dimension)
    (x : E) :
    H x =
      ∑ i : Fin dimension,
        inner ℝ ((hH.eigenvectorBasis hDimension) i) x •
          (hH.eigenvalues hDimension i •
            ((hH.eigenvectorBasis hDimension) i)) := by
  let b := hH.eigenvectorBasis hDimension
  conv_lhs => rw [← b.sum_repr' x]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hH.apply_eigenvectorBasis hDimension i]
  simp [b, smul_smul]

/-- The finite spectral-semigroup right Hamiltonian difference quotient is the
finite sum of the scalar exponential slopes in the Hamiltonian eigenbasis. -/
theorem finiteDimensionalSymmetricHamiltonianSpectralSemigroup_differenceQuotient_eq_sum
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E)
    (hH : H.IsSymmetric)
    (dimension : ℕ)
    (hDimension : Module.finrank ℝ E = dimension)
    (x : E)
    (t : NNReal) :
    (t : ℝ)⁻¹ •
        (x - finiteDimensionalSymmetricHamiltonianSpectralSemigroup
          H hH dimension hDimension t x) =
      ∑ i : Fin dimension,
        inner ℝ ((hH.eigenvectorBasis hDimension) i) x •
          (((t : ℝ)⁻¹ *
              (1 - Real.exp
                (-(hH.eigenvalues hDimension i) * (t : ℝ)))) •
            ((hH.eigenvectorBasis hDimension) i)) := by
  let b := hH.eigenvectorBasis hDimension
  have hx : x = ∑ i : Fin dimension, inner ℝ (b i) x • b i :=
    (b.sum_repr' x).symm
  have hsemigroup :
      finiteDimensionalSymmetricHamiltonianSpectralSemigroup
          H hH dimension hDimension t x =
        ∑ i : Fin dimension,
          inner ℝ (b i) x •
            (Real.exp (-(hH.eigenvalues hDimension i) * (t : ℝ)) • b i) := by
    simpa [finiteDimensionalSymmetricHamiltonianSpectralSemigroup, b] using
      orthonormalDiagonalOperator_apply
        b
        (fun i : Fin dimension =>
          Real.exp (-(hH.eigenvalues hDimension i) * (t : ℝ))) x
  change
    (t : ℝ)⁻¹ •
        (x - finiteDimensionalSymmetricHamiltonianSpectralSemigroup
          H hH dimension hDimension t x) = _
  calc
    (t : ℝ)⁻¹ •
        (x - finiteDimensionalSymmetricHamiltonianSpectralSemigroup
          H hH dimension hDimension t x) =
      (t : ℝ)⁻¹ •
        ((∑ i : Fin dimension, inner ℝ (b i) x • b i) -
          finiteDimensionalSymmetricHamiltonianSpectralSemigroup
            H hH dimension hDimension t x) :=
      congrArg
        (fun y : E =>
          (t : ℝ)⁻¹ •
            (y - finiteDimensionalSymmetricHamiltonianSpectralSemigroup
              H hH dimension hDimension t x)) hx
    _ =
      (t : ℝ)⁻¹ •
        ((∑ i : Fin dimension, inner ℝ (b i) x • b i) -
          ∑ i : Fin dimension,
            inner ℝ (b i) x •
              (Real.exp (-(hH.eigenvalues hDimension i) * (t : ℝ)) • b i)) :=
      congrArg
        (fun y : E =>
          (t : ℝ)⁻¹ •
            ((∑ i : Fin dimension, inner ℝ (b i) x • b i) - y))
        hsemigroup
    _ = _ := by
      rw [← Finset.sum_sub_distrib, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      module

/-- The theorem-generated finite spectral semigroup has right derivative `-H`,
or equivalently its right Hamiltonian difference quotient converges to `H`, on
every finite-dimensional state. -/
theorem finiteDimensionalSymmetricHamiltonianSpectralSemigroup_differenceQuotient_tendsto
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E)
    (hH : H.IsSymmetric)
    (dimension : ℕ)
    (hDimension : Module.finrank ℝ E = dimension)
    (x : E) :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ •
          (x - finiteDimensionalSymmetricHamiltonianSpectralSemigroup
            H hH dimension hDimension t x))
      (nhdsWithin 0 (Ioi 0))
      (nhds (H x)) := by
  rw [finiteDimensionalSymmetricHamiltonian_apply_eq_sum
    H hH dimension hDimension x]
  have hsum :
      Tendsto
        (fun t : NNReal =>
          ∑ i : Fin dimension,
            inner ℝ ((hH.eigenvectorBasis hDimension) i) x •
              (((t : ℝ)⁻¹ *
                  (1 - Real.exp
                    (-(hH.eigenvalues hDimension i) * (t : ℝ)))) •
                ((hH.eigenvectorBasis hDimension) i)))
        (nhdsWithin 0 (Ioi 0))
        (nhds
          (∑ i : Fin dimension,
            inner ℝ ((hH.eigenvectorBasis hDimension) i) x •
              (hH.eigenvalues hDimension i •
                ((hH.eigenvectorBasis hDimension) i)))) := by
    refine tendsto_finset_sum _ fun i hi => ?_
    have hcoefficient :
        Tendsto
          (fun _ : NNReal =>
            inner ℝ ((hH.eigenvectorBasis hDimension) i) x)
          (nhdsWithin 0 (Ioi 0))
          (nhds (inner ℝ ((hH.eigenvectorBasis hDimension) i) x)) :=
      tendsto_const_nhds
    have hslope :=
      tendsto_nnreal_inv_mul_one_sub_exp_neg_mul
        (hH.eigenvalues hDimension i)
    have hbasis :
        Tendsto
          (fun _ : NNReal => (hH.eigenvectorBasis hDimension) i)
          (nhdsWithin 0 (Ioi 0))
          (nhds ((hH.eigenvectorBasis hDimension) i)) :=
      tendsto_const_nhds
    exact hcoefficient.smul (hslope.smul hbasis)
  apply hsum.congr'
  exact Filter.Eventually.of_forall fun t => by
    symm
    exact finiteDimensionalSymmetricHamiltonianSpectralSemigroup_differenceQuotient_eq_sum
      H hH dimension hDimension x t

end

end MathlibAnalytic
end MGAP4D
