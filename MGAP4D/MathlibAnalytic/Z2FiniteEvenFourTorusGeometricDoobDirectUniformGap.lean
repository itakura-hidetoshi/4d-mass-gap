import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricDoobDirectVariationMatrixData
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricDoobDirichletUniformGapBridge
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusStrictCouplingUniformCenteredRayleighPoincare
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- An eigenbasis vector with eigenvalue strictly below one is orthogonal to
every fixed vector of a finite-dimensional real symmetric contraction. -/
theorem finiteDimensionalSymmetricPositiveContraction_eigenbasis_inner_fixed_eq_zero
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)
    (i : Fin D.dimension)
    (q : E)
    (hq : D.operator q = q)
    (hi : D.eigenvalue i < 1) :
    inner ℝ (D.eigenbasis i) q = 0 := by
  have hSymm :
      inner ℝ (D.operator (D.eigenbasis i)) q =
        inner ℝ (D.eigenbasis i) (D.operator q) :=
    D.symmetric (D.eigenbasis i) q
  rw [D.operator_apply_eigenbasis i, hq, inner_smul_left] at hSymm
  nlinarith

/-- The Rayleigh value of a normalized canonical eigenbasis vector is exactly
its eigenvalue. -/
theorem finiteDimensionalSymmetricPositiveContraction_eigenbasis_rayleigh_eq_eigenvalue
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)
    (i : Fin D.dimension) :
    inner ℝ (D.operator (D.eigenbasis i)) (D.eigenbasis i) =
      D.eigenvalue i := by
  rw [D.operator_apply_eigenbasis i, inner_smul_left]
  simp

/-- The compact direct-variation context at one finite side, with all physical
parameters and cutoff evidence inherited unchanged. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobDirectVariationContextAt
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) :
    Z2GeometricDoobDirectVariationContext where
  energyIdentity := energyIdentity
  energyNontrivial := energyNontrivial
  hEnergy := hEnergy
  β := β
  hβ := hβ
  hβCutoff := hβCutoff
  H := H

namespace Z2GeometricDoobDirectVariationContext

/-- The direct variation certificate gives the exact weighted mean-zero Doob
Rayleigh estimate with rate one half. -/
theorem weightedCenteredRayleigh_le_half
    (C : Z2GeometricDoobDirectVariationContext)
    (f : FiniteEvenFourTorusZ2SliceHilbert C.H)
    (hMean : C.doobData.weightedMean f = 0) :
    C.doobData.weightedDoobQuadratic f ≤
      (1 / 2 : ℝ) * C.doobData.weightedNormSq f := by
  have hRayleigh :=
    finiteProductDoob_centered_parallel_rayleigh_le
      C.doobData C.parallelVariationCertificate f hMean
  change C.doobData.weightedDoobQuadratic f ≤
    C.variationMatrixData.coefficient * C.doobData.weightedNormSq f
    at hRayleigh
  rw [C.variationMatrixData_coefficient] at hRayleigh
  exact hRayleigh

end Z2GeometricDoobDirectVariationContext

/-- Every strictly excited eigenvalue of the actual invariant one-slab
transfer is at most one half.  Orthogonality to the chosen positive Perron
ground follows from symmetry and the distinct eigenvalues `λ < 1` and `1`. -/
theorem finiteEvenFourTorusZ2GeometricDoobDirect_excitedEigenvalue_le_half
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ)
    (i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
      H β energyIdentity energyNontrivial hβ.le hEnergy.le) :
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ.le hEnergy.le).eigenvalue i.1 ≤
      (1 / 2 : ℝ) := by
  let D := finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ.le hEnergy.le
  let x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
    D.eigenbasis i.1
  have hGroundInvariant :=
    finiteEvenFourTorusZ2UnfixedGauge_fixedVector_mem_invariant
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_fixed
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
  let q : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
    ⟨finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
      H β energyIdentity energyNontrivial hβ.le hEnergy.le,
      hGroundInvariant⟩
  have hqFixed : D.operator q = q := by
    apply Subtype.ext
    exact finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_fixed
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  have hOrthogonal : inner ℝ x q = 0 := by
    simpa [x] using
      finiteDimensionalSymmetricPositiveContraction_eigenbasis_inner_fixed_eq_zero
        D i.1 q hqFixed i.2.2
  have hxGround :
      inner ℝ x.1
        (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ.le hEnergy.le) = 0 := by
    simpa [x, q] using hOrthogonal
  let C := finiteEvenFourTorusZ2GeometricDoobDirectVariationContextAt
    energyIdentity energyNontrivial hEnergy β hβ hβCutoff H
  have hTransfer :=
    finiteEvenFourTorusZ2UnfixedGaugeInvariant_transfer_rayleigh_le_of_weightedDoob
      H β energyIdentity energyNontrivial (1 / 2 : ℝ)
      hβ.le hEnergy.le
      (fun f hMean => C.weightedCenteredRayleigh_le_half f hMean)
      x hxGround
  change inner ℝ (D.operator x) x ≤ (1 / 2 : ℝ) * ‖x‖ ^ 2 at hTransfer
  have hEigenRayleigh :
      inner ℝ (D.operator x) x = D.eigenvalue i.1 := by
    simpa [x] using
      finiteDimensionalSymmetricPositiveContraction_eigenbasis_rayleigh_eq_eigenvalue
        D i.1
  calc
    D.eigenvalue i.1 = inner ℝ (D.operator x) x := hEigenRayleigh.symm
    _ ≤ (1 / 2 : ℝ) * ‖x‖ ^ 2 := hTransfer
    _ = 1 / 2 := by simp [x]

/-- The actual geometric Perron--Doob direct response therefore supplies a
volume-independent strict spectral cap with exact rate one half. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobDirectUniformSpectralCap
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy) :
    Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate
      β energyIdentity energyNontrivial hβ hEnergy where
  rate := 1 / 2
  rate_pos := by norm_num
  rate_lt_one := by norm_num
  excitedEigenvalue_le_rate :=
    finiteEvenFourTorusZ2GeometricDoobDirect_excitedEigenvalue_le_half
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff

/-- The spectral cap gives the repository's canonical ground-coordinate
centered Rayleigh estimate at the same exact rate one half. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobDirectUniformCenteredRayleigh
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy) :
    Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate
      β energyIdentity energyNontrivial hβ hEnergy :=
  (finiteEvenFourTorusZ2GeometricDoobDirectUniformSpectralCap
    energyIdentity energyNontrivial hEnergy β hβ hβCutoff).toCenteredRayleighCertificate

@[simp] theorem finiteEvenFourTorusZ2GeometricDoobDirectUniformCenteredRayleigh_rate
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy) :
    (finiteEvenFourTorusZ2GeometricDoobDirectUniformCenteredRayleigh
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff).rate =
      (1 / 2 : ℝ) := rfl

/-- Exact Dirichlet coercivity one half for the actual geometric Doob chain,
now expressed on the repository's canonical ground-coordinate centered sector. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobDirectUniformPoincare
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy) :
    Z2UnfixedGaugeGeometricDoobUniformPoincareCertificate
      β energyIdentity energyNontrivial hβ hEnergy where
  coercivity := 1 / 2
  coercivity_pos := by norm_num
  coercivity_lt_one := by norm_num
  centeredPoincare := by
    intro H x hx
    let D := finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
    let f := D.unweight x.1
    have hRayleigh :=
      (finiteEvenFourTorusZ2GeometricDoobDirectUniformCenteredRayleigh
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff).centeredRayleigh
        H x hx
    rw [finiteEvenFourTorusZ2UnfixedGaugeGeometricDoobDirichletForm_eq]
    change (1 / 2 : ℝ) * D.weightedNormSq f ≤
      D.weightedNormSq f - D.weightedDoobQuadratic f
    rw [D.weightedDoobQuadratic_eq_transfer_inner,
      D.weightedNormSq_eq_norm_sq, D.weightedVector_unweight]
    change (1 / 2 : ℝ) * ‖x.1‖ ^ 2 ≤
      ‖x.1‖ ^ 2 -
        inner ℝ
          (finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
            H β energyIdentity energyNontrivial hβ.le hEnergy.le x.1) x.1
    change inner ℝ
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
          H β energyIdentity energyNontrivial hβ.le hEnergy.le x.1) x.1 ≤
      (1 / 2 : ℝ) * ‖x.1‖ ^ 2 at hRayleigh
    linarith

/-- Terminal complete package: the exact actual geometric Doob row has a
volume-independent Dirichlet coercivity one half and hence closes the complete
finite-volume full-transfer uniform-gap package on the same direct-response
cutoff interval. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobDirectUniformGapPackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy) :
    Z2FiniteEvenFourTorusSpatialSandwichStabilityCompletePackage
      β energyIdentity energyNontrivial hβ hEnergy :=
  finiteEvenFourTorusZ2GeometricDoobDirichletUniformGapBridge
    β energyIdentity energyNontrivial hβ hEnergy
    (finiteEvenFourTorusZ2GeometricDoobDirectUniformPoincare
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff)

end

end MathlibAnalytic
end MGAP4D
