import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricDoobDirectVariationMatrixData
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricDoobDirichletUniformGapBridge
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusStrictCouplingUniformCenteredRayleighPoincare
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

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
  simpa [variationMatrixData_coefficient] using hRayleigh

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
  have hSymm :
      inner ℝ (D.operator x) q = inner ℝ x (D.operator q) :=
    D.symmetric x q
  have hOrthogonal : inner ℝ x q = 0 := by
    rw [D.operator_apply_eigenbasis i.1, hqFixed,
      inner_smul_left] at hSymm
    have hNe : D.eigenvalue i.1 ≠ 1 := ne_of_lt i.2.2
    apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hNe)
    nlinarith [hSymm]
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
  rw [D.operator_apply_eigenbasis i.1, inner_smul_left,
    real_inner_self_eq_norm_sq] at hTransfer
  simpa [x] using hTransfer

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
