import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronGroundSimplicity
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeFullSpectralCompletePackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The canonical eigenvalue-one spectral index of the actual compressed
unfixed-gauge finite `Z₂` transfer is subsingleton. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex_subsingleton
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Subsingleton
      ((finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        H β energyIdentity energyNontrivial hβ hEnergy).GroundSpectralIndex) := by
  let D := finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy
  obtain ⟨p, _hpne, _hppos, _hpfix, hpgen⟩ :=
    finiteEvenFourTorusZ2UnfixedGaugeInvariant_fixed_space_generated_by_positiveGround
      H β energyIdentity energyNontrivial hβ hEnergy
  constructor
  intro i j
  have hifix : D.operator (D.eigenbasis i.1) = D.eigenbasis i.1 := by
    rw [D.operator_apply_eigenbasis i.1, i.2, one_smul]
  have hjfix : D.operator (D.eigenbasis j.1) = D.eigenbasis j.1 := by
    rw [D.operator_apply_eigenbasis j.1, j.2, one_smul]
  obtain ⟨a, ha⟩ := hpgen (D.eigenbasis i.1) hifix
  obtain ⟨b, hb⟩ := hpgen (D.eigenbasis j.1) hjfix
  have hpne : p ≠ 0 := by
    intro hpzero
    have hibasis : D.eigenbasis i.1 ≠ 0 :=
      D.eigenbasis_orthonormal.ne_zero i.1
    apply hibasis
    rw [ha, hpzero]
    simp
  have hane : a ≠ 0 := by
    intro hazero
    have hibasis : D.eigenbasis i.1 ≠ 0 :=
      D.eigenbasis_orthonormal.ne_zero i.1
    apply hibasis
    rw [ha, hazero]
    simp
  have hrelation : a • D.eigenbasis j.1 = b • D.eigenbasis i.1 := by
    rw [hb, ha]
    simp [smul_smul, mul_comm]
  have hindex : j.1 = i.1 :=
    D.eigenbasis_orthonormal.linearIndependent
      |>.eq_of_smul_apply_eq_smul_apply
        a b j.1 i.1 hane hrelation
  exact Subtype.ext hindex

/-- The actual canonical ground spectral index is inhabited and unique. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex_unique
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Nonempty
      ((finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        H β energyIdentity energyNontrivial hβ hEnergy).GroundSpectralIndex) ∧
    Subsingleton
      ((finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        H β energyIdentity energyNontrivial hβ hEnergy).GroundSpectralIndex) :=
  ⟨finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex_nonempty
      H β energyIdentity energyNontrivial hβ hEnergy,
    finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex_subsingleton
      H β energyIdentity energyNontrivial hβ hEnergy⟩

/-- Perron simplicity is compatible with the previously constructed complete
actual ground/excited/null decomposition package. -/
structure Z2UnfixedGaugePerronGroundCompletePackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  fullSpectralPackage :
    Z2UnfixedGaugeFullSpectralCompletePackage
      β energyIdentity energyNontrivial hβ hEnergy
  positiveGround :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H
  positiveGround_ne_zero : positiveGround ≠ 0
  positiveGround_pointwisePositive :
    FiniteBoundaryPointwisePositive positiveGround.1
  positiveGround_fixed :
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy positiveGround =
        positiveGround
  fixed_space_generated :
    ∀ g : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy g = g →
        ∃ c : ℝ, g = c • positiveGround
  canonicalGroundIndex_nonempty :
    Nonempty
      ((finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        H β energyIdentity energyNontrivial hβ hEnergy).GroundSpectralIndex)
  canonicalGroundIndex_subsingleton :
    Subsingleton
      ((finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        H β energyIdentity energyNontrivial hβ hEnergy).GroundSpectralIndex)

/-- Bundle the actual full spectral package with Perron ground-state
simplicity.  The prior full package is side-two; the Perron ground result is
proved at every finite side parameter `H`. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugePerronGroundCompletePackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2UnfixedGaugePerronGroundCompletePackage
      H β energyIdentity energyNontrivial hβ hEnergy := by
  obtain ⟨p, hpne, hppos, hpfix, hpgen⟩ :=
    finiteEvenFourTorusZ2UnfixedGaugeInvariant_fixed_space_generated_by_positiveGround
      H β energyIdentity energyNontrivial hβ hEnergy
  exact
    { fullSpectralPackage :=
        finiteEvenFourTorusZ2UnfixedGaugeFullSpectralCompletePackage
          β energyIdentity energyNontrivial hβ hEnergy
      positiveGround := p
      positiveGround_ne_zero := hpne
      positiveGround_pointwisePositive := hppos
      positiveGround_fixed := hpfix
      fixed_space_generated := hpgen
      canonicalGroundIndex_nonempty :=
        finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex_nonempty
          H β energyIdentity energyNontrivial hβ hEnergy
      canonicalGroundIndex_subsingleton :=
        finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex_subsingleton
          H β energyIdentity energyNontrivial hβ hEnergy }

end

end MathlibAnalytic
end MGAP4D
