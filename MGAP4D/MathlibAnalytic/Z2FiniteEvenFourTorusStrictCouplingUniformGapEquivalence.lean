import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusStrictCouplingUniformSpectralCap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A proof-relevant witness of one strictly positive excitation-energy floor
valid at every finite side parameter. -/
structure Z2UnfixedGaugeStrictCouplingUniformGapWitness
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  gap : ℝ
  gap_pos : 0 < gap
  gap_le_atVolume :
    ∀ H : ℕ,
      gap ≤ finiteEvenFourTorusZ2UnfixedGaugeStrictExcitationGapAt
        H β energyIdentity energyNontrivial hβ hEnergy

namespace Z2UnfixedGaugeStrictCouplingUniformGapWitness

variable
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (W : Z2UnfixedGaugeStrictCouplingUniformGapWitness
      β energyIdentity energyNontrivial hβ hEnergy)

/-- A common positive energy floor gives a common excited-transfer cap by the
exact relation `λ = exp (-E)`. -/
noncomputable def toSpectralCapCertificate :
    Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate
      β energyIdentity energyNontrivial hβ hEnergy where
  rate := Real.exp (-W.gap)
  rate_pos := Real.exp_pos _
  rate_lt_one := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_neg_of_pos W.gap_pos)
  excitedEigenvalue_le_rate := by
    intro H i
    let D := finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
    have hgapEnergy :
        W.gap ≤ D.positiveSpectralEnergy i.toPositive :=
      le_trans (W.gap_le_atVolume H)
        (Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate.
          finiteEvenFourTorusZ2UnfixedGaugeStrictExcitationGapAt_le_excitedEnergy
            (β := β) (energyIdentity := energyIdentity)
            (energyNontrivial := energyNontrivial)
            (hβ := hβ) (hEnergy := hEnergy) H i)
    change D.positiveEigenvalue i.toPositive ≤ Real.exp (-W.gap)
    rw [← D.exp_neg_positiveSpectralEnergy i.toPositive]
    exact Real.exp_le_exp.mpr (neg_le_neg hgapEnergy)

/-- Recovering the common gap from the exponential spectral cap returns the
original witness value exactly. -/
theorem toSpectralCapCertificate_uniformExcitationGap_eq :
    W.toSpectralCapCertificate.uniformExcitationGap = W.gap := by
  simp [toSpectralCapCertificate,
    Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate.uniformExcitationGap,
    Real.log_exp]

end Z2UnfixedGaugeStrictCouplingUniformGapWitness

namespace Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate

variable
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate
      β energyIdentity energyNontrivial hβ hEnergy)

/-- Every common spectral cap canonically produces a proof-relevant uniform-gap
witness. -/
noncomputable def toUniformGapWitness :
    Z2UnfixedGaugeStrictCouplingUniformGapWitness
      β energyIdentity energyNontrivial hβ hEnergy where
  gap := C.uniformExcitationGap
  gap_pos := C.uniformExcitationGap_pos
  gap_le_atVolume := C.uniformExcitationGap_le_strictExcitationGapAt

/-- Converting a spectral cap to its energy floor and back recovers the exact
spectral rate. -/
theorem toUniformGapWitness_toSpectralCapCertificate_rate_eq :
    C.toUniformGapWitness.toSpectralCapCertificate.rate = C.rate := by
  exact C.exp_neg_uniformExcitationGap

end Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate

/-- Existence of a strict common excited-transfer cap is equivalent to the
precise positive uniform finite-volume excitation-gap statement. -/
theorem z2UnfixedGaugeStrictCoupling_uniformSpectralCap_iff_uniformGap
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    Nonempty
        (Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate
          β energyIdentity energyNontrivial hβ hEnergy) ↔
      Nonempty
        (Z2UnfixedGaugeStrictCouplingUniformGapWitness
          β energyIdentity energyNontrivial hβ hEnergy) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.toUniformGapWitness⟩
  · rintro ⟨W⟩
    exact ⟨W.toSpectralCapCertificate⟩

/-- Proposition-level form of the exact family-uniform gap statement. -/
def Z2UnfixedGaugeStrictCouplingHasUniformGap
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) : Prop :=
  ∃ Δstar : ℝ,
    0 < Δstar ∧
    ∀ H : ℕ,
      Δstar ≤ finiteEvenFourTorusZ2UnfixedGaugeStrictExcitationGapAt
        H β energyIdentity energyNontrivial hβ hEnergy

/-- The proof-relevant witness and the direct existential statement are exactly
equivalent. -/
theorem z2UnfixedGaugeStrictCoupling_uniformGapWitness_iff_hasUniformGap
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    Nonempty
        (Z2UnfixedGaugeStrictCouplingUniformGapWitness
          β energyIdentity energyNontrivial hβ hEnergy) ↔
      Z2UnfixedGaugeStrictCouplingHasUniformGap
        β energyIdentity energyNontrivial hβ hEnergy := by
  constructor
  · rintro ⟨W⟩
    exact ⟨W.gap, W.gap_pos, W.gap_le_atVolume⟩
  · rintro ⟨gap, gap_pos, gap_le_atVolume⟩
    exact ⟨{
      gap := gap
      gap_pos := gap_pos
      gap_le_atVolume := gap_le_atVolume }⟩

/-- Final exact characterization: the outstanding family-uniform gap is
neither hidden nor weakened; it is precisely equivalent to producing one
volume-independent cap below one for all actual excited transfer eigenvalues. -/
theorem z2UnfixedGaugeStrictCoupling_hasUniformGap_iff_uniformSpectralCap
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    Z2UnfixedGaugeStrictCouplingHasUniformGap
        β energyIdentity energyNontrivial hβ hEnergy ↔
      Nonempty
        (Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate
          β energyIdentity energyNontrivial hβ hEnergy) := by
  rw [← z2UnfixedGaugeStrictCoupling_uniformGapWitness_iff_hasUniformGap]
  exact
    (z2UnfixedGaugeStrictCoupling_uniformSpectralCap_iff_uniformGap
      β energyIdentity energyNontrivial hβ hEnergy).symm

end

end MathlibAnalytic
end MGAP4D
