import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeSpectralResolution
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Positive-support transfer of the actual Gauss-invariant unfixed-gauge
finite `Z₂` one-slab transfer. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralTransfer
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy →L[ℝ]
      FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).positiveSpectralTransfer

/-- Support energy `-log λ` of an actual positive transfer eigenmode. -/
def finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (i : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralIndex
      H β energyIdentity energyNontrivial hβ hEnergy) : ℝ :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).positiveSpectralEnergy i

/-- Hamiltonian on the nonzero spectral support of the actual finite transfer. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeSupportHamiltonian
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy →L[ℝ]
      FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).positiveSpectralHamiltonian

/-- Natural-time support semigroup of the actual finite transfer. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSemigroup
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (n : ℕ) :
    FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy →L[ℝ]
      FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).positiveSpectralSemigroup n

/-- Synthesis of actual positive-support coordinates into the Gauss-invariant
slice Hilbert space. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSynthesis
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
        H β energyIdentity energyNontrivial hβ hEnergy →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).positiveSpectralSynthesis

/-- Every actual support energy is nonnegative. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (i : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralIndex
      H β energyIdentity energyNontrivial hβ hEnergy) :
    0 ≤ finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
      H β energyIdentity energyNontrivial hβ hEnergy i :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).positiveSpectralEnergy_nonneg i

/-- Exponentiating minus an actual support energy recovers the exact transfer
eigenvalue on that mode. -/
theorem finiteEvenFourTorusZ2UnfixedGauge_exp_neg_supportEnergy
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (i : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralIndex
      H β energyIdentity energyNontrivial hβ hEnergy) :
    Real.exp
        (-finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
          H β energyIdentity energyNontrivial hβ hEnergy i) =
      finiteEvenFourTorusZ2UnfixedGaugeInvariantEigenvalue
        H β energyIdentity energyNontrivial hβ hEnergy i.1 :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).exp_neg_positiveSpectralEnergy i

/-- Additive natural time is composition on the actual positive support. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSemigroup_add
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (m n : ℕ) :
    finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSemigroup
        H β energyIdentity energyNontrivial hβ hEnergy (m + n) =
      (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSemigroup
        H β energyIdentity energyNontrivial hβ hEnergy m).comp
      (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSemigroup
        H β energyIdentity energyNontrivial hβ hEnergy n) :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).positiveSpectralSemigroup_add m n

/-- The actual transfer intertwines exactly with its support transfer under
spectral synthesis. -/
theorem finiteEvenFourTorusZ2UnfixedGauge_supportTransfer_intertwining
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (x : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
      H β energyIdentity energyNontrivial hβ hEnergy) :
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSynthesis
          H β energyIdentity energyNontrivial hβ hEnergy x) =
      finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSynthesis
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralTransfer
          H β energyIdentity energyNontrivial hβ hEnergy x) :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).operator_positiveSpectralSynthesis_intertwining x

/-- Every natural power of the actual transfer intertwines with the support
Hamiltonian semigroup. -/
theorem finiteEvenFourTorusZ2UnfixedGauge_supportSemigroup_intertwining
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (n : ℕ)
    (x : FiniteEvenFourTorusZ2UnfixedGaugePositiveSpectralSpace
      H β energyIdentity energyNontrivial hβ hEnergy) :
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy) ^ n
        (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSynthesis
          H β energyIdentity energyNontrivial hβ hEnergy x) =
      finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSynthesis
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralSemigroup
          H β energyIdentity energyNontrivial hβ hEnergy n x) :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ hEnergy).operator_pow_positiveSpectralSynthesis_intertwining n x

end

end MathlibAnalytic
end MGAP4D
