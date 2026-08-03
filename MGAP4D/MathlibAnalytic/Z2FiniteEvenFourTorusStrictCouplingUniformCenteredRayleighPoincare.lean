import MGAP4D.MathlibAnalytic.FiniteDimensionalUniqueGroundCenteredRayleigh
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusStrictCouplingUniformSpectralCap
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronGroundSpectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- A volume-independent, basis-free Rayleigh contraction on the actual
strict-coupling `Z₂` transfer after removing its unique ground coordinate. -/
structure Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  rate : ℝ
  rate_pos : 0 < rate
  rate_lt_one : rate < 1
  centeredRayleigh :
    ∀ (H : ℕ)
      (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H),
      finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates
          H β energyIdentity energyNontrivial hβ.le hEnergy.le x = 0 →
        inner ℝ
            (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
              H β energyIdentity energyNontrivial hβ.le hEnergy.le x) x ≤
          rate * ‖x‖ ^ 2

namespace Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate

variable
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (R : Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate
      β energyIdentity energyNontrivial hβ hEnergy)

/-- The centered Rayleigh estimate bounds every actual excited transfer
eigenvalue by the same rate. -/
noncomputable def toSpectralCapCertificate :
    Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate
      β energyIdentity energyNontrivial hβ hEnergy where
  rate := R.rate
  rate_pos := R.rate_pos
  rate_lt_one := R.rate_lt_one
  excitedEigenvalue_le_rate := by
    intro H i
    let D := finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
    letI : Nonempty D.GroundSpectralIndex :=
      finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex_nonempty
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
    have hcenter : D.groundCoordinates (D.eigenbasis i.1) = 0 := by
      ext j
      change D.eigenbasis.repr (D.eigenbasis i.1) j.1 = 0
      have hne : j.1 ≠ i.1 := by
        intro hji
        have hground : D.eigenvalue i.1 = 1 := by
          simpa [hji] using j.2
        exact (ne_of_lt i.2.2) hground
      simp [hne]
    have hRayleigh := R.centeredRayleigh H (D.eigenbasis i.1) (by
      change D.groundCoordinates (D.eigenbasis i.1) = 0
      exact hcenter)
    change
      inner ℝ (D.operator (D.eigenbasis i.1)) (D.eigenbasis i.1) ≤
        R.rate * ‖D.eigenbasis i.1‖ ^ 2 at hRayleigh
    exact D.excited_eigenvalue_le_of_operator_quadraticForm_le_on_canonicalGroundOrthogonal
      R.rate (by
        intro x hx
        apply R.centeredRayleigh H x
        change D.groundCoordinates x = 0
        ext j
        have hground :
            (⟨j.1, j.2⟩ : D.GroundSpectralIndex) =
              D.canonicalGroundIndex :=
          Subsingleton.elim _ _
        have hindex : j.1 = D.canonicalGroundIndex.1 :=
          congrArg Subtype.val hground
        have hx' := hx
        change inner ℝ (D.eigenbasis D.canonicalGroundIndex.1) x = 0 at hx'
        change D.eigenbasis.repr x j.1 = 0
        rw [D.eigenbasis.repr_apply, hindex]
        exact hx') i

/-- The spectral cap generated from centered Rayleigh data retains the supplied
rate exactly. -/
theorem toSpectralCapCertificate_rate_eq :
    R.toSpectralCapCertificate.rate = R.rate :=
  rfl

end Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate

namespace Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate

variable
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate
      β energyIdentity energyNontrivial hβ hEnergy)

/-- A common excited spectral cap generates a basis-free centered Rayleigh
contraction for the actual transfer at every finite volume. -/
noncomputable def toCenteredRayleighCertificate :
    Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate
      β energyIdentity energyNontrivial hβ hEnergy where
  rate := C.rate
  rate_pos := C.rate_pos
  rate_lt_one := C.rate_lt_one
  centeredRayleigh := by
    intro H x hx
    let D := finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
    letI : Nonempty D.GroundSpectralIndex :=
      finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex_nonempty
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
    letI : Subsingleton D.GroundSpectralIndex :=
      finiteEvenFourTorusZ2UnfixedGaugeGroundSpectralIndex_subsingleton
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
    have hnull : ¬ Nonempty D.NullSpectralIndex :=
      finiteEvenFourTorusZ2UnfixedGaugeNullSpectralIndex_not_nonempty_strict
        H β energyIdentity energyNontrivial hβ hEnergy
    have hxorth : inner ℝ D.canonicalGroundVector x = 0 := by
      have hcoord := congrArg
        (fun y : D.GroundSpectralSpace => y D.canonicalGroundIndex) hx
      change D.eigenbasis.repr x D.canonicalGroundIndex.1 = 0 at hcoord
      simpa [FiniteDimensionalSymmetricPositiveContractionData.canonicalGroundVector]
        using hcoord
    change inner ℝ (D.operator x) x ≤ C.rate * ‖x‖ ^ 2
    exact
      D.operator_quadraticForm_le_on_canonicalGroundOrthogonal_of_excited_cap
        hnull C.rate C.rate_pos.le
        (fun i => C.excitedEigenvalue_le_rate H i) x hxorth

/-- The centered Rayleigh certificate generated from a spectral cap retains the
same rate. -/
theorem toCenteredRayleighCertificate_rate_eq :
    C.toCenteredRayleighCertificate.rate = C.rate :=
  rfl

end Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate

/-- A volume-independent Poincare/Dirichlet coercivity estimate for the actual
one-step transfer defect `I - T_H` on the unique-ground-centered sector. -/
structure Z2UnfixedGaugeStrictCouplingUniformCenteredPoincareCertificate
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  coercivity : ℝ
  coercivity_pos : 0 < coercivity
  coercivity_lt_one : coercivity < 1
  centeredPoincare :
    ∀ (H : ℕ)
      (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H),
      finiteEvenFourTorusZ2UnfixedGaugeGroundCoordinates
          H β energyIdentity energyNontrivial hβ.le hEnergy.le x = 0 →
        coercivity * ‖x‖ ^ 2 ≤
          inner ℝ
            (x - finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
              H β energyIdentity energyNontrivial hβ.le hEnergy.le x) x

namespace Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate

variable
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (R : Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate
      β energyIdentity energyNontrivial hβ hEnergy)

/-- Rayleigh contraction and Poincare coercivity are the same estimate after
the exact change of variables `coercivity = 1 - rate`. -/
noncomputable def toCenteredPoincareCertificate :
    Z2UnfixedGaugeStrictCouplingUniformCenteredPoincareCertificate
      β energyIdentity energyNontrivial hβ hEnergy where
  coercivity := 1 - R.rate
  coercivity_pos := sub_pos.mpr R.rate_lt_one
  coercivity_lt_one := by linarith [R.rate_pos]
  centeredPoincare := by
    intro H x hx
    have hRayleigh := R.centeredRayleigh H x hx
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
    linarith

@[simp] theorem toCenteredPoincareCertificate_coercivity :
    R.toCenteredPoincareCertificate.coercivity = 1 - R.rate :=
  rfl

end Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate

namespace Z2UnfixedGaugeStrictCouplingUniformCenteredPoincareCertificate

variable
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (P : Z2UnfixedGaugeStrictCouplingUniformCenteredPoincareCertificate
      β energyIdentity energyNontrivial hβ hEnergy)

/-- Poincare coercivity gives the exactly dual centered Rayleigh contraction
with `rate = 1 - coercivity`. -/
noncomputable def toCenteredRayleighCertificate :
    Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate
      β energyIdentity energyNontrivial hβ hEnergy where
  rate := 1 - P.coercivity
  rate_pos := sub_pos.mpr P.coercivity_lt_one
  rate_lt_one := by linarith [P.coercivity_pos]
  centeredRayleigh := by
    intro H x hx
    have hPoincare := P.centeredPoincare H x hx
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at hPoincare
    linarith

/-- Poincare coercivity therefore generates the common excited spectral cap. -/
noncomputable def toSpectralCapCertificate :
    Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate
      β energyIdentity energyNontrivial hβ hEnergy :=
  P.toCenteredRayleighCertificate.toSpectralCapCertificate

@[simp] theorem toCenteredRayleighCertificate_rate :
    P.toCenteredRayleighCertificate.rate = 1 - P.coercivity :=
  rfl

@[simp] theorem toSpectralCapCertificate_rate :
    P.toSpectralCapCertificate.rate = 1 - P.coercivity :=
  rfl

end Z2UnfixedGaugeStrictCouplingUniformCenteredPoincareCertificate

namespace Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate

variable
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate
      β energyIdentity energyNontrivial hβ hEnergy)

/-- A common spectral cap also generates the exactly dual Poincare estimate. -/
noncomputable def toCenteredPoincareCertificate :
    Z2UnfixedGaugeStrictCouplingUniformCenteredPoincareCertificate
      β energyIdentity energyNontrivial hβ hEnergy :=
  C.toCenteredRayleighCertificate.toCenteredPoincareCertificate

@[simp] theorem toCenteredPoincareCertificate_coercivity :
    C.toCenteredPoincareCertificate.coercivity = 1 - C.rate :=
  rfl

end Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate

/-- Existence of a common spectral cap is exactly equivalent to existence of a
basis-free centered Rayleigh contraction for the actual family. -/
theorem z2UnfixedGaugeStrictCoupling_uniformCenteredRayleigh_iff_uniformSpectralCap
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    Nonempty
        (Z2UnfixedGaugeStrictCouplingUniformCenteredRayleighCertificate
          β energyIdentity energyNontrivial hβ hEnergy) ↔
      Nonempty
        (Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate
          β energyIdentity energyNontrivial hβ hEnergy) := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.toSpectralCapCertificate⟩
  · rintro ⟨C⟩
    exact ⟨C.toCenteredRayleighCertificate⟩

/-- The same common spectral cap is exactly equivalent to a volume-independent
centered Poincare/Dirichlet coercivity estimate for `I - T_H`. -/
theorem z2UnfixedGaugeStrictCoupling_uniformCenteredPoincare_iff_uniformSpectralCap
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    Nonempty
        (Z2UnfixedGaugeStrictCouplingUniformCenteredPoincareCertificate
          β energyIdentity energyNontrivial hβ hEnergy) ↔
      Nonempty
        (Z2UnfixedGaugeStrictCouplingUniformSpectralCapCertificate
          β energyIdentity energyNontrivial hβ hEnergy) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.toSpectralCapCertificate⟩
  · rintro ⟨C⟩
    exact ⟨C.toCenteredPoincareCertificate⟩

end

end MathlibAnalytic
end MGAP4D
