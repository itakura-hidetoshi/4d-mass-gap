import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanGreenPoissonUniqueDualMaximizersL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- Restrict an equivalence to matching level sets of two compatible scalar
observables. -/
def equivRestrictToLevelSets
    {α β γ : Type*}
    (e : α ≃ β)
    (p : α → γ)
    (q : β → γ)
    (hcompat : ∀ x : α, q (e x) = p x)
    (c : γ) :
    {x : α // p x = c} ≃ {y : β // q y = c} where
  toFun x := ⟨e x.1, (hcompat x.1).trans x.2⟩
  invFun y :=
    ⟨e.symm y.1, by
      have h : q y.1 = p (e.symm y.1) := by
        simpa using hcompat (e.symm y.1)
      exact h.symm.trans y.2⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply y.1

local notation "Ω₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2
local notation "A₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
local notation "G₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
local notation "GE₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
local notation "PE₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
local notation "GW₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
local notation "PW₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2

/-- The actual centered Green operator and Poisson operator form an equivalence
on the beta-zero vacuum-orthogonal sector. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenEquivL2 :
    Ω₀ ≃ Ω₀ where
  toFun := G₀
  invFun := A₀
  left_inv :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply_centeredGreen_eq_self
  right_inv :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_poisson_eq_self

/-- The Green-energy unit sphere on the actual beta-zero centered sector. -/
abbrev periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyUnitSphereL2 :=
  {f : Ω₀ // GE₀ f = 1}

/-- The Poisson-energy unit sphere on the actual beta-zero centered sector. -/
abbrev periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyUnitSphereL2 :=
  {u : Ω₀ // PE₀ u = 1}

local notation "GS₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyUnitSphereL2
local notation "PS₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyUnitSphereL2

/-- Green and Poisson restrict to mutually inverse maps between their exact
energy unit spheres. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereEquivL2 :
    GS₀ ≃ PS₀ :=
  equivRestrictToLevelSets
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenEquivL2
    GE₀
    PE₀
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_centeredGreen_eq_greenEnergyNorm
    1

@[simp] theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenPoissonEnergyUnitSphereEquivL2_apply_coe
    (f : GS₀) :
    ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereEquivL2
      f : PS₀) : Ω₀) = G₀ (f : Ω₀) :=
  rfl

@[simp] theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenPoissonEnergyUnitSphereEquivL2_symm_apply_coe
    (u : PS₀) :
    ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereEquivL2.symm
      u : GS₀) : Ω₀) = A₀ (u : Ω₀) :=
  rfl

/-- Green energy one forces a nonzero vector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_ne_zero_of_greenEnergyNorm_eq_one
    (f : Ω₀)
    (hf : GE₀ f = 1) :
    f ≠ 0 := by
  intro hZero
  have hEnergyZero : GE₀ f = 0 :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_eq_zero_iff
      f).2 hZero
  rw [hf] at hEnergyZero
  norm_num at hEnergyZero

/-- Poisson energy one forces a nonzero vector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_ne_zero_of_poissonEnergyNorm_eq_one
    (u : Ω₀)
    (hu : PE₀ u = 1) :
    u ≠ 0 := by
  intro hZero
  have hEnergyZero : PE₀ u = 0 :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_eq_zero_iff
      u).2 hZero
  rw [hu] at hEnergyZero
  norm_num at hEnergyZero

/-- Composing the normalized Green witness with the normalized Poisson witness
returns the Green-energy normalization of the original datum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_poissonDualUnitWitness_greenDualUnitWitness_eq_greenNormalize
    (f : Ω₀)
    (hf : f ≠ 0) :
    PW₀ (GW₀ f) = (GE₀ f)⁻¹ • f := by
  change (PE₀ (GW₀ f))⁻¹ • A₀ (GW₀ f) = (GE₀ f)⁻¹ • f
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenDualUnitWitnessL2_poissonEnergy_eq_one
      f hf]
  norm_num
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenDualUnitWitnessL2
  rw [map_smul]
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply_centeredGreen_eq_self]

/-- Composing the normalized Poisson witness with the normalized Green witness
returns the Poisson-energy normalization of the original state. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenDualUnitWitness_poissonDualUnitWitness_eq_poissonNormalize
    (u : Ω₀)
    (hu : u ≠ 0) :
    GW₀ (PW₀ u) = (PE₀ u)⁻¹ • u := by
  change (GE₀ (PW₀ u))⁻¹ • G₀ (PW₀ u) = (PE₀ u)⁻¹ • u
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDualUnitWitnessL2_greenEnergy_eq_one
      u hu]
  norm_num
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDualUnitWitnessL2
  rw [map_smul]
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_poisson_eq_self]

/-- On the Green-energy unit sphere, the two normalized duality maps compose to
the identity. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_poissonDualUnitWitness_greenDualUnitWitness_eq_self_of_greenEnergyNorm_eq_one
    (f : Ω₀)
    (hf : GE₀ f = 1) :
    PW₀ (GW₀ f) = f := by
  have hfNe :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_ne_zero_of_greenEnergyNorm_eq_one
      f hf
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_poissonDualUnitWitness_greenDualUnitWitness_eq_greenNormalize
      f hfNe,
    hf]
  norm_num

/-- On the Poisson-energy unit sphere, the two normalized duality maps compose
to the identity. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenDualUnitWitness_poissonDualUnitWitness_eq_self_of_poissonEnergyNorm_eq_one
    (u : Ω₀)
    (hu : PE₀ u = 1) :
    GW₀ (PW₀ u) = u := by
  have huNe :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_ne_zero_of_poissonEnergyNorm_eq_one
      u hu
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenDualUnitWitness_poissonDualUnitWitness_eq_poissonNormalize
      u huNe,
    hu]
  norm_num

/-- Every Green-energy unit vector pairs to one with its image on the
Poisson-energy unit sphere. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_greenPoissonEnergyUnitSphereEquivL2_apply_eq_one
    (f : GS₀) :
    inner ℝ (f : Ω₀)
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereEquivL2
          f : Ω₀) = 1 := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenPoissonEnergyUnitSphereEquivL2_apply_coe]
  calc
    inner ℝ (f : Ω₀) (G₀ (f : Ω₀)) =
        inner ℝ (G₀ (f : Ω₀)) (f : Ω₀) := real_inner_comm _ _
    _ = GE₀ (f : Ω₀) ^ 2 :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_sq
        (f : Ω₀)).symm
    _ = 1 := by rw [f.property]; norm_num

/-- Every Poisson-energy unit vector pairs to one with its inverse image on the
Green-energy unit sphere. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_greenPoissonEnergyUnitSphereEquivL2_symm_apply_eq_one
    (u : PS₀) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereEquivL2.symm
          u : Ω₀)
        (u : Ω₀) = 1 := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenPoissonEnergyUnitSphereEquivL2_symm_apply_coe]
  calc
    inner ℝ (A₀ (u : Ω₀)) (u : Ω₀) = PE₀ (u : Ω₀) ^ 2 :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_sq
        (u : Ω₀)).symm
    _ = 1 := by rw [u.property]; norm_num

/-- On the two unit spheres, pairing one characterizes exactly the Green image. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_poissonEnergyUnitSphere_inner_eq_one_iff
    (f : GS₀)
    (u : PS₀) :
    inner ℝ (f : Ω₀) (u : Ω₀) = 1 ↔
      u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereEquivL2
          f := by
  have hfNe :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_ne_zero_of_greenEnergyNorm_eq_one
      (f : Ω₀) f.property
  constructor
  · intro hPair
    have hRaw :
        (u : Ω₀) = GW₀ (f : Ω₀) :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_poissonEnergy_le_one_and_inner_eq_greenEnergyNorm_iff_eq_greenDualUnitWitnessL2
        (f : Ω₀) (u : Ω₀) hfNe).1
        ⟨le_of_eq u.property, by simpa [f.property] using hPair⟩
    apply Subtype.ext
    calc
      (u : Ω₀) = GW₀ (f : Ω₀) := hRaw
      _ = (GE₀ (f : Ω₀))⁻¹ • G₀ (f : Ω₀) := rfl
      _ = G₀ (f : Ω₀) := by rw [f.property]; norm_num
      _ =
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereEquivL2
            f : Ω₀) := by rfl
  · intro hEq
    subst u
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_greenPoissonEnergyUnitSphereEquivL2_apply_eq_one
        f

/-- On the two unit spheres, pairing one characterizes exactly the Poisson
inverse image. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenEnergyUnitSphere_inner_eq_one_iff
    (f : GS₀)
    (u : PS₀) :
    inner ℝ (f : Ω₀) (u : Ω₀) = 1 ↔
      f =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereEquivL2.symm
          u := by
  have huNe :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_ne_zero_of_poissonEnergyNorm_eq_one
      (u : Ω₀) u.property
  constructor
  · intro hPair
    have hRaw :
        (f : Ω₀) = PW₀ (u : Ω₀) :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenEnergy_le_one_and_inner_eq_poissonEnergyNorm_iff_eq_poissonDualUnitWitnessL2
        (f : Ω₀) (u : Ω₀) huNe).1
        ⟨le_of_eq f.property, by simpa [u.property] using hPair⟩
    apply Subtype.ext
    calc
      (f : Ω₀) = PW₀ (u : Ω₀) := hRaw
      _ = (PE₀ (u : Ω₀))⁻¹ • A₀ (u : Ω₀) := rfl
      _ = A₀ (u : Ω₀) := by rw [u.property]; norm_num
      _ =
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereEquivL2.symm
            u : Ω₀) := by rfl
  · intro hEq
    subst f
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_greenPoissonEnergyUnitSphereEquivL2_symm_apply_eq_one
        u

/-- Structured receipt for exact Green--Poisson duality on the two actual
beta-zero energy unit spheres. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereDualityL2Receipt :
    Prop where
  green_energy_transport :
    ∀ f : Ω₀, PE₀ (G₀ f) = GE₀ f
  poisson_energy_transport :
    ∀ u : Ω₀, GE₀ (A₀ u) = PE₀ u
  green_normalized_composition :
    ∀ (f : Ω₀) (hf : f ≠ 0), PW₀ (GW₀ f) = (GE₀ f)⁻¹ • f
  poisson_normalized_composition :
    ∀ (u : Ω₀) (hu : u ≠ 0), GW₀ (PW₀ u) = (PE₀ u)⁻¹ • u
  sphere_left_inverse :
    ∀ f : GS₀,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereEquivL2.symm
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereEquivL2
            f) = f
  sphere_right_inverse :
    ∀ u : PS₀,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereEquivL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereEquivL2.symm
            u) = u
  green_sphere_pairing :
    ∀ f : GS₀,
      inner ℝ (f : Ω₀)
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereEquivL2
            f : Ω₀) = 1
  poisson_sphere_pairing :
    ∀ u : PS₀,
      inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereEquivL2.symm
            u : Ω₀)
          (u : Ω₀) = 1
  green_unique_pairing :
    ∀ (f : GS₀) (u : PS₀),
      inner ℝ (f : Ω₀) (u : Ω₀) = 1 ↔
        u =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereEquivL2
            f
  poisson_unique_pairing :
    ∀ (f : GS₀) (u : PS₀),
      inner ℝ (f : Ω₀) (u : Ω₀) = 1 ↔
        f =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereEquivL2.symm
            u
  claim_boundary :
    True

/-- The exact energy-unit-sphere duality receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereDualityL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenPoissonEnergyUnitSphereDualityL2Receipt := by
  refine
    { green_energy_transport := ?_
      poisson_energy_transport := ?_
      green_normalized_composition := ?_
      poisson_normalized_composition := ?_
      sphere_left_inverse := ?_
      sphere_right_inverse := ?_
      green_sphere_pairing := ?_
      poisson_sphere_pairing := ?_
      green_unique_pairing := ?_
      poisson_unique_pairing := ?_
      claim_boundary := trivial }
  · intro f
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_centeredGreen_eq_greenEnergyNorm
        f
  · intro u
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenEnergyNormL2_poisson_eq_poissonEnergyNorm
        u
  · intro f hf
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_poissonDualUnitWitness_greenDualUnitWitness_eq_greenNormalize
        f hf
  · intro u hu
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenDualUnitWitness_poissonDualUnitWitness_eq_poissonNormalize
        u hu
  · intro f
    exact Equiv.symm_apply_apply _ _
  · intro u
    exact Equiv.apply_symm_apply _ _
  · intro f
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_greenPoissonEnergyUnitSphereEquivL2_apply_eq_one
        f
  · intro u
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_greenPoissonEnergyUnitSphereEquivL2_symm_apply_eq_one
        u
  · intro f u
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_poissonEnergyUnitSphere_inner_eq_one_iff
        f u
  · intro f u
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_greenEnergyUnitSphere_inner_eq_one_iff
        f u

end
end MathlibAnalytic
end MGAP4D
