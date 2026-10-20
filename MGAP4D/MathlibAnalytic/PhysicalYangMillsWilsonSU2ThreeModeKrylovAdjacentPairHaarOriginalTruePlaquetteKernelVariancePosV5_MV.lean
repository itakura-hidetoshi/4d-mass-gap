import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCenteredPhysicalGICovarianceCauchyV5_MU
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectorySpecialUnitaryTwoStapleOscillationSeparationBCF
import MGAP4D.MathlibAnalytic.PeriodicHypercubicNondegenerateShifts
import Mathlib.Tactic

/-!
# P4-Q2-MV — genuinely nonconstant SU(2) Wilson plaquettes have
# strictly POSITIVE variance under the ACTUAL positive Wilson slab kernel

MU proved a genuine Wilson positive-kernel Cauchy–Schwarz upper bound
for actual centered Gauss-law Wilson plaquette physical source readout.
This module separates two questions that must not be conflated:

* Real spatial Wilson plaquette fluctuation is strictly positive at
  any finite spatial H and any frozen b>=0, because the ACTUAL
  original SU(2) positive Wilson kernel has full support, and
  each spatial plaquette energy has distinct values at two TRUE
  physical SU(2) link configurations.
* This positive variance does NOT imply that the ORIGINAL signed
  two-interacting-posterior local score has a strictly positive
  variance, still less that the genuine GI covariance has a lower
  bound. Cancellation across the original signed posterior is real.

The proof first proves general strict positivity of the existing
MS Wilson-kernel conditional variance of any nonconstant continuous
f on the REAL original finite-H configuration space. The original
kernel K_b(A,B)>0 and normalized product Haar have positive mass
on every nonempty open set.

Then show EVERY genuine embedded spatial plaquette energy is
nonconstant, by comparing the identity physical configuration with
the configuration in which its FIRST TRUE spatial link is replaced
by the CENTRAL SU(2) element -I. The three other oriented boundary
links are geometrically distinct on the even periodic spatial slice
of side length >=2, proved using existing periodic shift geometry.
The two original Wilson energy values are 0 and 2, not a symbolic
or Z2 substitute.

Consequently Var_{K_b(.,B)}(W_{H,p})>0 for EVERY actual spatial
plaquette p and every finite H, b>=0 and original positive Wilson
one-slab kernel section.

This asserts NO volume-uniform lower bound, no positivity of
signed GI covariance/score variance at b>0, no assumption about
spatial correlation decay, positive fine coupling×all Krylov
depth, H1-C3 strong limit or 4D Yang–Mills continuum mass gap.

No substitute posterior or physical source, Dobrushin, sorry,
admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MV_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MV_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MV_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MV_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MV_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2MV_HaarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance p4Q2MV_spatialHaarOpenPos (H : ℕ) :
    Measure.IsOpenPosMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b
local notation "Mean" => p4Q2MS_originalWilsonKernelConditionalMean H b
local notation "Var" => p4Q2MS_originalWilsonKernelConditionalVariance H b
local notation "w" => p4Q2LO_originalLocalPlaquetteContinuous H

/-- STRICT POSITIVITY of the ORIGINAL positive-Wilson-kernel
conditional variance whenever the original continuous observable
differs from its actual conditional kernel mean at one configuration.
The proof uses full support of the SAME original product Haar
reference and the strictly positive actual kernel K, without
resampling either interacting Wilson posterior. -/
theorem p4Q2MV_originalWilsonVariance_pos_of_ne_mean
    (z : Cfg × Cfg) (f : C(Cfg, ℝ))
    (A₀ : Cfg) (h : f A₀ ≠ Mean z f) :
    0 < Var z f := by
  let k : Cfg → ℝ := fun A => (f A - Mean z f)^2 * K A z.2
  have hk_cont : Continuous k :=
    ((f.continuous.sub continuous_const).pow 2).mul
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_continuous
        H 2 b z.2)
  have hk_int : Integrable k haar :=
    hk_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hk_nonneg : 0 ≤ k := by
    intro A
    exact mul_nonneg (sq_nonneg _)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H 2 b A z.2).le
  have hk_nonzero : k A₀ ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr h))
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H 2 b A₀ z.2).ne'
  have hIntPos : 0 < ∫ A : Cfg, k A ∂haar :=
    integral_pos_of_integrable_nonneg_nonzero hk_cont hk_int hk_nonneg hk_nonzero
  change 0 < (∫ A : Cfg, k A ∂haar) /
    p4Q2MR_originalWilsonKernelMass H b z
  exact div_pos hIntPos
    (p4Q2MS_originalWilsonKernelMass_pos H b z)

/-- In particular, TWO distinct point values of an actual original
continuous observable suffice for strict Wilson conditional variance
at any finite H and b>=0, with no quantitative gap assumption. -/
theorem p4Q2MV_originalWilsonVariance_pos_of_distinct_values
    (z : Cfg × Cfg) (f : C(Cfg, ℝ))
    (A₀ A₁ : Cfg) (h : f A₀ ≠ f A₁) :
    0 < Var z f := by
  by_cases h0 : f A₀ = Mean z f
  · apply p4Q2MV_originalWilsonVariance_pos_of_ne_mean H b z f A₁
    intro h1
    exact h (h0.trans h1.symm)
  · exact p4Q2MV_originalWilsonVariance_pos_of_ne_mean
      H b z f A₀ h0

/-- The true original SU(2) spatial Wilson energy of EVERY actual
periodic spatial plaquette is zero at the all-identity configuration. -/
theorem p4Q2MV_originalSpatialPlaquette_identity_energy_zero
    (p : Plaq) :
    w p (fun _ : Link => (1 : Gauge)) = 0 := by
  change specialUnitaryWilsonPlaquetteEnergy 2
    (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
      (fun _ : Link => (1 : Gauge)) p) = 0
  simp [periodicHypercubicEvenSpatialSlicePlaquetteHolonomy,
    specialUnitaryWilsonPlaquetteEnergy_two_one]

/-- For ANY actual spatial SU(2) plaquette, its first genuine spatial
link differs from all its other three oriented boundary links, including
on the shortest even periodic lattice H=0 (side length 2). -/
theorem p4Q2MV_originalSpatialPlaquette_firstLink_otherThree_ne
    (p : Plaq) :
    let v := p.1
    let mu := p.2.1.1
    let nu := p.2.1.2
    let e0 : Link := (v,mu)
    (periodicHypercubicEvenSpatialSliceShift H v mu, nu) ≠ e0 ∧
    (periodicHypercubicEvenSpatialSliceShift H v nu, mu) ≠ e0 ∧
    (v,nu) ≠ e0 := by
  dsimp
  have haxis : p.2.1.1 ≠ p.2.1.2 := by
    intro heq
    exact (ne_of_lt p.2.2) (congrArg Subtype.val heq)
  have hshift :
      periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.2 ≠ p.1 := by
    intro heq
    have hv := congrArg Subtype.val heq
    exact (periodicHypercubicShift_ne_self
      (PeriodicHypercubicEvenSideLength H)
      (by
        change 2 ≤ 2 * (H + 1)
        omega)
      p.1.1 p.2.1.2.1) hv
  constructor
  · intro heq
    exact haxis (congrArg Prod.snd heq).symm
  constructor
  · intro heq
    exact hshift (congrArg Prod.fst heq)
  · intro heq
    exact haxis (congrArg Prod.snd heq).symm

/-- The TRUE original spatial plaquette Wilson holonomy is the central
SU(2) -I when only the plaquette's first physical spatial link is
replaced by -I in the full identity configuration.
The geometric noncoincidence of all four links has been proved. -/
theorem p4Q2MV_originalSpatialPlaquette_firstLink_negativeIdentity_holonomy
    (p : Plaq) :
    periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
      (Function.update (fun _ : Link => (1 : Gauge))
        (p.1,p.2.1.1) specialUnitaryTwoNegativeIdentity) p =
      specialUnitaryTwoNegativeIdentity := by
  let v := p.1
  let mu := p.2.1.1
  let nu := p.2.1.2
  let e0 : Link := (v,mu)
  let e1 : Link := (periodicHypercubicEvenSpatialSliceShift H v mu,nu)
  let e2 : Link := (periodicHypercubicEvenSpatialSliceShift H v nu,mu)
  let e3 : Link := (v,nu)
  have hne := p4Q2MV_originalSpatialPlaquette_firstLink_otherThree_ne H p
  dsimp only at hne
  rcases hne with ⟨h1,h2,h3⟩
  have hf0 :
      (Function.update (fun _ : Link => (1 : Gauge)) e0
        specialUnitaryTwoNegativeIdentity) e0 = specialUnitaryTwoNegativeIdentity := by
    simp [Function.update]
  have hf1 :
      (Function.update (fun _ : Link => (1 : Gauge)) e0
        specialUnitaryTwoNegativeIdentity) e1 = 1 := by
    simp [Function.update, e1, e0, v, mu, nu, h1]
  have hf2 :
      (Function.update (fun _ : Link => (1 : Gauge)) e0
        specialUnitaryTwoNegativeIdentity) e2 = 1 := by
    simp [Function.update, e2, e0, v, mu, nu, h2]
  have hf3 :
      (Function.update (fun _ : Link => (1 : Gauge)) e0
        specialUnitaryTwoNegativeIdentity) e3 = 1 := by
    simp [Function.update, e3, e0, v, mu, nu, h3]
  change
    (Function.update (fun _ : Link => (1 : Gauge)) e0
        specialUnitaryTwoNegativeIdentity) e0 *
      (Function.update (fun _ : Link => (1 : Gauge)) e0
        specialUnitaryTwoNegativeIdentity) e1 *
      ((Function.update (fun _ : Link => (1 : Gauge)) e0
        specialUnitaryTwoNegativeIdentity) e2)⁻¹ *
      ((Function.update (fun _ : Link => (1 : Gauge)) e0
        specialUnitaryTwoNegativeIdentity) e3)⁻¹ =
      specialUnitaryTwoNegativeIdentity
  rw [hf0, hf1, hf2, hf3]
  simp

/-- The SAME true physical spatial SU(2) plaquette takes the
different Wilson energy value 2 at the one-negative-center-link
configuration, not at an artificial scalar/Z₂ plaquette. -/
theorem p4Q2MV_originalSpatialPlaquette_negativeFirstLink_energy_two
    (p : Plaq) :
    w p
      (Function.update (fun _ : Link => (1 : Gauge))
        (p.1,p.2.1.1) specialUnitaryTwoNegativeIdentity) = 2 := by
  change specialUnitaryWilsonPlaquetteEnergy 2
    (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
      (Function.update (fun _ : Link => (1 : Gauge))
        (p.1,p.2.1.1) specialUnitaryTwoNegativeIdentity) p) = 2
  rw [p4Q2MV_originalSpatialPlaquette_firstLink_negativeIdentity_holonomy H p]
  exact specialUnitaryWilsonPlaquetteEnergy_two_negativeIdentity

/-- EVERY actual original spatial Wilson plaquette energy has at least
two distinct physical SU(2) spatial-link configuration values:
identity gives 0; replace its first link by -I gives 2. -/
theorem p4Q2MV_originalSpatialPlaquette_nonconstant
    (p : Plaq) :
    ∃ A₀ A₁ : Cfg, w p A₀ ≠ w p A₁ := by
  let A₀ : Cfg := fun _ => 1
  let A₁ : Cfg := Function.update A₀ (p.1,p.2.1.1)
    specialUnitaryTwoNegativeIdentity
  refine ⟨A₀,A₁,?_⟩
  have hzero : w p A₀ = 0 :=
    p4Q2MV_originalSpatialPlaquette_identity_energy_zero H p
  have htwo : w p A₁ = 2 :=
    p4Q2MV_originalSpatialPlaquette_negativeFirstLink_energy_two H p
  rw [hzero,htwo]
  norm_num

/-- MAIN genuine physical Wilson result. EVERY actual SU(2) spatial
plaquette p has STRICTLY positive normalized variance under the
unchanged full positive original one-slab Wilson kernel at ANY
finite H, frozen b>=0 and actual two-boundary context z.
This does NOT say a uniform-in-H lower variance exists. -/
theorem p4Q2MV_originalSpatialPlaquette_kernelVariance_pos
    (z : Cfg × Cfg) (p : Plaq) :
    0 < Var z (w p) := by
  rcases p4Q2MV_originalSpatialPlaquette_nonconstant H p with
    ⟨A₀,A₁,hdist⟩
  exact p4Q2MV_originalWilsonVariance_pos_of_distinct_values
    H b z (w p) A₀ A₁ hdist

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MV_originalWilsonVariance_pos_of_ne_mean
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MV_originalWilsonVariance_pos_of_distinct_values
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MV_originalSpatialPlaquette_identity_energy_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MV_originalSpatialPlaquette_firstLink_otherThree_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MV_originalSpatialPlaquette_firstLink_negativeIdentity_holonomy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MV_originalSpatialPlaquette_negativeFirstLink_energy_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MV_originalSpatialPlaquette_nonconstant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MV_originalSpatialPlaquette_kernelVariance_pos
