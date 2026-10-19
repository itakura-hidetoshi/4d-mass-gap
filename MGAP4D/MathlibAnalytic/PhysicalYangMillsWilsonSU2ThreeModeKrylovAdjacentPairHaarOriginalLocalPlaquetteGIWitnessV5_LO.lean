import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalTwoContextGICoercivityV5_LN
import Mathlib.Tactic

/-!
# P4-Q2-LO — a TRUE local plaquette detects the original physical GI minor

The genuine spatial Wilson action is the finite SUM over ORIGINAL spatial
plaquette energies, not a surrogate action. We prove that its original
two-context GI determinant decomposes into the sum of actual SINGLE
plaquette determinants. LM makes the total nonzero; elementary finite
sum nonvanishing gives an actual local plaquette with nonzero determinant.

Each local plaquette energy is a bounded continuous gauge-invariant original
SU(2) observable. Its multiplication of the physical Gauss-law constant
unit is an actual physical Hilbert vector, represented by the exact
plaquette energy in Haar-L². JH then identifies its two original GI
responses with the exact TWO INTERACTING WILSON POSTERIOR responses.

LN's adjugate/Frobenius inequality yields strictly positive explicit
coercivity on the two-source physical plane spanned by the unit and
this physically selected local plaquette. No fixed plaquette witness,
volume-uniform floor, artificial rank assumption, independent-Haar
posterior replacement, Dobrushin, sorry/admit or new axioms.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2LO_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LO_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LO_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LO_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LO_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Spatial
variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "ps" => periodicHypercubicEvenSpatialSlicePlaquetteList H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "U" => periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "L" => ContinuousMap.toLp 2 haar ℝ
local notation "G" => p4Q2JH_originalGIResponseCLM H

/-- True original single spatial plaquette SU(2) Wilson energy, as a
continuous (hence bounded) function of the complete spatial configuration. -/
noncomputable def p4Q2LO_originalLocalPlaquetteContinuous (p : Plaq) : C(Cfg, ℝ) := by
  have hHol : Continuous
      (fun A : Cfg => periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p) := by
    unfold periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
    fun_prop
  exact ⟨fun A => specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p),
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp hHol⟩

@[simp] theorem p4Q2LO_originalLocalPlaquetteContinuous_apply
    (p : Plaq) (A : Cfg) :
    p4Q2LO_originalLocalPlaquetteContinuous H p A =
      specialUnitaryWilsonPlaquetteEnergy 2
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p) := rfl

/-- The exact original global spatial Wilson action is the finite sum
of THESE genuine local plaquette continuous functions. -/
theorem p4Q2LO_originalSpatialWilsonContinuous_eq_localSum :
    p4Q2JI_actualSpatialWilsonContinuous H =
      (((periodicHypercubicEvenSpatialSlicePlaquetteList H).map fun p => p4Q2LO_originalLocalPlaquetteContinuous H p).sum) := by
  ext A
  change
    (((periodicHypercubicEvenSpatialSlicePlaquetteList H).map fun p => specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p)).sum) =
    (((periodicHypercubicEvenSpatialSlicePlaquetteList H).map fun p => p4Q2LO_originalLocalPlaquetteContinuous H p).sum) A
  have hlist : ∀ xs : List Plaq,
      ((xs.map fun p => specialUnitaryWilsonPlaquetteEnergy 2
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p)).sum) =
        ((xs.map fun p => p4Q2LO_originalLocalPlaquetteContinuous H p).sum) A := by
    intro xs
    induction xs with
    | nil => simp
    | cons p xs ih =>
        simpa only [List.map_cons, List.sum_cons, ContinuousMap.add_apply,
          p4Q2LO_originalLocalPlaquetteContinuous_apply] using
          congrArg (fun t : ℝ =>
            specialUnitaryWilsonPlaquetteEnergy 2
              (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p) + t) ih
  exact hlist (periodicHypercubicEvenSpatialSlicePlaquetteList H)

/-- Linearity of true JH Haar-L² detector over any finite list of
actual continuous spatial sources. -/
private theorem p4Q2LO_originalGI_map_list_sum
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg)
    (xs : List (C(Cfg, ℝ))) :
    G b hb e z (L xs.sum) =
      (xs.map fun f => G b hb e z (L f)).sum := by
  induction xs with
  | nil => simp
  | cons f fs ih =>
      simp only [List.sum_cons, List.map_cons, map_add, ih]

/-- Pure adjugate additivity: if the second source is a finite sum,
the original two-context determinant is the sum of its minors. -/
private theorem p4Q2LO_minor_map_list_sum
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link)
    (z z' : Cfg × Cfg) (xs : List (C(Cfg, ℝ))) :
    G b hb e z (L (1 : C(Cfg, ℝ))) * G b hb e' z' (L xs.sum) -
      G b hb e z (L xs.sum) * G b hb e' z' (L (1 : C(Cfg, ℝ))) =
    (xs.map fun f =>
      G b hb e z (L (1 : C(Cfg, ℝ))) * G b hb e' z' (L f) -
        G b hb e z (L f) * G b hb e' z' (L (1 : C(Cfg, ℝ)))).sum := by
  induction xs with
  | nil => simp
  | cons f fs ih =>
      simp only [List.sum_cons, List.map_cons, map_add]
      rw [← ih]
      ring

/-- One original two-context determinant, but with an ACTUAL individual
spatial plaquette energy instead of the total Wilson action. -/
noncomputable def p4Q2LO_originalLocalPlaquetteGIMinor
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link)
    (z z' : Cfg × Cfg) (p : Plaq) : ℝ :=
  G b hb e z (L (1 : C(Cfg, ℝ))) *
    G b hb e' z' (L (p4Q2LO_originalLocalPlaquetteContinuous H p)) -
  G b hb e z (L (p4Q2LO_originalLocalPlaquetteContinuous H p)) *
    G b hb e' z' (L (1 : C(Cfg, ℝ)))

/-- The ORIGINAL global spatial Wilson GI minor is precisely the
sum over EVERY actual single-plaquette GI minor. -/
theorem p4Q2LO_originalSpatialGIMinor_eq_sum_local
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link) (z z' : Cfg × Cfg) :
    p4Q2JI_originalGISpatialActionMinor H b hb e e' z z' =
      ((periodicHypercubicEvenSpatialSlicePlaquetteList H).map fun p =>
        p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p).sum := by
  unfold p4Q2JI_originalGISpatialActionMinor
  rw [p4Q2LO_originalSpatialWilsonContinuous_eq_localSum H]
  rw [p4Q2LO_minor_map_list_sum H b hb e e' z z'
    ((periodicHypercubicEvenSpatialSlicePlaquetteList H).map fun p => p4Q2LO_originalLocalPlaquetteContinuous H p)]
  simp only [List.map_map]
  rfl

/-- Finite-sum witness: nonzero sum forces one actual summand nonzero,
with proven membership rather than a synthetic index. -/
private theorem p4Q2LO_exists_nonzero_of_list_sum
    {α : Type*} (xs : List α) (f : α → ℝ)
    (h : (xs.map f).sum ≠ 0) : ∃ p ∈ xs, f p ≠ 0 := by
  induction xs with
  | nil => simp at h
  | cons p xs ih =>
      by_cases hp : f p = 0
      · have hrest : (xs.map f).sum ≠ 0 := by
          simpa [hp] using h
        obtain ⟨q, hq, hqne⟩ := ih hrest
        exact ⟨q, by simp [hq], hqne⟩
      · exact ⟨p, by simp, hp⟩

/-- LM's proven nonzero GLOBAL original Wilson GI minor produces a
nonzero actual SINGLE spatial plaquette original Wilson GI minor,
at real contexts and for every finite H, positive b, and real links.
The selected plaquette may depend on volume and contexts. -/
theorem p4Q2LO_originalLocalPlaquetteGIMinor_exists_nonzero
    (b : ℝ) (hb : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg, ∃ p : Plaq,
      p ∈ ps ∧ p4Q2LO_originalLocalPlaquetteGIMinor
        H b hb.le e e' z z' p ≠ 0 := by
  obtain ⟨z, z', hminor⟩ :=
    p4Q2LM_originalSpatialWilsonGIMinor_exists_nonzero_contexts
      H b hb e e' left₀ right₀
  have hsum : ((periodicHypercubicEvenSpatialSlicePlaquetteList H).map fun p =>
        p4Q2LO_originalLocalPlaquetteGIMinor H b hb.le e e' z z' p).sum ≠ 0 := by
    rw [← p4Q2LO_originalSpatialGIMinor_eq_sum_local H b hb.le e e' z z']
    exact hminor
  obtain ⟨p, hp, hpminor⟩ := p4Q2LO_exists_nonzero_of_list_sum
    ps (p4Q2LO_originalLocalPlaquetteGIMinor H b hb.le e e' z z') hsum
  exact ⟨z, z', p, hp, hpminor⟩

/-- Bounded original plaquette energy: no invented surrogate observable. -/
noncomputable def p4Q2LO_originalLocalPlaquetteBounded
    (p : Plaq) : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H 2 :=
  BoundedContinuousFunction.mkOfCompact (p4Q2LO_originalLocalPlaquetteContinuous H p)

@[simp] theorem p4Q2LO_originalLocalPlaquetteBounded_apply
    (p : Plaq) (A : Cfg) :
    p4Q2LO_originalLocalPlaquetteBounded H p A =
      p4Q2LO_originalLocalPlaquetteContinuous H p A := rfl

/-- Each truly local spatial plaquette energy is gauge invariant by
the ORIGINAL four-edge SU(2) holonomy-conjugation theorem. -/
theorem p4Q2LO_originalLocalPlaquetteBounded_gaugeInvariant
    (p : Plaq) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant
      H 2 (p4Q2LO_originalLocalPlaquetteBounded H p) := by
  intro γ A
  change specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ A) p) =
    specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p)
  rw [periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_gaugeTransform]
  exact specialUnitaryWilsonPlaquetteEnergy_conjInvariant
    (γ p.1) (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p)

/-- Multiply the true physical Gauss-law constant unit by the real
single-plaquette Wilson action using EXISTING physical Hilbert operator. -/
noncomputable def p4Q2LO_originalLocalPlaquettePhysicalSource
    (p : Plaq) : Phys :=
  periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator
    H 2 (p4Q2LO_originalLocalPlaquetteBounded H p)
    (p4Q2LO_originalLocalPlaquetteBounded_gaugeInvariant H p) U

/-- The genuine local physical source has precisely its original
plaquette energy as a continuous Haar-a.e. representative. -/
theorem p4Q2LO_originalLocalPlaquettePhysicalSource_coe_eq_toLp
    (p : Plaq) :
    ((p4Q2LO_originalLocalPlaquettePhysicalSource H p : Phys) : Lp ℝ 2 haar) =
      L (p4Q2LO_originalLocalPlaquetteContinuous H p) := by
  apply Lp.ext
  have hMul :
      (fun A : Cfg => ((p4Q2LO_originalLocalPlaquettePhysicalSource H p : Phys) :
        Lp ℝ 2 haar) A) =ᵐ[haar]
      (fun A : Cfg =>
        p4Q2LO_originalLocalPlaquetteBounded H p A *
          (U : Lp ℝ 2 haar) A) := by
    change (fun A : Cfg =>
      (periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2 H 2
        (p4Q2LO_originalLocalPlaquetteBounded H p)
        (U : Lp ℝ 2 haar)) A) =ᵐ[haar] _
    exact periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2_coeFn
      H 2 (p4Q2LO_originalLocalPlaquetteBounded H p) (U : Lp ℝ 2 haar)
  have hU :
      (fun A : Cfg => (U : Lp ℝ 2 haar) A) =ᵐ[haar]
      (fun _ => (1 : ℝ)) := by
    change (fun A : Cfg => (Lp.const 2 haar (1 : ℝ)) A) =ᵐ[haar]
      (fun _ => (1 : ℝ))
    exact Lp.coeFn_const (μ := haar) (p := 2) (c := (1 : ℝ))
  have hRep :
      (fun A : Cfg => ((p4Q2LO_originalLocalPlaquettePhysicalSource H p : Phys) :
        Lp ℝ 2 haar) A) =ᵐ[haar]
      p4Q2LO_originalLocalPlaquetteContinuous H p := by
    filter_upwards [hMul, hU] with A hm hu
    rw [hm, hu]
    rw [mul_one, p4Q2LO_originalLocalPlaquetteBounded_apply]
  exact hRep.trans
    ((p4Q2LO_originalLocalPlaquetteContinuous H p).coeFn_toLp
      (p := 2) (𝕜 := ℝ) haar).symm

/-- The actual TWO interacting original Wilson posterior GI response of
the local Gauss-law Hilbert source matches the original JH functional. -/
theorem p4Q2LO_originalLocalPlaquetteGI_eq_physicalGI
    (b : ℝ) (hb : 0 ≤ b) (e : Link)
    (z : Cfg × Cfg) (p : Plaq) :
    G b hb e z (L (p4Q2LO_originalLocalPlaquetteContinuous H p)) =
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
        (p4Q2LO_originalLocalPlaquettePhysicalSource H p) e z := by
  have hLp :=
    p4Q2LO_originalLocalPlaquettePhysicalSource_coe_eq_toLp H p
  have hRep :
      (fun A : Cfg =>
        ((p4Q2LO_originalLocalPlaquettePhysicalSource H p : Phys) :
          Lp ℝ 2 haar) A) =ᵐ[haar]
      p4Q2LO_originalLocalPlaquetteContinuous H p := by
    rw [hLp]
    exact (p4Q2LO_originalLocalPlaquetteContinuous H p).coeFn_toLp
      (p := 2) (𝕜 := ℝ) haar
  have h := p4Q2JH_originalGIResponseCLM_agrees_with_physicalGI H b hb e z
    (p4Q2LO_originalLocalPlaquettePhysicalSource H p)
    (p4Q2LO_originalLocalPlaquetteContinuous H p) hRep
  rw [hLp] at h
  exact h

/-- Actual two-dimensional physical Hilbert source plane selected by
the original plaquette index; no imaginary local test vector. -/
noncomputable def p4Q2LO_originalPhysicalLocalTwoSource
    (p : Plaq) (x y : ℝ) : Phys :=
  x • U + y • p4Q2LO_originalLocalPlaquettePhysicalSource H p

theorem p4Q2LO_originalPhysicalLocalTwoSource_GI_eq
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg)
    (p : Plaq) (x y : ℝ) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
      (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z =
      x * G b hb e z (L (1 : C(Cfg, ℝ))) +
        y * G b hb e z (L (p4Q2LO_originalLocalPlaquetteContinuous H p)) := by
  let f : C(Cfg, ℝ) :=
    x • (1 : C(Cfg, ℝ)) + y • p4Q2LO_originalLocalPlaquetteContinuous H p
  have hF :
      L f = x • L (1 : C(Cfg, ℝ)) +
        y • L (p4Q2LO_originalLocalPlaquetteContinuous H p) := by
    dsimp [f]
    rw [map_add, map_smul, map_smul]
  have hCoe :
      ((p4Q2LO_originalPhysicalLocalTwoSource H p x y : Phys) : Lp ℝ 2 haar) =
        L f := by
    change ((x • U + y • p4Q2LO_originalLocalPlaquettePhysicalSource H p : Phys) :
      Lp ℝ 2 haar) = L f
    rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
      p4Q2JU_originalPhysicalUnit_coe_eq_toLp,
      p4Q2LO_originalLocalPlaquettePhysicalSource_coe_eq_toLp,
      hF]
  have hRep :
      (fun A : Cfg =>
        ((p4Q2LO_originalPhysicalLocalTwoSource H p x y : Phys) :
          Lp ℝ 2 haar) A) =ᵐ[haar] f := by
    rw [hCoe]
    exact f.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  have h :=
    p4Q2JH_originalGIResponseCLM_agrees_with_physicalGI H b hb e z
      (p4Q2LO_originalPhysicalLocalTwoSource H p x y) f hRep
  rw [hCoe, hF, map_add, map_smul, map_smul] at h
  simpa only [smul_eq_mul] using h.symm

/-- EXACT four-entry original local physical GI response Frobenius
denominator; all response channels use true interacting Wilson laws. -/
noncomputable def p4Q2LO_originalLocalGIFrobeniusSq
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link)
    (z z' : Cfg × Cfg) (p : Plaq) : ℝ :=
  (G b hb e z (L (1 : C(Cfg, ℝ))))^2 +
  (G b hb e z (L (p4Q2LO_originalLocalPlaquetteContinuous H p)))^2 +
  (G b hb e' z' (L (1 : C(Cfg, ℝ))))^2 +
  (G b hb e' z' (L (p4Q2LO_originalLocalPlaquetteContinuous H p)))^2

noncomputable def p4Q2LO_originalLocalGIQuantitativeCoefficient
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link)
    (z z' : Cfg × Cfg) (p : Plaq) : ℝ :=
  (p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p)^2 /
    p4Q2LO_originalLocalGIFrobeniusSq H b hb e e' z z' p

/-- Nonzero LOCAL genuine original GI determinant yields explicit
finite-volume coercivity for every x U + y W_p U in physical Hilbert. -/
theorem p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link)
    (z z' : Cfg × Cfg) (p : Plaq)
    (hminor : p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p ≠ 0) :
    0 < p4Q2LO_originalLocalGIQuantitativeCoefficient H b hb e e' z z' p ∧
      ∀ x y : ℝ,
        p4Q2LO_originalLocalGIQuantitativeCoefficient H b hb e e' z z' p *
          (x^2 + y^2) ≤
        (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
          (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
        (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
          (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2 := by
  let a : ℝ := G b hb e z (L (1 : C(Cfg, ℝ)))
  let q : ℝ := G b hb e z (L (p4Q2LO_originalLocalPlaquetteContinuous H p))
  let c : ℝ := G b hb e' z' (L (1 : C(Cfg, ℝ)))
  let d : ℝ := G b hb e' z' (L (p4Q2LO_originalLocalPlaquetteContinuous H p))
  have hd : a * d - q * c ≠ 0 := by
    change a * d - q * c ≠ 0 at hminor
    exact hminor
  have h := p4Q2LN_twoRowFrobenius_coercive a q c d hd
  constructor
  · change 0 < (a * d - q * c)^2 / (a^2 + q^2 + c^2 + d^2)
    exact h.1
  · intro x y
    rw [p4Q2LO_originalPhysicalLocalTwoSource_GI_eq,
      p4Q2LO_originalPhysicalLocalTwoSource_GI_eq]
    change ((a * d - q * c)^2 / (a^2 + q^2 + c^2 + d^2)) *
      (x^2 + y^2) ≤
        (x * a + y * q)^2 + (x * c + y * d)^2
    convert h.2 x y using 1; ring

/-- Unconditional genuine local plaquette physical two-source GI
coercivity at EVERY finite H, positive b, and given pair of real links.
The witness p, contexts and κ are existential and H-dependent. -/
theorem p4Q2LO_originalPhysicalLocalPlaquetteGI_exists_coercive
    (b : ℝ) (hb : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg, ∃ p : Plaq, p ∈ ps ∧ ∃ κ : ℝ,
      0 < κ ∧ ∀ x y : ℝ,
        κ * (x^2 + y^2) ≤
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb.le (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb.le (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2 := by
  obtain ⟨z, z', p, hp, hminor⟩ :=
    p4Q2LO_originalLocalPlaquetteGIMinor_exists_nonzero
      H b hb e e' left₀ right₀
  obtain ⟨hκ, hbound⟩ :=
    p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive
      H b hb.le e e' z z' p hminor
  exact ⟨z, z', p, hp,
    p4Q2LO_originalLocalGIQuantitativeCoefficient H b hb.le e e' z z' p,
    hκ, hbound⟩

end Spatial
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LO_originalSpatialWilsonContinuous_eq_localSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LO_originalSpatialGIMinor_eq_sum_local
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LO_originalLocalPlaquetteGIMinor_exists_nonzero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LO_originalLocalPlaquetteBounded_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LO_originalLocalPlaquettePhysicalSource_coe_eq_toLp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LO_originalLocalPlaquetteGI_eq_physicalGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LO_originalPhysicalLocalTwoSource_GI_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LO_originalPhysicalLocalPlaquetteGI_exists_coercive