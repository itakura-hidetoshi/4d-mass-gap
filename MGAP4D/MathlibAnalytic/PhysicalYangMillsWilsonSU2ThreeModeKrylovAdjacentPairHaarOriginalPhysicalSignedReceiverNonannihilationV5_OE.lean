import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoPosteriorGaussianSeparationV5_OD
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalMeanEnergySinglePlaquetteV5_MK
import Mathlib.Tactic

/-!
# P4-Q2-OE — authentic Gauss-law physical signed receiver nonannihilation

OD proved the exact original TWO interacting Wilson posterior
signed-density functional L_D on C(SU(2),R) and the genuine FF physical
signed receiver fiber R_f, with the exact equality
  original physical GI gap(f,e,z) = L_D(e,z.right)(R_f(e,z,-)).
NY/OD proved L_D != 0 and true temporal Gaussian kernel sections
separate the two original Wilson posterior laws. Neither result alone
says the image of PHYSICAL Gauss-law sources under f -> R_f contains
or approximates such Gaussian sections.

OE closes the distinct, *finite-volume existential* physical receiver
nonannihilation gate using the PREVIOUS PROVED actual LO local physical
GI minor, not a new assumed receiver rank or kernel-span relation:
- for each true local plaquette p, the exact two-context squared norm
  of the SAME original source f_(p,x,y)=x*U+y*(W_p*U) is the square sum
  of two actual OD L_D/R_f signed functionals;
- LO's original physical local minor transfers exactly to positive
  signed functional 2-row coercivity at real interacting contexts;
- for every finite H, b>0 and real links e,e' and initial boundaries,
  some genuine contexts and p carry a positive two-row floor for
  ALL x,y simultaneously, forcing exact common-kernel triviality;
- in particular the SAME genuine constant Gauss-law physical source U
  is detected in one of those true contexts;
- MF and MK spatial mean-energy/single-plaquette bounds retain their
  exact original finite-H Q_GI/N_H scales under the OD identification.

The witnesses and positive floor depend on H, b, and selected
contexts. No arbitrary fixed-context receiver injectivity, all
physical Krylov-source detection, single endpoint source, positive
fine all-depth bound, U0, strong continuum limit or mass gap is proved.
Both original interacting Wilson posteriors, Gauss-law source,
Perron half-density and Wilson spatial terms remain unchanged.
No Dobrushin, sorry, admit, new axiom or artificial rank hypothesis.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OE_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OE_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OE_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OE_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OE_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section OriginalPhysicalReceiver
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "Source" => p4Q2LO_originalPhysicalLocalTwoSource H
local notation "L" => p4Q2OD_originalTwoPosteriorContrastCLM H b hb
local notation "Fiber" => p4Q2OD_originalPhysicalSignedReceiverFiber H b hb
local notation "n" => (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)
local notation "E" => p4Q2LW_originalHarnackContrastScale b
local notation "Q" => p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb

/-- EXACT original TWO-Wilson-posterior signed physical receiver
double-square on one genuine Gauss-law local source plane:
two different REAL original interacting contexts, but the SAME
true Gauss-law source f_(p,x,y) in both. -/
noncomputable def p4Q2OE_originalPhysicalReceiverSignedDoubleSq
    (e e' : Link) (z z' : Cfg × Cfg)
    (p : Plaq) (x y : ℝ) : ℝ :=
  (L z.2 e (Fiber (Source p x y) e z))^2 +
  (L z'.2 e' (Fiber (Source p x y) e' z'))^2

/-- The true OD signed-density pairing of ACTUAL FF receivers
is literally the MD/LO original two-posterior Gauss-law GI square.
This is the needed source/receiver compatibility, NOT an assumed
identification of a Gaussian section with a physical receiver. -/
theorem p4Q2OE_originalPhysicalReceiverSignedDoubleSq_eq_original
    (e e' : Link) (z z' : Cfg × Cfg)
    (p : Plaq) (x y : ℝ) :
    p4Q2OE_originalPhysicalReceiverSignedDoubleSq
      H b hb e e' z z' p x y =
    p4Q2MD_originalPlaquettePhysicalTwoSourceGapSquare
      H b hb e e' z z' p x y := by
  unfold p4Q2OE_originalPhysicalReceiverSignedDoubleSq
    p4Q2MD_originalPlaquettePhysicalTwoSourceGapSquare
  simp only [p4Q2OD_originalPhysicalGI_eq_truePosteriorSignedFunctional]

/-- Every genuinely NONZERO actual local Wilson GI minor proves
an explicit positive two-row coercivity floor for OD's original
posterior contrast functionals, with the unchanged source p,x,y.
The local minor is a previously proved sufficient physical certificate;
it is NOT assumed in the existential theorems below. -/
theorem p4Q2OE_originalPhysicalReceiverSignedDoubleSq_coercive
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq)
    (hminor : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0) :
    0 < p4Q2LO_originalLocalGIQuantitativeCoefficient
      H b hb e e' z z' p ∧
    ∀ x y : ℝ,
      p4Q2LO_originalLocalGIQuantitativeCoefficient
          H b hb e e' z z' p * (x^2 + y^2) ≤
        p4Q2OE_originalPhysicalReceiverSignedDoubleSq
          H b hb e e' z z' p x y := by
  obtain ⟨hPos, hFloor⟩ :=
    p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive
      H b hb e e' z z' p hminor
  refine ⟨hPos, ?_⟩
  intro x y
  rw [p4Q2OE_originalPhysicalReceiverSignedDoubleSq_eq_original]
  exact hFloor x y

/-- Unconditional actual finite-H source-range coercivity:
LO constructs the needed original interacting-Wilson contexts,
plaquette and strictly positive floor without inserting a new
GI detector rank, Gaussian source-surjectivity or norm assumption. -/
theorem p4Q2OE_originalPhysicalReceiver_exists_signedCoercivity
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      ∃ p : Plaq, p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      ∃ κ : ℝ, 0 < κ ∧ ∀ x y : ℝ,
        κ * (x^2 + y^2) ≤
          p4Q2OE_originalPhysicalReceiverSignedDoubleSq
            H b hpos.le e e' z z' p x y := by
  obtain ⟨z, z', p, hp, κ, hκ, hFloor⟩ :=
    p4Q2LO_originalPhysicalLocalPlaquetteGI_exists_coercive
      H b hpos e e' left₀ right₀
  refine ⟨z, z', p, hp, κ, hκ, ?_⟩
  intro x y
  rw [p4Q2OE_originalPhysicalReceiverSignedDoubleSq_eq_original]
  exact hFloor x y

/-- A positive genuinely established two-row signed receiver floor
forces two actual OD posterior-contrast receiver evaluations to have
trivial COMMON KERNEL on the true (U, W_p U) coefficient plane. -/
theorem p4Q2OE_originalPhysicalReceiver_signedCoercivity_commonKernel
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq)
    (κ : ℝ) (hκ : 0 < κ)
    (hFloor : ∀ x y : ℝ,
      κ * (x^2 + y^2) ≤
        p4Q2OE_originalPhysicalReceiverSignedDoubleSq
          H b hb e e' z z' p x y) :
    ∀ x y : ℝ,
      L z.2 e (Fiber (Source p x y) e z) = 0 ∧
      L z'.2 e' (Fiber (Source p x y) e' z') = 0 →
        x = 0 ∧ y = 0 := by
  intro x y ⟨hFirst, hSecond⟩
  have hSqZero :
      p4Q2OE_originalPhysicalReceiverSignedDoubleSq
        H b hb e e' z z' p x y = 0 := by
    simp [p4Q2OE_originalPhysicalReceiverSignedDoubleSq, hFirst, hSecond]
  have hUpper : κ * (x^2 + y^2) ≤ 0 := by
    simpa only [hSqZero] using hFloor x y
  have hSquaresNonpos : x^2 + y^2 ≤ 0 := by
    by_contra hn
    have hPositive : 0 < x^2 + y^2 := lt_of_not_ge hn
    have hProductPos := mul_pos hκ hPositive
    linarith
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

/-- Strong existential nonannihilation statement with NO rank
hypothesis: for every finite H, b>0 and physical link pair,
some genuine original interacting-Wilson contexts and one genuine
plaquette give an INJECTIVE two-row signed OD detector on the SAME
real Gauss-law source coefficient plane. This is NOT the all-source
endpoint detector Φ_(n,r). -/
theorem p4Q2OE_originalPhysicalReceiver_exists_commonKernel_trivial
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      ∃ p : Plaq, p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      ∀ x y : ℝ,
        L z.2 e (Fiber (Source p x y) e z) = 0 ∧
        L z'.2 e' (Fiber (Source p x y) e' z') = 0 →
          x = 0 ∧ y = 0 := by
  obtain ⟨z, z', p, hp, κ, hκ, hFloor⟩ :=
    p4Q2OE_originalPhysicalReceiver_exists_signedCoercivity
      H b hpos e e' left₀ right₀
  refine ⟨z, z', p, hp, ?_⟩
  exact p4Q2OE_originalPhysicalReceiver_signedCoercivity_commonKernel
    H b hpos.le e e' z z' p κ hκ hFloor

/-- An actual, fixed physical Gauss-law source U (not an invented
Gaussian section) is detected by at least ONE of the two genuine
original interacting-Wilson posterior-contrast receiver functionals
at suitable real contexts. The SAME U is used on BOTH sides.
Contexts are existential, not uniform in H and not one endpoint. -/
theorem p4Q2OE_originalPhysicalUnitReceiver_exists_nonannihilation
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      L z.2 e (Fiber U e z) ≠ 0 ∨
      L z'.2 e' (Fiber U e' z') ≠ 0 := by
  obtain ⟨z, z', p, _hp, hFaithful⟩ :=
    p4Q2OE_originalPhysicalReceiver_exists_commonKernel_trivial
      H b hb hpos e e' left₀ right₀
  have hSourceUnit : Source p 1 0 = U := by
    simp [p4Q2LO_originalPhysicalLocalTwoSource]
  have hNotBoth :
      ¬ (L z.2 e (Fiber (Source p 1 0) e z) = 0 ∧
        L z'.2 e' (Fiber (Source p 1 0) e' z') = 0) := by
    intro hBoth
    have hOneZero : (1 : ℝ) = 0 := (hFaithful 1 0 hBoth).1
    norm_num at hOneZero
  rw [hSourceUnit] at hNotBoth
  exact ⟨z, z', not_and_or.mp hNotBoth⟩

/-- For EVERY original physical link e, not just an unspecified
selected link, the actual constant Gauss-law source U is detected
by the SAME original two-posterior signed receiver at some authentic
interacting-Wilson context. The context may depend on H, b, and e. -/
theorem p4Q2OE_originalPhysicalUnitReceiver_eachLink_exists_nonzero
    (hpos : 0 < b) (e : Link) (left₀ right₀ : Cfg) :
    ∃ z : Cfg × Cfg,
      L z.2 e (Fiber U e z) ≠ 0 := by
  obtain ⟨z, z', h⟩ :=
    p4Q2OE_originalPhysicalUnitReceiver_exists_nonannihilation
      H b hb hpos e e left₀ right₀
  rcases h with hFirst | hSecond
  · exact ⟨z, hFirst⟩
  · exact ⟨z', hSecond⟩

/-- Consequently, the unmodified original GI two-POSTERIOR
expectation gap of the SAME physically defined constant Gauss-law
Hilbert vector U is nonzero somewhere for EVERY genuine link,
at every finite H and positive frozen Wilson coupling. This is
an existence-in-context statement, not a global endpoint source
injection or integrated covariance lower bound. -/
theorem p4Q2OE_originalPhysicalUnitGI_eachLink_exists_nonzero
    (hpos : 0 < b) (e : Link) (left₀ right₀ : Cfg) :
    ∃ z : Cfg × Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb U e z ≠ 0 := by
  obtain ⟨z, hz⟩ :=
    p4Q2OE_originalPhysicalUnitReceiver_eachLink_exists_nonzero
      H b hb hpos e left₀ right₀
  refine ⟨z, ?_⟩
  rw [p4Q2OD_originalPhysicalGI_eq_truePosteriorSignedFunctional]
  exact hz

/-- The original MF physical spatial average is IDENTICALLY the
average of two TRUE OD signed-posterior functional evaluations
on each p-specific Gauss-law physical Hilbert source plane.
The local source still varies with p, and is NOT a single endpoint
source. The genuine Q_GI/n and original Harnack E are unchanged. -/
theorem p4Q2OE_originalPhysicalReceiver_spatialAverage_linearFloor
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg) (x y : ℝ) :
    ((Q e e' z z' / n) / (10 * E^2)) * (x^2 + y^2) ≤
      (∑ p : Plaq,
        p4Q2OE_originalPhysicalReceiverSignedDoubleSq
          H b hb e e' z z' p x y) / n := by
  have h :=
    p4Q2MF_originalFullPhysicalGapAverage_ge_linearGI
      H b hb hpos hcount e e' z z' x y
  simpa only [p4Q2OE_originalPhysicalReceiverSignedDoubleSq_eq_original]
    using h

/-- One actual plaquette at authentic interacting-Wilson contexts
attains the genuine spatial mean-energy floor in the EXACT OD
signed physical receiver pairing representation; the rate Q_GI/n
can still decay as H grows. This makes no source-family transport. -/
theorem p4Q2OE_originalPhysicalReceiver_exists_meanPlaquette_floor
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      0 < n ∧
      0 < Q e e' z z' / n ∧
      ∃ p : Plaq,
        p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
        ∀ x y : ℝ,
          ((Q e e' z z' / n) / (10 * E^2)) * (x^2 + y^2) ≤
            p4Q2OE_originalPhysicalReceiverSignedDoubleSq
              H b hpos.le e e' z z' p x y := by
  obtain ⟨z, z', hn, hQ, p, hp, hFloor⟩ :=
    p4Q2MK_originalPhysicalGI_exists_authenticMeanPlaquette
      H b hpos.le hpos e e' left₀ right₀
  refine ⟨z, z', hn, hQ, p, hp, ?_⟩
  intro x y
  rw [p4Q2OE_originalPhysicalReceiverSignedDoubleSq_eq_original]
  exact hFloor x y

end OriginalPhysicalReceiver
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OE_originalPhysicalReceiverSignedDoubleSq_eq_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OE_originalPhysicalReceiverSignedDoubleSq_coercive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OE_originalPhysicalReceiver_exists_signedCoercivity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OE_originalPhysicalReceiver_signedCoercivity_commonKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OE_originalPhysicalReceiver_exists_commonKernel_trivial
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OE_originalPhysicalUnitReceiver_exists_nonannihilation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OE_originalPhysicalReceiver_spatialAverage_linearFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OE_originalPhysicalReceiver_exists_meanPlaquette_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OE_originalPhysicalUnitReceiver_eachLink_exists_nonzero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OE_originalPhysicalUnitGI_eachLink_exists_nonzero
