import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalReceiverToNumeratorExplicitRadiusV5_PZ37AES
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AET — original source receiver local-to-global chordal descent

The original AES quantitative bridge requires an authentic D_H slope
certificate L_F for the centered physical source JQ receiver. Instead
of assuming this full-boundary bound as a black box, we reduce it
without weakening its conclusion to the actual one-link source
receiver inequalities in the two original boundary slices.

Two new structural facts are exact and UNCONDITIONAL:
* F_e(A,B;xi) is independent of B(e), since JQ's original receiver
  replaces the right link e by the genuine SU(2) integration variable xi;
* the unchanged true Haar numerator N_e(A,B) is independent of B(e).

For the remaining physical boundary coordinates, any certified
per-link absolute receiver slope L_F in the ORIGINAL ADK chordal
distance d_J glues to a full original ADL D_H global slope.
The finite-coordinate gluing is a typed additive Lipschitz analogue
of AEP's exact source-preserving telescoping. It uses the
already-verified finite-two-boundary exponential Harnack theorem
on exp(f), not an independent product posterior or new metric.

This new local-to-global certificate composes with AES to give a
true numerator D_H modulus, an explicit AER half-amplitude radius
and a gauge-opposite original pair-Haar two-ball covariance moment.

The local receiver modulus on the OTHER one-link coordinates is a
separate, genuinely physical obligation, not numerically established
here. In particular no H-uniform L_F, source regularization constant,
GI threshold, coercivity, spectral gap or continuum mass gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- A signed real one-coordinate absolute modulus induces a
positive exponential Harnack factor, without a positivity condition
on the signed original observable. -/
theorem p4Q2PZ37AET_realExpHarnack_of_absDifference
    (x y t : ℝ) (h : |x-y| ≤ t) :
    Real.exp x ≤ Real.exp t * Real.exp y := by
  have hUpper : x ≤ t + y := by
    have hu := (abs_le.mp h).2
    linarith only [hu]
  calc
    Real.exp x ≤ Real.exp (t+y) := Real.exp_le_exp.mpr hUpper
    _ = Real.exp t * Real.exp y := Real.exp_add _ _

/-- FINITE two-boundary Lipschitz descent for any real signed
observable, from per-coordinate original-link bounds.
It is genuinely finite-coordinate and uses AEP's proven
telescoping for exp(f); no positivity of f is needed. -/
theorem p4Q2PZ37AET_finiteTwoBoundary_absLipschitz
    {ι G : Type*} [Fintype ι] [DecidableEq ι]
    (d : G → G → ℝ) (hdSym : ∀ g h, d g h = d h g)
    (L : ℝ) (f : (ι → G) × (ι → G) → ℝ)
    (hLeft : ∀ (A B : ι → G) (i : ι) (g h : G),
      |f (Function.update A i g,B) -
        f (Function.update A i h,B)| ≤ L * d g h)
    (hRight : ∀ (A B : ι → G) (i : ι) (g h : G),
      |f (A,Function.update B i g) -
        f (A,Function.update B i h)| ≤ L * d g h)
    (A B C D : ι → G) :
    |f (A,B)-f (C,D)| ≤
      L * ∑ i : ι, (d (A i) (C i)+d (B i) (D i)) := by
  let E : (ι → G) × (ι → G) → ℝ := fun z => Real.exp (f z)
  have hExpLeft :
      ∀ (U V : ι → G) (i : ι) (g h : G),
        E (Function.update U i g,V) ≤
          Real.exp (L * d g h) * E (Function.update U i h,V) := by
    intro U V i g h
    exact p4Q2PZ37AET_realExpHarnack_of_absDifference
      _ _ _ (hLeft U V i g h)
  have hExpRight :
      ∀ (U V : ι → G) (i : ι) (g h : G),
        E (U,Function.update V i g) ≤
          Real.exp (L * d g h) * E (U,Function.update V i h) := by
    intro U V i g h
    exact p4Q2PZ37AET_realExpHarnack_of_absDifference
      _ _ _ (hRight U V i g h)
  have hUpper (U V W X : ι → G) :
      f (U,V)-f (W,X) ≤
        L * ∑ i : ι, (d (U i) (W i)+d (V i) (X i)) := by
    have hExp :=
      p4Q2PZ37AEP_finiteTwoBoundaryHarnack
        d L E hExpLeft hExpRight U V W X
    have hExp' :
        Real.exp (f (U,V)) ≤
          Real.exp
            (L * ∑ i : ι, (d (U i) (W i)+d (V i) (X i)) +
              f (W,X)) := by
      rw [Real.exp_add]
      exact hExp
    have hLe := Real.exp_le_exp.mp hExp'
    linarith only [hLe]
  have hfwd := hUpper A B C D
  have hback := hUpper C D A B
  have hSumSym :
      (∑ i : ι, (d (C i) (A i)+d (D i) (B i))) =
        ∑ i : ι, (d (A i) (C i)+d (B i) (D i)) := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hdSym (C i) (A i), hdSym (D i) (B i)]
  rw [hSumSym] at hback
  apply abs_le.mpr
  constructor
  · linarith only [hback]
  · exact hfwd

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "mu" => normalizedCompactHaar G
local notation "chi" => p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37AET_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AET_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AET_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AET_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AET_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "F" => p4Q2JQ_originalPhysicalSourceLinkReceiver H b0 hb0 f0
local notation "N" => p4Q2PZ37AEF_originalCenteredCovarianceNumerator H
local notation "q" => p4Q2JQ_originalPhysicalGIDensityWeight H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "Lq" => (13 * b0) * Real.exp (13 * b0) *
  (Real.exp (b0 *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) /
    Real.sqrt (
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0)^3))

local instance p4Q2PZ37AET_links : Fintype Link := Fintype.ofFinite _

/-- The original right-insertion receiver C(G,R) does NOT depend on
the value of the right context at the actual receiver link e.
This is a genuine exact source-receiver property, without an
assumption on the remaining boundary coordinates. -/
theorem p4Q2PZ37AET_originalReceiver_ignoresRightReceiverLink
    (e : Link) (A B : Cfg) (xi g : G) :
    F e (A,Function.update B e xi) g = F e (A,B) g := by
  classical
  have hReplace :
      Function.update (Function.update B e xi) e g =
        Function.update B e g := by
    funext i
    by_cases hi : i = e
    · subst i
      simp
    · simp [Function.update, hi]
  simp only [p4Q2JQ_originalPhysicalSourceLinkReceiver_apply, hReplace]

/-- The actual SU(2) Haar numerator of the same physical centered
Wilson receiver inherits exact independence from B(e), not merely
a small error term. -/
theorem p4Q2PZ37AET_originalHaarNumerator_ignoresRightReceiverLink
    (e : Link) (A B : Cfg) (xi : G) :
    N e (A, Function.update B e xi) = N e (A,B) := by
  change
    (∫ g : G, F e (A,Function.update B e xi) g * chi g ∂mu) =
      (∫ g : G, F e (A,B) g * chi g ∂mu)
  apply integral_congr_ae
  filter_upwards with g
  rw [p4Q2PZ37AET_originalReceiver_ignoresRightReceiverLink H e A B xi g]

/-- For all OTHER right boundary links and all left links, a local
D_J slope of the original source receiver glues into the ORIGINAL
whole-boundary D_H Lipschitz certificate required in AES.
The right receiver coordinate itself needs NO Lipschitz premise. -/
theorem p4Q2PZ37AET_originalOneLinkReceiver_givesFullSlope
    (e : Link) (LF : ℝ) (hLF : 0 ≤ LF)
    (hLeft : ∀ (A B : Cfg) (i : Link) (g h xi : G),
      |F e (Function.update A i g,B) xi -
        F e (Function.update A i h,B) xi| ≤ LF * dJ g h)
    (hRightAway : ∀ (A B : Cfg) (i : Link), i ≠ e →
      ∀ (g h xi : G),
      |F e (A,Function.update B i g) xi -
        F e (A,Function.update B i h) xi| ≤ LF * dJ g h) :
    ∀ (z w : Pair) (xi : G),
      |F e z xi-F e w xi| ≤ LF*D z w := by
  classical
  intro z w xi
  have hLeftX : ∀ (A B : Cfg) (i : Link) (g h : G),
      |F e (Function.update A i g,B) xi -
        F e (Function.update A i h,B) xi| ≤ LF*dJ g h := by
    intro A B i g h
    exact hLeft A B i g h xi
  have hRightX : ∀ (A B : Cfg) (i : Link) (g h : G),
      |F e (A,Function.update B i g) xi -
        F e (A,Function.update B i h) xi| ≤ LF*dJ g h := by
    intro A B i g h
    by_cases hie : i = e
    · subst i
      rw [p4Q2PZ37AET_originalReceiver_ignoresRightReceiverLink H e A B g xi,
        p4Q2PZ37AET_originalReceiver_ignoresRightReceiverLink H e A B h xi]
      simp only [sub_self, abs_zero]
      exact mul_nonneg hLF (p4Q2PZ37ADK_trueChordalDistance_nonneg g h)
    · exact hRightAway A B i hie g h xi
  have h :=
    p4Q2PZ37AET_finiteTwoBoundary_absLipschitz
      dJ p4Q2PZ37ADK_trueChordalDistance_symm LF
      (fun z : Pair => F e z xi)
      hLeftX hRightX z.1 z.2 w.1 w.2
  simpa only [p4Q2PZ37ADL_originalFullBoundaryChordalDistance] using h

/-- The unchanged Haar numerator inherits the EXACT same D_H slope
from original link-local Wilson receiver certificates, using the
already verified AES |original character| <= 1. -/
theorem p4Q2PZ37AET_originalOneLinkReceiver_givesNumeratorSlope
    (e : Link) (LF : ℝ) (hLF : 0 ≤ LF)
    (hLeft : ∀ (A B : Cfg) (i : Link) (g h xi : G),
      |F e (Function.update A i g,B) xi -
        F e (Function.update A i h,B) xi| ≤ LF * dJ g h)
    (hRightAway : ∀ (A B : Cfg) (i : Link), i ≠ e →
      ∀ (g h xi : G),
      |F e (A,Function.update B i g) xi -
        F e (A,Function.update B i h) xi| ≤ LF * dJ g h) :
    ∀ z w : Pair, |N e z-N e w| ≤ LF*D z w := by
  exact p4Q2PZ37AES_originalReceiverSlope_givesNumeratorUnitSlope
    H e LF hLF
    (p4Q2PZ37AET_originalOneLinkReceiver_givesFullSlope
      H e LF hLF hLeft hRightAway)

/-- A certified local D_J slope on all genuine input coordinates
EXCEPT the right receiver link gives a fully explicit AER radius and
original pair-Haar covariance-square two-ball floor. -/
theorem p4Q2PZ37AET_originalOneLinkCertified_explicitStableBall
    (e : Link) (a : Pair) (lambda M LF : ℝ)
    (ha : 0 < C b0 hb0 e a) (hlambda : 0 < lambda)
    (hM : 0 ≤ M) (hLF : 0 ≤ LF)
    (hQFloor : ∀ z : Pair, lambda ≤ q b0 hb0 z)
    (hNmax : ∀ z : Pair, |N e z| ≤ M)
    (hLeft : ∀ (A B : Cfg) (i : Link) (g h xi : G),
      |F e (Function.update A i g,B) xi -
        F e (Function.update A i h,B) xi| ≤ LF * dJ g h)
    (hRightAway : ∀ (A B : Cfg) (i : Link), i ≠ e →
      ∀ (g h xi : G),
      |F e (A,Function.update B i g) xi -
        F e (A,Function.update B i h) xi| ≤ LF * dJ g h) :
    ∃ R : ℝ,
      R = min ((lambda*C b0 hb0 e a/4)/(LF+1))
        (min 1
          ((lambda^2*C b0 hb0 e a/(4*(M+lambda)))/(Lq+1))) ∧
      0 < R ∧
      (∀ z w : Pair, D z w < R →
        |C b0 hb0 e z - C b0 hb0 e w| ≤ C b0 hb0 e a / 2) ∧
      (C b0 hb0 e a / 2)^2 *
        (2*(min (R/(2*(Fintype.card Link : ℝ)+1)) 2 / 4)^
          (8*Fintype.card Link)) ≤ S b0 hb0 e := by
  exact p4Q2PZ37AES_originalReceiverSlope_explicitRadius_unitCharacter
    H e a lambda M LF ha hlambda hM hLF hQFloor hNmax
    (p4Q2PZ37AET_originalOneLinkReceiver_givesFullSlope
      H e LF hLF hLeft hRightAway)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AET_realExpHarnack_of_absDifference
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AET_finiteTwoBoundary_absLipschitz
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AET_originalReceiver_ignoresRightReceiverLink
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AET_originalHaarNumerator_ignoresRightReceiverLink
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AET_originalOneLinkReceiver_givesFullSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AET_originalOneLinkReceiver_givesNumeratorSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AET_originalOneLinkCertified_explicitStableBall
