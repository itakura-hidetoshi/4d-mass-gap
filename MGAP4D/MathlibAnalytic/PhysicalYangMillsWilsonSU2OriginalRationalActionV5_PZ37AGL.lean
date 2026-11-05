import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalKernelTaylorIntervalV5_PZ37AGJ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalExact24CenterFourModeV5_PZ37AFX
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGL — exact rational evaluation of ORIGINAL finite Wilson actions

Rational arithmetic is linked to the ACTUAL first-column coordinates of
an existing original SU(2) element. The matrix convention is
  [[x0 + I*x1, -x2 + I*x3], [x2 + I*x3, x0 - I*x1]].
Thus multiplication signs must be derived from these original matrices,
not imported from a differently oriented quaternion convention.

We prove closure of rational coordinate witnesses under actual group
multiplication and inverse, then extract actual Wilson energy as 1-x0.
These witnesses evaluate the original spatial plaquette holonomies,
original temporal relative holonomies, and the ORIGINAL one-slab action.
The established AFQ 24 centers have such witnesses by AFX, without an
external action-value oracle. Their full original action interval has
zero width and can be supplied to the existing AGJ kernel evaluator.

The arithmetic on supplied finite data is rational. Enumeration of the
existing canonical spatial lists is still noncomputable; this module does
not claim an executed large-volume table or effective complexity bound.
Haar cell masses, the centered-source mean, and any actual nonzero signed
transfer remain separate obligations. No shell, volume-uniform coercivity,
Hamiltonian gap or continuum four-dimensional mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators ComplexConjugate
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Coordinate multiplication in the actual original matrix convention. -/
def p4Q2PZ37AGL_coordinateMul {R : Type*} [CommRing R]
    (a b : Fin 4 → R) : Fin 4 → R :=
  ![a 0*b 0-a 1*b 1-a 2*b 2-a 3*b 3,
    a 0*b 1+a 1*b 0-a 2*b 3+a 3*b 2,
    a 2*b 0-a 3*b 1+a 0*b 2+a 1*b 3,
    a 2*b 1+a 3*b 0+a 0*b 3-a 1*b 2]

def p4Q2PZ37AGL_coordinateInv {R : Type*} [CommRing R]
    (a : Fin 4 → R) : Fin 4 → R := ![a 0, -a 1, -a 2, -a 3]

/-- Pure arithmetic regression for the noncommutative orientation. -/
theorem p4Q2PZ37AGL_orientation_checked :
    p4Q2PZ37AGL_coordinateMul (![0,1,0,0] : Fin 4 → ℚ) ![0,0,1,0] =
      ![0,0,0,-1] ∧
    p4Q2PZ37AGL_coordinateMul (![0,0,1,0] : Fin 4 → ℚ) ![0,1,0,0] =
      ![0,0,0,1] := by
  constructor <;> funext i <;> fin_cases i <;>
    norm_num [p4Q2PZ37AGL_coordinateMul]

theorem p4Q2PZ37AGL_inverse_checked :
    p4Q2PZ37AGL_coordinateMul (![0,1,0,0] : Fin 4 → ℚ)
      (p4Q2PZ37AGL_coordinateInv ![0,1,0,0]) = ![1,0,0,0] := by
  funext i
  fin_cases i <;> norm_num [p4Q2PZ37AGL_coordinateMul, p4Q2PZ37AGL_coordinateInv]

noncomputable section
open scoped Topology Classical InnerProductSpace ENNReal

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
local notation "V" => p4Q2PZ37ADR_originalFourCoordinates
local notation "Grid" => p4Q2PZ37AFQ_GridIndex

/-- Derive the original multiplication formula before using rational data. -/
theorem p4Q2PZ37AGL_originalCoordinates_mul (g h : G) (j : Fin 4) :
    V (g * h) j = p4Q2PZ37AGL_coordinateMul
      (fun i => V g i) (fun i => V h i) j := by
  have h01 : (g : Mat) 0 1 = -conj ((g : Mat) 1 0) := by
    simpa using congrArg (fun M : Mat => M 0 1)
      (p4Q2PZ37ADR_originalMatrix_fromFirstColumn g)
  have h11 : (g : Mat) 1 1 = conj ((g : Mat) 0 0) := by
    simpa using congrArg (fun M : Mat => M 1 1)
      (p4Q2PZ37ADR_originalMatrix_fromFirstColumn g)
  have hm : ((g * h : G) : Mat) = (g : Mat) * (h : Mat) := rfl
  fin_cases j <;>
    simp [p4Q2PZ37ADR_originalFourCoordinates, p4Q2PZ37AGL_coordinateMul,
      hm, Matrix.mul_apply, Fin.sum_univ_two, h01, h11,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem p4Q2PZ37AGL_originalCoordinates_inv (g : G) (j : Fin 4) :
    V g⁻¹ j = p4Q2PZ37AGL_coordinateInv (fun i => V g i) j := by
  have h01 : (g : Mat) 0 1 = -conj ((g : Mat) 1 0) := by
    simpa using congrArg (fun M : Mat => M 0 1)
      (p4Q2PZ37ADR_originalMatrix_fromFirstColumn g)
  have hm : ((g⁻¹ : G) : Mat) = Matrix.conjTranspose (g : Mat) := rfl
  fin_cases j <;>
    simp [p4Q2PZ37ADR_originalFourCoordinates, p4Q2PZ37AGL_coordinateInv,
      hm, Matrix.conjTranspose_apply, h01]

/-- This is the original Wilson energy, not a proxy quaternion function. -/
theorem p4Q2PZ37AGL_originalEnergy_coordinate (g : G) :
    specialUnitaryWilsonPlaquetteEnergy 2 g = 1 - V g 0 := by
  have h11 : (g : Mat) 1 1 = conj ((g : Mat) 0 0) := by
    simpa using congrArg (fun M : Mat => M 1 1)
      (p4Q2PZ37ADR_originalMatrix_fromFirstColumn g)
  change 1 - (Matrix.trace (g : Mat)).re / (2 : ℝ) = 1 - V g 0
  simp [Matrix.trace_fin_two, h11, p4Q2PZ37ADR_originalFourCoordinates] <;> ring

/-- Rational data with pointwise evidence for one actual original group element. -/
structure p4Q2PZ37AGL_rationalCoordinates (g : G) where
  value : Fin 4 → ℚ
  hValue : ∀ j, V g j = (value j : ℝ)

namespace p4Q2PZ37AGL_rationalCoordinates

variable {g h : G}

def mul (a : p4Q2PZ37AGL_rationalCoordinates g)
    (b : p4Q2PZ37AGL_rationalCoordinates h) :
    p4Q2PZ37AGL_rationalCoordinates (g * h) where
  value := p4Q2PZ37AGL_coordinateMul a.value b.value
  hValue := by
    intro j
    rw [p4Q2PZ37AGL_originalCoordinates_mul]
    fin_cases j <;> simp [p4Q2PZ37AGL_coordinateMul, a.hValue, b.hValue]

def inv (a : p4Q2PZ37AGL_rationalCoordinates g) :
    p4Q2PZ37AGL_rationalCoordinates g⁻¹ where
  value := p4Q2PZ37AGL_coordinateInv a.value
  hValue := by
    intro j
    rw [p4Q2PZ37AGL_originalCoordinates_inv]
    fin_cases j <;> simp [p4Q2PZ37AGL_coordinateInv, a.hValue]

def energy (a : p4Q2PZ37AGL_rationalCoordinates g) : ℚ := 1 - a.value 0

theorem energy_exact (a : p4Q2PZ37AGL_rationalCoordinates g) :
    specialUnitaryWilsonPlaquetteEnergy 2 g = (a.energy : ℝ) := by
  rw [p4Q2PZ37AGL_originalEnergy_coordinate, a.hValue 0]
  simp [energy]

end p4Q2PZ37AGL_rationalCoordinates

/-- All established AFQ centers have original rational coordinate evidence. -/
def p4Q2PZ37AGL_originalCenter_rational
    (i : Fin (Fintype.card Grid)) :
    p4Q2PZ37AGL_rationalCoordinates (p4Q2PZ37AFQ_originalCenters i) where
  value := p4Q2PZ37AFX_gridCoordinate ((Fintype.equivFin Grid).symm i)
  hValue := by
    intro j
    rw [p4Q2PZ37AFX_originalCenter_coordinates]
    exact p4Q2PZ37AFX_gridCoordinate_exact ((Fintype.equivFin Grid).symm i) j

/-- Cast a finite evaluation only after proving each actual summand exact. -/
theorem p4Q2PZ37AGL_finiteSum_exact {ι : Type*}
    (xs : List ι) (f : ι → ℝ) (q : ι → ℚ) (h : ∀ i, f i = (q i : ℝ)) :
    (xs.map f).sum = ((xs.map q).sum : ℚ) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simpa only [List.map_cons, List.sum_cons, Rat.cast_add, h x] using
      congrArg (fun z : ℝ => (q x : ℝ) + z) ih

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Plq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Cross" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "S" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2

/-- The actual four-link original plaquette word, with its order preserved. -/
def p4Q2PZ37AGL_originalPlaquette_rational
    (A : Cfg) (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e)) (p : Plq) :
    p4Q2PZ37AGL_rationalCoordinates
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p) :=
  (((a (p.1, p.2.1.1)).mul
      (a (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.1, p.2.1.2))).mul
      ((a (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.2, p.2.1.1)).inv)).mul
      ((a (p.1, p.2.1.2)).inv)

def p4Q2PZ37AGL_spatialActionRational
    (A : Cfg) (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e)) : ℚ :=
  ((periodicHypercubicEvenSpatialSlicePlaquetteList H).map
    (fun p => (p4Q2PZ37AGL_originalPlaquette_rational H A a p).energy)).sum

theorem p4Q2PZ37AGL_originalSpatialAction_exact
    (A : Cfg) (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e)) :
    W A = (p4Q2PZ37AGL_spatialActionRational H A a : ℝ) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction
    p4Q2PZ37AGL_spatialActionRational
  exact p4Q2PZ37AGL_finiteSum_exact _ _ _
    (fun p => (p4Q2PZ37AGL_originalPlaquette_rational H A a p).energy_exact)

def p4Q2PZ37AGL_crossingActionRational
    (A B : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e))
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) : ℚ :=
  ((periodicHypercubicEvenSpatialSliceLinkList H).map
    (fun e => ((a e).inv.mul (b e)).energy)).sum

theorem p4Q2PZ37AGL_originalCrossingAction_exact
    (A B : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e))
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) :
    Cross A B = (p4Q2PZ37AGL_crossingActionRational H A B a b : ℝ) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
    p4Q2PZ37AGL_crossingActionRational
  exact p4Q2PZ37AGL_finiteSum_exact _ _ _
    (fun e => ((a e).inv.mul (b e)).energy_exact)

def p4Q2PZ37AGL_slabActionRational
    (A B : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e))
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) : ℚ :=
  (1 / 2 : ℚ) * p4Q2PZ37AGL_spatialActionRational H A a +
    p4Q2PZ37AGL_crossingActionRational H A B a b +
    (1 / 2 : ℚ) * p4Q2PZ37AGL_spatialActionRational H B b

/-- An equality for the literal ORIGINAL one-slab action, not a surrogate. -/
theorem p4Q2PZ37AGL_originalSlabAction_exact
    (A B : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e))
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) :
    S A B = (p4Q2PZ37AGL_slabActionRational H A B a b : ℝ) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
    p4Q2PZ37AGL_slabActionRational
  rw [p4Q2PZ37AGL_originalSpatialAction_exact H A a,
    p4Q2PZ37AGL_originalCrossingAction_exact H A B a b,
    p4Q2PZ37AGL_originalSpatialAction_exact H B b]
  push_cast
  ring

/-- Zero-width action input for AGJ, justified by the actual finite word. -/
def p4Q2PZ37AGL_originalSlabActionSingleton
    (A B : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e))
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) :
    p4Q2PZ37AFV_verifiedInterval (S A B) where
  lower := p4Q2PZ37AGL_slabActionRational H A B a b
  upper := p4Q2PZ37AGL_slabActionRational H A B a b
  hLower := (p4Q2PZ37AGL_originalSlabAction_exact H A B a b).symm.le
  hUpper := (p4Q2PZ37AGL_originalSlabAction_exact H A B a b).le

/-- Every assignment of the existing genuine AFQ 24 centers to the
original spatial links supplies the action singleton without an oracle. -/
def p4Q2PZ37AGL_original24CenterActionSingleton
    (left right : Link → Fin (Fintype.card Grid)) :
    p4Q2PZ37AFV_verifiedInterval
      (S (fun e => p4Q2PZ37AFQ_originalCenters (left e))
        (fun e => p4Q2PZ37AFQ_originalCenters (right e))) :=
  p4Q2PZ37AGL_originalSlabActionSingleton H _ _
    (fun e => p4Q2PZ37AGL_originalCenter_rational (left e))
    (fun e => p4Q2PZ37AGL_originalCenter_rational (right e))

theorem p4Q2PZ37AGL_original24CenterAction_zeroWidth
    (left right : Link → Fin (Fintype.card Grid)) :
    (p4Q2PZ37AGL_original24CenterActionSingleton H left right).upper -
      (p4Q2PZ37AGL_original24CenterActionSingleton H left right).lower = 0 := by
  simp [p4Q2PZ37AGL_original24CenterActionSingleton,
    p4Q2PZ37AGL_originalSlabActionSingleton]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGL_orientation_checked
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGL_inverse_checked
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGL_originalCoordinates_mul
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGL_originalCoordinates_inv
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGL_originalEnergy_coordinate
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGL_rationalCoordinates.mul
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGL_rationalCoordinates.inv
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGL_rationalCoordinates.energy_exact
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGL_originalCenter_rational
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGL_finiteSum_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGL_originalPlaquette_rational
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGL_originalSpatialAction_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGL_originalCrossingAction_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGL_originalSlabAction_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGL_originalSlabActionSingleton
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGL_original24CenterActionSingleton
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGL_original24CenterAction_zeroWidth
