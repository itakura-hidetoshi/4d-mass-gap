import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedCoordinateEnergyV5_NU
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# P4-Q2-NV — all-degree ACTUAL SU2 temporal Wilson character coordinate expansion

NU proved that a nonzero genuine original Wilson–Perron-minus-Dirac
signed functional has some strictly positive n-th coordinate moment
square energy E_n. The missing analytical bridge is identifying these
positive moments with the original temporal Wilson Gaussian kernel.

NV supplies the exact finite-dimensional ALGEBRAIC step for every n:
the ACTUAL normalized SU(2) fundamental temporal character chi(x,g)
is a HALF of the sum of eight real coordinate products, and its n-th
power is a half^n-weighted finite Gram sum of the genuine coordinate
monomials from NU.

  chi(x,g)^n = (1/2)^n Σ_(q : Fin n → Index) m_q(x)m_q(g).

We reuse the canonical SU2 real-eight matrix feature and mathlib
Fintype.sum_pow, not an invented rank, representation or surrogate
kernel. This is the crucial pointwise polynomial Fock bridge; it is
NOT YET the signed double Haar integral identity or complete
exponential energy expansion. Real Wilson posterior pair, Perron
half-density, Gauss-law source and spatial Wilson factors are untouched.

All scalar Wilson weights (b/2)^n/n! are strictly positive for b>0,
and NU guarantees some strictly positive genuinely signed coefficient.
No sorry, admit, new axiom, Dobrushin, U0, H1-C3 or continuum gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NV_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NV_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NV_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NV_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NV_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Index" => (Fin 2 × Fin 2) × Bool
local notation "coord" => p4Q2NO_originalSU2RealEightCoordinate
local notation "J" => specialUnitaryMatrixRealFeature 2
local notation "chi" => p4Q2NG_originalSU2TemporalCharacter

/-- Point evaluation of a finite product of REAL continuous SU(2)
matrix coordinate maps is the finite product of the scalar evaluations.
This step is a mathlib commutative-monoid homomorphism computation. -/
private theorem p4Q2NV_coordinateListProduct_eval
    (ls : List Index) (g : Gauge) :
    ((ls.map coord).prod) g =
      (ls.map (fun q => coord q g)).prod := by
  induction ls with
  | nil => simp
  | cons q qs ih => simp [ih]

/-- Exact indexed form of NU's already-defined genuine
finite-dimensional SU(2) real-coordinate monomial. -/
theorem p4Q2NV_originalRealEightCoordinateProduct_apply
    (n : ℕ) (indices : Fin n → Index) (g : Gauge) :
    (p4Q2NU_originalRealEightCoordinateProduct n indices) g =
      ∏ i : Fin n, coord (indices i) g := by
  calc
    (p4Q2NU_originalRealEightCoordinateProduct n indices) g =
        (((List.ofFn indices).map coord).prod) g := rfl
    _ = ((List.ofFn indices).map (fun q => coord q g)).prod :=
      p4Q2NV_coordinateListProduct_eval (List.ofFn indices) g
    _ = ∏ i : Fin n, coord (indices i) g := by
      rw [List.map_ofFn, Fin.prod_ofFn]

/-- The original normalized Wilson temporal character is the HALF
of the scalar Gram sum of the genuine eight matrix coordinates. -/
theorem p4Q2NV_originalTemporalCharacter_eq_realEightCoordinateSum
    (x g : Gauge) :
    chi x g =
      (∑ q : Index, coord q x * coord q g) / 2 := by
  rw [p4Q2NM_originalSU2TemporalCharacter_eq_half_realEight_inner]
  rw [PiLp.inner_apply]
  simp only [realScalarInner_eq_mul]
  rfl

/-- MAIN all-order pointwise monomial Fock identity for the EXACT
original SU(2) Wilson temporal character. No formal signed
integration, density or synthetic posterior is smuggled in. -/
theorem p4Q2NV_originalTemporalCharacter_power_eq_coordinateGram
    (n : ℕ) (x g : Gauge) :
    (chi x g)^n =
      (1 / 2 : ℝ)^n *
        (∑ indices : Fin n → Index,
          (p4Q2NU_originalRealEightCoordinateProduct n indices) x *
            (p4Q2NU_originalRealEightCoordinateProduct n indices) g) := by
  calc
    (chi x g)^n =
        ((1 / 2 : ℝ) *
          (∑ q : Index, coord q x * coord q g)) ^ n := by
      rw [p4Q2NV_originalTemporalCharacter_eq_realEightCoordinateSum]
      ring
    _ = (1 / 2 : ℝ)^n *
          ((∑ q : Index, coord q x * coord q g) ^ n) := by rw [mul_pow]
    _ = (1 / 2 : ℝ)^n *
          (∑ indices : Fin n → Index,
            ∏ i : Fin n,
              (coord (indices i) x * coord (indices i) g)) := by
      rw [Fintype.sum_pow]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro indices hi
      rw [Finset.prod_mul_distrib]
      rw [← p4Q2NV_originalRealEightCoordinateProduct_apply n indices x,
        ← p4Q2NV_originalRealEightCoordinateProduct_apply n indices g]

/-- The Wilson character Fock coefficient for these REAL coordinate
monomials has STRICTLY POSITIVE scalar weight for every b>0,n. -/
theorem p4Q2NV_originalTemporalCoordinateTaylorCoefficient_pos
    (b : ℝ) (hb : 0 < b) (n : ℕ) :
    0 < (b / 2)^n / (n.factorial : ℝ) := by
  positivity

/-- The GENUINE signed Wilson–Perron coordinate moments constructed in
NU have at least ONE strictly positive contribution after inclusion
of the exact positive Wilson exponential coefficient.

This is NOT YET a lower bound for the actual Gaussian double energy
until the signed integral/series compatibility identity is proved. -/
theorem p4Q2NV_originalWilsonPerron_someWeightedSignedCoordinateEnergy_pos
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b) (bpos : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (y : Gauge) (c : ℝ) :
    ∃ n : ℕ, 0 <
      ((b / 2)^n / (n.factorial : ℝ)) *
        p4Q2NU_originalWilsonPerronSignedCoordinateEnergy
          H b hb e z y c n := by
  obtain ⟨n, hn⟩ :=
    p4Q2NU_originalWilsonPerron_signedCoordinateEnergy_someDegree_pos
      H b hb bpos e z y c
  exact ⟨n,
    mul_pos (p4Q2NV_originalTemporalCoordinateTaylorCoefficient_pos
      b bpos n) hn⟩

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NV_originalRealEightCoordinateProduct_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NV_originalTemporalCharacter_eq_realEightCoordinateSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NV_originalTemporalCharacter_power_eq_coordinateGram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NV_originalTemporalCoordinateTaylorCoefficient_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NV_originalWilsonPerron_someWeightedSignedCoordinateEnergy_pos
