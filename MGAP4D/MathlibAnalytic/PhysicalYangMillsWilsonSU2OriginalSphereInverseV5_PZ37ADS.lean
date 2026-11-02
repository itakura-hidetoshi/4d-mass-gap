import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSphereCoordinatesV5_PZ37ADR
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADS — genuine SU(2) and unit 3-sphere inverse maps

The actual original Matrix.specialUnitaryGroup (Fin 2) ℂ is used.
ADR already gave an injective original SU(2) → S³ first-column map.
ADS constructs its opposite map at every actual S³ point, using
[a, -conj b; b, conj a] with a,b recovered from the FOUR REAL coordinates.
The real sphere condition proves the genuine determinant-one matrix
membership, not a surrogate group or a separate probability space.

The new concrete maps are inverse in both directions; the induced
Equiv is about ORIGINAL SU(2) and the actual Mathlib unit sphere.
This proves the formerly missing *bijectivity* part of ADQ's
Haar transfer bridge, but DOES NOT yet prove its measure-preserving
condition nor its ADK chordal ball/isometry condition. Those are
separate remaining obligations. No physical sources/posteriors,
normalized original Haar, true boundary pair-Haar or theorem root
is changed, and no mass gap conclusion is inferred.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators ComplexConjugate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S3" => Metric.sphere (0 : E4) 1

/-- Actual complex number reconstructed from the first two original
real sphere coordinates. -/
def p4Q2PZ37ADS_sphereA (x : S3) : ℂ :=
  ⟨(x : E4) 0, (x : E4) 1⟩

/-- Actual complex number reconstructed from the second two sphere
coordinates. -/
def p4Q2PZ37ADS_sphereB (x : S3) : ℂ :=
  ⟨(x : E4) 2, (x : E4) 3⟩

/-- A true point of the real 3-sphere is exactly a normalized
pair of complex numbers; no Haar claim is used. -/
theorem p4Q2PZ37ADS_sphere_complex_normSq_one (x : S3) :
    Complex.normSq (p4Q2PZ37ADS_sphereA x) +
      Complex.normSq (p4Q2PZ37ADS_sphereB x) = 1 := by
  have hx : ‖(x : E4)‖ = 1 := by
    simpa only [dist_zero_right] using x.property
  have hSq : ‖(x : E4)‖ ^ 2 = 1 := by
    rw [hx]
    norm_num
  rw [EuclideanSpace.real_norm_sq_eq] at hSq
  simpa [p4Q2PZ37ADS_sphereA, p4Q2PZ37ADS_sphereB,
    Complex.normSq_apply, Fin.sum_univ_four, pow_two,
    add_assoc, add_left_comm, add_comm] using hSq

/-- Algebraic membership of a quaternion-shaped matrix in the
ORIGINAL SU(2) subtype, established from actual complex normSq.
No assumed group structure on an abstract S³ is used. -/
theorem p4Q2PZ37ADS_quaternionMatrix_mem_originalSU2
    (a b : ℂ) (h : Complex.normSq a + Complex.normSq b = 1) :
    !![a, -conj b; b, conj a] ∈
      Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  let M : Mat := !![a, -conj b; b, conj a]
  have hC : a * conj a + b * conj b = (1 : ℂ) := by
    calc
      a * conj a + b * conj b =
          (Complex.normSq a : ℂ) + (Complex.normSq b : ℂ) := by
            rw [Complex.mul_conj, Complex.mul_conj]
      _ = 1 := by exact_mod_cast h
  have hDet : M.det = 1 := by
    dsimp [M]
    rw [Matrix.det_fin_two]
    change a * conj a - (-conj b) * b = 1
    calc
      a * conj a - (-conj b) * b =
          a * conj a + b * conj b := by ring
      _ = 1 := hC
  have hAdj : M.conjTranspose = M.adjugate := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.adjugate_fin_two, Matrix.conjTranspose_apply]
  have hUnit : M * star M = (1 : Mat) := by
    calc
      M * star M = M * M.conjTranspose := by
        rw [Matrix.star_eq_conjTranspose]
      _ = M * M.adjugate := by rw [hAdj]
      _ = M.det • (1 : Mat) := Matrix.mul_adjugate M
      _ = 1 := by rw [hDet]; simp
  change M ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ
  exact (Matrix.mem_specialUnitaryGroup_iff).mpr
    ⟨(Matrix.mem_unitaryGroup_iff).mpr hUnit, hDet⟩

/-- Explicit inverse map into the SAME original SU(2) gauge group.
This is a real group element, not a made-up quaternionic measure. -/
def p4Q2PZ37ADS_originalSphereToSU2 (x : S3) : G :=
  ⟨!![p4Q2PZ37ADS_sphereA x, -conj (p4Q2PZ37ADS_sphereB x);
       p4Q2PZ37ADS_sphereB x, conj (p4Q2PZ37ADS_sphereA x)],
   p4Q2PZ37ADS_quaternionMatrix_mem_originalSU2
     (p4Q2PZ37ADS_sphereA x) (p4Q2PZ37ADS_sphereB x)
     (p4Q2PZ37ADS_sphere_complex_normSq_one x)⟩

/-- First complex column of the inverse map retains precisely
the two reconstructed coordinates. -/
theorem p4Q2PZ37ADS_inverse_firstColumn (x : S3) :
    p4Q2PZ37ADR_originalFirstColumn
      (p4Q2PZ37ADS_originalSphereToSU2 x) =
      (p4Q2PZ37ADS_sphereA x, p4Q2PZ37ADS_sphereB x) := by
  rfl

/-- The canonical sphere → genuine SU(2) → sphere composition is
literally the identity on every S³ point. -/
theorem p4Q2PZ37ADS_sphere_roundtrip (x : S3) :
    p4Q2PZ37ADR_originalSU2ToSphere
      (p4Q2PZ37ADS_originalSphereToSU2 x) = x := by
  apply Subtype.ext
  change p4Q2PZ37ADR_originalFourCoordinates
      (p4Q2PZ37ADS_originalSphereToSU2 x) = (x : E4)
  ext i
  fin_cases i <;>
    simp [p4Q2PZ37ADR_originalFourCoordinates,
      p4Q2PZ37ADS_originalSphereToSU2,
      p4Q2PZ37ADS_sphereA, p4Q2PZ37ADS_sphereB]

/-- The opposite genuine SU(2) → sphere → SU(2) composition
is identity, using ADR's proved original embedding injectivity. -/
theorem p4Q2PZ37ADS_originalSU2_roundtrip (g : G) :
    p4Q2PZ37ADS_originalSphereToSU2
      (p4Q2PZ37ADR_originalSU2ToSphere g) = g := by
  apply p4Q2PZ37ADR_originalSU2ToSphere_injective
  exact p4Q2PZ37ADS_sphere_roundtrip
    (p4Q2PZ37ADR_originalSU2ToSphere g)

/-- The original SU(2) first-column sphere map is genuinely
surjective onto ALL of the mathematical unit 3-sphere. -/
theorem p4Q2PZ37ADS_originalSU2ToSphere_surjective :
    Function.Surjective p4Q2PZ37ADR_originalSU2ToSphere := by
  intro x
  exact ⟨p4Q2PZ37ADS_originalSphereToSU2 x,
    p4Q2PZ37ADS_sphere_roundtrip x⟩

/-- The genuine original SU(2) first-column map is a bijection. -/
theorem p4Q2PZ37ADS_originalSU2ToSphere_bijective :
    Function.Bijective p4Q2PZ37ADR_originalSU2ToSphere :=
  ⟨p4Q2PZ37ADR_originalSU2ToSphere_injective,
   p4Q2PZ37ADS_originalSU2ToSphere_surjective⟩

/-- Fully concrete equivalence of the ORIGINAL SU(2) group carrier
and the Mathlib real unit 3-sphere, with both inverses PROVED.
This is deliberately not yet a measure-space or isometric equivalence. -/
def p4Q2PZ37ADS_originalSU2EquivSphere : G ≃ S3 where
  toFun := p4Q2PZ37ADR_originalSU2ToSphere
  invFun := p4Q2PZ37ADS_originalSphereToSU2
  left_inv := p4Q2PZ37ADS_originalSU2_roundtrip
  right_inv := p4Q2PZ37ADS_sphere_roundtrip

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADS_sphere_complex_normSq_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADS_quaternionMatrix_mem_originalSU2
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADS_inverse_firstColumn
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADS_sphere_roundtrip
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADS_originalSU2_roundtrip
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADS_originalSU2ToSphere_surjective
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADS_originalSU2ToSphere_bijective
