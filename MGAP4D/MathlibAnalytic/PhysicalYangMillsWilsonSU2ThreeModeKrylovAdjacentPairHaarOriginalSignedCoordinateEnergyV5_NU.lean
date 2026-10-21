import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianSignedMonomialV5_NT
import Mathlib.Tactic

/-!
# P4-Q2-NU — genuine Wilson–Perron signed finite-degree coordinate energies

NT proved that every authentic two-Wilson-posterior Perron-minus-Dirac
continuous functional is detected by ONE finite product of entries of
the existing actual real-eight SU(2) matrix embedding.

NU packages all such products at each finite degree n into a genuine
finite nonnegative sum of squared signed Haar-minus-Dirac moments:

  E_n = Σ_(q : Fin n → real-eight-coordinate-index)
          ( ∫ (Π_i J_(q_i)(g)) rho(g) dHaar(g)
                     - c Π_i J_(q_i)(y) )².

Every integral is genuine and integrable by continuity on compact SU(2).
For every beta>0, original posterior pair, Gauss-law source, true Perron
half-density and actual right-boundary link, SOME E_n is STRICTLY
POSITIVE without a hypothesis of rank, finite-point injection, or
nonzero physical detector. This is a finite-dimensional signed Fock
COORDINATE mode, NOT YET identified with the existing completed
Hilbert tensor-power signed Bochner moments or Gaussian double energy.

The remaining hard bridge is precisely identifying the signed energy
of exp(beta * original character) with the convergent positive series
of these actual E_n with normalization powers and factorials.
No fake posterior, new axiom, sorry, admit, Dobrushin, U0 or gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NU_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NU_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NU_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NU_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NU_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Index" => (Fin 2 × Fin 2) × Bool
local notation "coord" => p4Q2NO_originalSU2RealEightCoordinate

/-- Genuine finite-order coordinate product from SU(2)'s actual
eight real matrix entries, including the n=0 constant-one case. -/
noncomputable def p4Q2NU_originalRealEightCoordinateProduct
    (n : ℕ) (indices : Fin n → Index) : C(Gauge, ℝ) :=
  ((List.ofFn indices).map coord).prod

/-- Evaluate an arbitrary bounded real signed functional on one
true n-th order real-eight coordinate monomial. -/
noncomputable def p4Q2NU_originalSignedCoordinateMoment
    (L : C(Gauge, ℝ) →L[ℝ] ℝ)
    (n : ℕ) (indices : Fin n → Index) : ℝ :=
  L (p4Q2NU_originalRealEightCoordinateProduct n indices)

/-- The n-th positive finite-coordinate Fock mode energy for a
real signed continuous functional; no Hilbert tensor identification
is imposed by definition. -/
noncomputable def p4Q2NU_originalSignedCoordinateEnergy
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) (n : ℕ) : ℝ :=
  ∑ indices : Fin n → Index,
    (p4Q2NU_originalSignedCoordinateMoment L n indices) ^ 2

/-- Every finite-degree signed coordinate energy is nonnegative,
without a hypothesis on L or a Gaussian kernel. -/
theorem p4Q2NU_originalSignedCoordinateEnergy_nonneg
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) (n : ℕ) :
    0 ≤ p4Q2NU_originalSignedCoordinateEnergy L n := by
  unfold p4Q2NU_originalSignedCoordinateEnergy
  exact Finset.sum_nonneg (fun q hq => sq_nonneg _)

/-- One nonzero signed coordinate product produces a strictly positive
finite-degree scalar energy. This is a finite true coordinate argument,
not a claimed positive Gaussian double integral. -/
theorem p4Q2NU_originalSignedCoordinateEnergy_pos_of_moment_ne_zero
    (L : C(Gauge, ℝ) →L[ℝ] ℝ)
    (n : ℕ) (indices : Fin n → Index)
    (hNonzero : p4Q2NU_originalSignedCoordinateMoment L n indices ≠ 0) :
    0 < p4Q2NU_originalSignedCoordinateEnergy L n := by
  have hOne :
      0 < (p4Q2NU_originalSignedCoordinateMoment L n indices) ^ 2 :=
    sq_pos_of_ne_zero hNonzero
  unfold p4Q2NU_originalSignedCoordinateEnergy
  exact lt_of_lt_of_le hOne
    (Finset.single_le_sum
      (fun q hq =>
        sq_nonneg (p4Q2NU_originalSignedCoordinateMoment L n q))
      (Finset.mem_univ indices))

/-- Stone–Weierstrass plus NT implies every NONZERO bounded signed
functional has a strictly positive actual finite-coordinate energy
at some degree; the degree is not assumed in advance. -/
theorem p4Q2NU_nonzeroSignedFunctional_has_positiveCoordinateDegree
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ n : ℕ, 0 < p4Q2NU_originalSignedCoordinateEnergy L n := by
  obtain ⟨indices, hMoment⟩ :=
    p4Q2NT_nonzeroSignedFunctional_has_coordinateProductWitness L hL
  let q : Fin indices.length → Index := fun i => indices[i.1]
  have hProd :
      p4Q2NU_originalRealEightCoordinateProduct indices.length q =
        (indices.map coord).prod := by
    simp [p4Q2NU_originalRealEightCoordinateProduct, q]
  have hNonzero :
      p4Q2NU_originalSignedCoordinateMoment L indices.length q ≠ 0 := by
    simpa only [p4Q2NU_originalSignedCoordinateMoment, hProd] using hMoment
  exact ⟨indices.length,
    p4Q2NU_originalSignedCoordinateEnergy_pos_of_moment_ne_zero
      L indices.length q hNonzero⟩

/-- Apply the same finite-dimensional moment family to the ORIGINAL
physical Wilson–Perron density rho(g) and true signed point evaluation
at y. This is an exact finite sum of genuine signed Haar moments. -/
noncomputable def p4Q2NU_originalWilsonPerronSignedCoordinateEnergy
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (y : Gauge) (c : ℝ) (n : ℕ) : ℝ :=
  ∑ indices : Fin n → Index,
    ((∫ g : Gauge,
        (p4Q2NU_originalRealEightCoordinateProduct n indices) g *
          p4Q2NG_originalSpatialPerronSignedContrast H b hb e z g
        ∂normalizedCompactHaar Gauge) -
      c * (p4Q2NU_originalRealEightCoordinateProduct n indices) y) ^ 2

/-- Each signed Haar monomial pairing defining the GENUINE original
coordinate energy is integrable, from the proved original rho
continuity and compactness of SU(2), not a surrogate posterior. -/
theorem p4Q2NU_originalWilsonPerron_signedCoordinateMoment_integrable
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (n : ℕ) (indices : Fin n → Index) :
    Integrable
      (fun g : Gauge =>
        (p4Q2NU_originalRealEightCoordinateProduct n indices) g *
          p4Q2NG_originalSpatialPerronSignedContrast H b hb e z g)
      (normalizedCompactHaar Gauge) := by
  have hCont : Continuous (fun g : Gauge =>
        (p4Q2NU_originalRealEightCoordinateProduct n indices) g *
          p4Q2NG_originalSpatialPerronSignedContrast H b hb e z g) :=
    (p4Q2NU_originalRealEightCoordinateProduct n indices).continuous.mul
      (p4Q2NI_originalSpatialPerronSignedContrast_continuous
        H b hb e z)
  exact hCont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Identification of each actual rho-minus-Dirac signed coordinate
moment with the NJ physical continuous functional evaluation. -/
theorem p4Q2NU_originalWilsonPerron_signedCoordinateMoment_eq_trueIntegral
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (y : Gauge) (c : ℝ) (n : ℕ) (indices : Fin n → Index) :
    p4Q2NU_originalSignedCoordinateMoment
        (p4Q2NJ_originalSignedDiracDefectCLM H b hb e z y c)
        n indices =
      (∫ g : Gauge,
          (p4Q2NU_originalRealEightCoordinateProduct n indices) g *
            p4Q2NG_originalSpatialPerronSignedContrast H b hb e z g
          ∂normalizedCompactHaar Gauge) -
        c * (p4Q2NU_originalRealEightCoordinateProduct n indices) y := by
  exact p4Q2NJ_originalSignedDiracDefectCLM_apply
    H b hb e z y c (p4Q2NU_originalRealEightCoordinateProduct n indices)

/-- The explicitly integrated ORIGINAL signed Haar coordinate energy
is EXACTLY the canonical finite positive coordinate-moment energy;
no interchange or new regularity assumption is hidden. -/
theorem p4Q2NU_originalWilsonPerron_signedCoordinateEnergy_eq
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (y : Gauge) (c : ℝ) (n : ℕ) :
    p4Q2NU_originalWilsonPerronSignedCoordinateEnergy
        H b hb e z y c n =
      p4Q2NU_originalSignedCoordinateEnergy
        (p4Q2NJ_originalSignedDiracDefectCLM H b hb e z y c) n := by
  unfold p4Q2NU_originalWilsonPerronSignedCoordinateEnergy
    p4Q2NU_originalSignedCoordinateEnergy
  apply Finset.sum_congr rfl
  intro indices hi
  rw [p4Q2NU_originalWilsonPerron_signedCoordinateMoment_eq_trueIntegral]

/-- MAIN genuine signed-measure consequence: for every beta>0, the
UNALTERED interacting Wilson–Perron posterior contrast minus ANY Dirac
evaluation has some finite-order coordinate-energy E_n STRICTLY
POSITIVE. The exact Gaussian double-energy series remains OPEN. -/
theorem p4Q2NU_originalWilsonPerron_signedCoordinateEnergy_someDegree_pos
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b) (bpos : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (y : Gauge) (c : ℝ) :
    ∃ n : ℕ, 0 <
      p4Q2NU_originalWilsonPerronSignedCoordinateEnergy H b hb e z y c n := by
  obtain ⟨n, hn⟩ :=
    p4Q2NU_nonzeroSignedFunctional_has_positiveCoordinateDegree
      (p4Q2NJ_originalSignedDiracDefectCLM H b hb e z y c)
      (p4Q2NJ_originalSignedDiracDefectCLM_ne_zero H b hb bpos e z y c)
  refine ⟨n, ?_⟩
  rw [p4Q2NU_originalWilsonPerron_signedCoordinateEnergy_eq]
  exact hn

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NU_originalSignedCoordinateEnergy_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NU_originalSignedCoordinateEnergy_pos_of_moment_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NU_nonzeroSignedFunctional_has_positiveCoordinateDegree
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NU_originalWilsonPerron_signedCoordinateMoment_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NU_originalWilsonPerron_signedCoordinateMoment_eq_trueIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NU_originalWilsonPerron_signedCoordinateEnergy_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NU_originalWilsonPerron_signedCoordinateEnergy_someDegree_pos
