import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianStoneWeierstrassV5_NO
import MGAP4D.MathlibAnalytic.RealKernelPositiveSemidefiniteCertificateAlgebra
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelPositiveSemidefiniteCertificate
import Mathlib.Tactic

/-!
# P4-Q2-NP — original SU2 Wilson temporal PSD and genuine signed polynomial witness

Reuse the EXISTING genuine SU(N) Wilson relative kernel PSD proof and
the exact original SU2 Gaussian formula to obtain a PSD certificate for the
real original temporal exponential k_b(x,g)=exp(b chi(x⁻¹g)).
Unlike the NN two-point determinant, this holds for every finite Gram
quadratic form, but only NONNEGATIVITY is claimed, not arbitrary-n strictness.

NO proved Stone–Weierstrass density of the actual eight matrix-coordinate
polynomial algebra. Combining it with NI/NJ's established NONZERO authentic
signed Wilson–Perron-minus-Dirac continuous linear functional yields a
coordinate POLYNOMIAL witness for that actual functional. No auxiliary
measure, physical source, posterior or rank condition is invented.

Still OPEN: fixed-b real kernel-section LINEAR-SPAN density, finite-n
strict Gram positivity, the all-order Fock Gaussian moment identity,
the authentic physical signed receiver's unconditional positive variance,
GI covariance, H1-C3 and continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NP_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NP_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NP_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NP_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NP_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "k" => p4Q2NJ_originalSU2WilsonTemporalSection

/-- The original SU2 Wilson temporal character exponential, at any beta≥0,
has a FULL finite-family positive-semidefinite certificate, by the
already proven exact genuine SU2 relative Wilson kernel plus exp(b) scaling.
No surrogate Gaussian measure or unrelated kernel is introduced. -/
noncomputable def p4Q2NP_originalSU2WilsonTemporalPSDCertificate
    (b : ℝ) (hb : 0 ≤ b) :
    RealKernelPositiveSemidefiniteCertificate Gauge (fun x g => k b x g) := by
  let C : RealKernelPositiveSemidefiniteCertificate Gauge
      (specialUnitaryWilsonRelativeKernel 2 b) :=
    specialUnitaryWilsonRelativeKernel_positiveSemidefiniteCertificate
      2 (by norm_num) b hb
  have hk : (fun x g : Gauge => k b x g) =
      (fun x g : Gauge =>
        Real.exp b * specialUnitaryWilsonRelativeKernel 2 b x g) := by
    funext x g
    rw [p4Q2NM_originalSU2TemporalWilsonSection_eq_realEightGaussian,
      p4Q2NM_originalSU2WilsonRelativeKernel_eq_realEightGaussian]
  rw [hk]
  exact C.nonnegSMul (Real.exp b) (Real.exp_pos b).le

/-- Every finite quadratic form of the EXACT original temporal
SU2 Wilson kernel is nonnegative, for arbitrary finite indexing type,
actual SU2 points (allowing repeats), and arbitrary REAL coefficients. -/
theorem p4Q2NP_originalSU2WilsonTemporal_allFiniteGram_nonneg
    (b : ℝ) (hb : 0 ≤ b)
    {ι : Type} [Fintype ι]
    (points : ι → Gauge) (coefficients : ι → ℝ) :
    0 ≤ ∑ i : ι, ∑ j : ι,
      coefficients i * coefficients j * k b (points i) (points j) :=
  (p4Q2NP_originalSU2WilsonTemporalPSDCertificate b hb).positiveSemidefinite
    ι points coefficients

/-- The genuine SU2 real-eight coordinate polynomial subalgebra,
whose density was proved in NO, is dense as a SET of continuous
functions, hence also has dense real linear span. -/
theorem p4Q2NP_originalSU2RealEightPolynomialAlgebra_dense :
    Dense
      (↑p4Q2NO_originalSU2RealEightPolynomialAlgebra : Set C(Gauge, ℝ)) := by
  apply dense_iff_closure_eq.mpr
  rw [← Subalgebra.topologicalClosure_coe]
  rw [p4Q2NO_originalSU2RealEightPolynomialAlgebra_closure_eq_top]
  rfl

/-- For every genuine two-Wilson-posterior signed Perron density and every
Dirac coefficient/location, an actual polynomial of the existing eight
SU2 real matrix coordinates separates that signed functional from Dirac.
This upgrades NI's arbitrary continuous signed witness to a concrete
coordinate-polynomial witness without modifying its physical source.

It does NOT say any fixed-beta Gaussian section detects the functional:
that is the separate unresolved Fock moment-completeness bridge. -/
theorem p4Q2NP_originalSignedDiracDefect_detected_by_realEightPolynomial
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b) (bpos : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (y : Gauge) (c : ℝ) :
    ∃ f : C(Gauge, ℝ),
      f ∈ p4Q2NO_originalSU2RealEightPolynomialAlgebra ∧
        p4Q2NJ_originalSignedDiracDefectCLM H b hb e z y c f ≠ 0 := by
  let L : C(Gauge, ℝ) →L[ℝ] ℝ :=
    p4Q2NJ_originalSignedDiracDefectCLM H b hb e z y c
  have hLne : L ≠ 0 :=
    p4Q2NJ_originalSignedDiracDefectCLM_ne_zero H b hb
      bpos e z y c
  by_contra hExists
  have hVanish (f : C(Gauge, ℝ))
      (hf : f ∈ p4Q2NO_originalSU2RealEightPolynomialAlgebra) :
      L f = 0 := by
    by_contra hNot
    exact hExists ⟨f, hf, hNot⟩
  have hEq : Set.EqOn (⇑L) (⇑(0 : C(Gauge, ℝ) →L[ℝ] ℝ))
      (↑p4Q2NO_originalSU2RealEightPolynomialAlgebra : Set C(Gauge, ℝ)) := by
    intro f hf
    simpa using hVanish f hf
  have hDenseSpan :
      Dense
        (↑(Submodule.span ℝ
          (↑p4Q2NO_originalSU2RealEightPolynomialAlgebra : Set C(Gauge, ℝ)))
          : Set C(Gauge, ℝ)) :=
    p4Q2NP_originalSU2RealEightPolynomialAlgebra_dense.mono
      (Submodule.subset_span)
  have hLzero : L = 0 := ContinuousLinearMap.ext_on hDenseSpan hEq
  exact hLne hLzero

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NP_originalSU2WilsonTemporalPSDCertificate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NP_originalSU2WilsonTemporal_allFiniteGram_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NP_originalSU2RealEightPolynomialAlgebra_dense
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NP_originalSignedDiracDefect_detected_by_realEightPolynomial
