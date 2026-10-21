import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRealEightGaussianKernelV5_NM
import Mathlib.Tactic

/-!
# P4-Q2-NN — genuine SU(2) Gaussian real-eight embedding and all-pair Gram

NM established the actual original SU(2) Wilson temporal kernel is
EXACTLY the Gaussian of the EXISTING real-eight Hilbert matrix feature
J, and proved J injective, norm² J=2, strictly positive squared
chord between distinct real SU2 group elements.

NN proves continuity of this exact J as a map from the ACTUAL compact
SU(2) into its previous finite-dimensional Euclidean matrix feature.
Continuity is proved coefficientwise from the original matrix subtype topology,
Complex.continuous_re/im, and the PiLp real-coordinate homeomorphism.

NN then upgrades NK's one special (1, Rpi) two-point Gram determinant:
for ANY TWO DISTINCT x,g in the true full SU(2) group and any b>0
the exact ORIGINAL temporal Wilson section Gram determinant is >0,
with no Haar law or posterior replaced:
  det [[k_b(x,x), k_b(x,g)], [k_b(g,x), k_b(g,g)]]
     = exp(2b) - k_b(x,g)^2 > 0.

This is genuine universal rank-two strictly PD on all SU2 pairs,
NOT yet strict PD on every finite family, full kernel linear-span
density, nonzero signed receiver variance, GI covariance, H1-C3
or continuum Yang–Mills mass gap.

The two authentic Wilson posteriors, Gauss-law physical source,
spatial touching plaquettes and Perron half-density remain unchanged.
No new axioms, Gaussian surrogate model, Dobrushin, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NN_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NN_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NN_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NN_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NN_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "J" => specialUnitaryMatrixRealFeature 2
local notation "k" => p4Q2NJ_originalSU2WilsonTemporalSection

/-- The ORIGINAL real-eight fundamental SU2 matrix feature is
continuous, not merely injective.  This uses the actual preexisting
matrix-subtype coefficient topology and continuous complex real/imaginary
projections, with the PiLp transport of the actual eight coordinates. -/
theorem p4Q2NN_originalSU2RealEightFeature_continuous :
    Continuous (specialUnitaryMatrixRealFeature 2 :
      Gauge → SpecialUnitaryMatrixRealFeatureSpace 2) := by
  change Continuous (fun g : Gauge =>
    WithLp.toLp 2 (fun q : (Fin 2 × Fin 2) × Bool =>
      if q.2 then ((g : Matrix (Fin 2) (Fin 2) ℂ) q.1.2 q.1.1).re
      else ((g : Matrix (Fin 2) (Fin 2) ℂ) q.1.2 q.1.1).im))
  have hEntry (i j : Fin 2) :
      Continuous (fun g : Gauge =>
        ((g : Matrix (Fin 2) (Fin 2) ℂ) i j)) :=
    (continuous_subtype_val : Continuous
      (fun g : Gauge => (g : Matrix (Fin 2) (Fin 2) ℂ))).matrix_elem i j
  have hCoordinates : Continuous (fun g : Gauge =>
      (fun q : (Fin 2 × Fin 2) × Bool =>
        if q.2 then ((g : Matrix (Fin 2) (Fin 2) ℂ) q.1.2 q.1.1).re
        else ((g : Matrix (Fin 2) (Fin 2) ℂ) q.1.2 q.1.1).im)) := by
    rw [continuous_pi_iff]
    intro q
    by_cases h : q.2
    · simpa [h] using
        Complex.continuous_re.comp (hEntry q.1.2 q.1.1)
    · simpa [h] using
        Complex.continuous_im.comp (hEntry q.1.2 q.1.1)
  exact (PiLp.continuous_toLp 2
    (fun _ : (Fin 2 × Fin 2) × Bool => ℝ)).comp hCoordinates

/-- Every actual temporal Wilson kernel section has the exact
diagonal exp(b), independent of the SU2 boundary configuration. -/
theorem p4Q2NN_originalSU2TemporalWilsonSection_self
    (b : ℝ) (x : Gauge) :
    k b x x = Real.exp b := by
  rw [p4Q2NM_originalSU2TemporalWilsonSection_eq_realEightGaussian]
  simp

/-- Symmetry of the ORIGINAL SU2 temporal exponential kernel,
now derived from the actual real-eight Gaussian chord formula. -/
theorem p4Q2NN_originalSU2TemporalWilsonSection_symmetric
    (b : ℝ) (x g : Gauge) :
    k b x g = k b g x := by
  rw [p4Q2NM_originalSU2TemporalWilsonSection_eq_realEightGaussian,
    p4Q2NM_originalSU2TemporalWilsonSection_eq_realEightGaussian]
  rw [norm_sub_rev (J x) (J g)]

/-- Original SU2 Gaussian temporal Wilson kernel evaluated on two
ARBITRARY true group elements, not on a replacement finite model. -/
noncomputable def p4Q2NN_originalTemporalArbitraryPairMatrix
    (b : ℝ) (x g : Gauge) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    k b (if i = 0 then x else g)
      (if j = 0 then x else g)

/-- Exact all-pairs 2x2 temporal Wilson Gram determinant on the
entire true SU2 group. -/
theorem p4Q2NN_originalTemporalArbitraryPairMatrix_det
    (b : ℝ) (x g : Gauge) :
    (p4Q2NN_originalTemporalArbitraryPairMatrix b x g).det =
      Real.exp b ^ 2 - (k b x g) ^ 2 := by
  rw [Matrix.det_fin_two]
  change
    k b x x * k b g g - k b x g * k b g x = _
  rw [p4Q2NN_originalSU2TemporalWilsonSection_self,
    p4Q2NN_originalSU2TemporalWilsonSection_self,
    ← p4Q2NN_originalSU2TemporalWilsonSection_symmetric b x g]
  ring

/-- Any two distinct genuine SU2 holonomies give a strictly positive
2x2 original temporal Wilson Gram determinant, at EVERY b>0. -/
theorem p4Q2NN_originalTemporalArbitraryPairMatrix_det_pos
    (b : ℝ) (hb : 0 < b) (x g : Gauge) (hneq : x ≠ g) :
    0 < (p4Q2NN_originalTemporalArbitraryPairMatrix b x g).det := by
  rw [p4Q2NN_originalTemporalArbitraryPairMatrix_det]
  have hDiag : 0 < Real.exp b := Real.exp_pos _
  have hOff : 0 < k b x g := by
    change 0 < Real.exp (b * p4Q2NG_originalSU2TemporalCharacter x g)
    exact Real.exp_pos _
  have hStrict : k b x g < Real.exp b :=
    p4Q2NM_originalSU2TemporalWilsonSection_strict_off_diagonal
      b hb x g hneq
  have hProd :
      0 < (Real.exp b - k b x g) * (Real.exp b + k b x g) :=
    mul_pos (sub_pos.mpr hStrict) (add_pos hDiag hOff)
  nlinarith [hProd]

/-- The SAME genuine all-pair Wilson Gram determinant is nonzero:
finite two-point separation is unconditional but still cannot be
mistaken for the open ALL-MODE linear-span density condition. -/
theorem p4Q2NN_originalTemporalArbitraryPairMatrix_det_ne_zero
    (b : ℝ) (hb : 0 < b) (x g : Gauge) (hneq : x ≠ g) :
    (p4Q2NN_originalTemporalArbitraryPairMatrix b x g).det ≠ 0 :=
  (p4Q2NN_originalTemporalArbitraryPairMatrix_det_pos b hb x g hneq).ne'

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NN_originalSU2RealEightFeature_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NN_originalSU2TemporalWilsonSection_self
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NN_originalSU2TemporalWilsonSection_symmetric
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NN_originalTemporalArbitraryPairMatrix_det
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NN_originalTemporalArbitraryPairMatrix_det_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NN_originalTemporalArbitraryPairMatrix_det_ne_zero
