import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeBoundaryDegreeMomentStrictness
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureNonnegSMulMomentStrictness
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonSelectedTaylorPSD
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace Topology

noncomputable section

private theorem cyclicFourEdgeWilsonPSDTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance cyclicFourEdgeWilsonPSDTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFourEdgeWilsonPSDCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFourEdgeWilsonPSDSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFourEdgeWilsonPSDMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFourEdgeWilsonPSDBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFourEdgeWilsonPSDSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The exact four-edge Wilson product kernel in the validated cyclic pair order
`(2,3)|(0,1)`.  The four edge kernels remain independent. -/
def specialUnitaryTwoCyclicFourEdgeWilsonProductKernel
    (beta : ℝ)
    (u v : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  (specialUnitaryWilsonRelativeKernel 2 beta (u 2) (v 2) *
      specialUnitaryWilsonRelativeKernel 2 beta (u 3) (v 3)) *
    (specialUnitaryWilsonRelativeKernel 2 beta (u 0) (v 0) *
      specialUnitaryWilsonRelativeKernel 2 beta (u 1) (v 1))

/-- Scalar coefficient of the common degree-`n` diagonal sector in the product
of four one-edge Wilson Taylor expansions. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient
    (beta : ℝ)
    (n : ℕ) : ℝ :=
  (specialUnitaryWilsonSelectedTaylorCoefficient beta n) ^ 4

/-- The selected common degree-`n` four-edge Hilbert kernel. -/
def specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel
    (beta : ℝ)
    (n : ℕ)
    (u v : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient beta n *
    specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel u v ^ n

/-- The selected common four-edge degree has the genuine four-edge source Fock
feature from #1667, scaled by the fourth power of the exact one-edge Taylor
coefficient (including `exp (-beta)`). -/
noncomputable def specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeFeature
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    RealHilbertKernelFeature
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta n) := by
  have hOne : 0 ≤ specialUnitaryWilsonSelectedTaylorCoefficient beta n := by
    unfold specialUnitaryWilsonSelectedTaylorCoefficient
    exact mul_nonneg (Real.exp_nonneg _)
      (div_nonneg (pow_nonneg hbeta _) (by positivity))
  have hFour :
      0 ≤ specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient beta n := by
    unfold specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient
    exact pow_nonneg hOne _
  simpa [specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel] using
    RealHilbertKernelFeature.nonnegSMul
      (specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient beta n)
      hFour
      (specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n)

/-- Coordinate product of the four independently selected one-edge Taylor
terms. -/
def specialUnitaryTwoCyclicFourEdgeWilsonSelectedCoordinateProductKernel
    (beta : ℝ)
    (n : ℕ)
    (u v : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  (specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta n (u 2) (v 2) *
      specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta n (u 3) (v 3)) *
    (specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta n (u 0) (v 0) *
      specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta n (u 1) (v 1))

/-- The product of the four selected coordinate terms is exactly the genuine
four-edge diagonal Fock kernel. -/
theorem specialUnitaryTwoCyclicFourEdgeWilsonSelectedCoordinateProductKernel_eq_selectedDegree
    (beta : ℝ)
    (n : ℕ)
    (u v : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryTwoCyclicFourEdgeWilsonSelectedCoordinateProductKernel beta n u v =
      specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta n u v := by
  simp only [specialUnitaryTwoCyclicFourEdgeWilsonSelectedCoordinateProductKernel,
    specialUnitaryWilsonRelativeSelectedDegreeKernel,
    specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel,
    specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient,
    specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel, mul_pow]
  ring

/-- Four-term telescoping remainder of the full rectangular finite Taylor
product after the common selected degree has been split from every coordinate.
Each term contains one PSD one-edge remainder and otherwise PSD full/selected
coordinate kernels. -/
def specialUnitaryTwoCyclicFourEdgeWilsonPartialSelectedRemainderKernel
    (beta : ℝ)
    (degree selected : ℕ)
    (u v : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  ((specialUnitaryWilsonRelativeKernelPartialSelectedRemainder
        2 beta degree selected (u 2) (v 2) *
      specialUnitaryWilsonRelativeKernelPartial 2 beta degree (u 3) (v 3)) *
    (specialUnitaryWilsonRelativeKernelPartial 2 beta degree (u 0) (v 0) *
      specialUnitaryWilsonRelativeKernelPartial 2 beta degree (u 1) (v 1)) +
   (specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta selected (u 2) (v 2) *
      specialUnitaryWilsonRelativeKernelPartialSelectedRemainder
        2 beta degree selected (u 3) (v 3)) *
    (specialUnitaryWilsonRelativeKernelPartial 2 beta degree (u 0) (v 0) *
      specialUnitaryWilsonRelativeKernelPartial 2 beta degree (u 1) (v 1))) +
  ((specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta selected (u 2) (v 2) *
      specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta selected (u 3) (v 3)) *
    (specialUnitaryWilsonRelativeKernelPartialSelectedRemainder
        2 beta degree selected (u 0) (v 0) *
      specialUnitaryWilsonRelativeKernelPartial 2 beta degree (u 1) (v 1)) +
   (specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta selected (u 2) (v 2) *
      specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta selected (u 3) (v 3)) *
    (specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta selected (u 0) (v 0) *
      specialUnitaryWilsonRelativeKernelPartialSelectedRemainder
        2 beta degree selected (u 1) (v 1)))

/-- One coordinate of the full finite Wilson Taylor kernel, as a PSD
certificate on the four-edge tuple. -/
noncomputable def specialUnitaryTwoFourEdgeWilsonPartialCoordinateCertificate
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (j : Fin 4) :
    RealKernelPositiveSemidefiniteCertificate
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (fun u v => specialUnitaryWilsonRelativeKernelPartial 2 beta degree (u j) (v j)) :=
  ((specialUnitaryWilsonRelativeKernelPartialConcreteFeature
      2 cyclicFourEdgeWilsonPSDTwoRankPositive beta hbeta degree).comap
    (fun u : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ => u j)).toPositiveSemidefiniteCertificate

/-- One selected coordinate Taylor degree, pulled to a four-edge tuple. -/
noncomputable def specialUnitaryTwoFourEdgeWilsonSelectedCoordinateCertificate
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (selected : ℕ)
    (j : Fin 4) :
    RealKernelPositiveSemidefiniteCertificate
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (fun u v =>
        specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta selected (u j) (v j)) :=
  ((specialUnitaryWilsonRelativeSelectedDegreeFeature
      2 cyclicFourEdgeWilsonPSDTwoRankPositive beta hbeta selected).comap
    (fun u : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ => u j)).toPositiveSemidefiniteCertificate

/-- One coordinate finite remainder, pulled to a four-edge tuple. -/
noncomputable def specialUnitaryTwoFourEdgeWilsonPartialRemainderCoordinateCertificate
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree selected : ℕ)
    (j : Fin 4) :
    RealKernelPositiveSemidefiniteCertificate
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (fun u v =>
        specialUnitaryWilsonRelativeKernelPartialSelectedRemainder
          2 beta degree selected (u j) (v j)) :=
  (specialUnitaryWilsonRelativeKernelPartialSelectedRemainder_positiveSemidefiniteCertificate
    2 cyclicFourEdgeWilsonPSDTwoRankPositive beta hbeta degree selected).comap
      (fun u : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ => u j)

/-- The four-term finite rectangular remainder is symmetric positive
semidefinite.  This is the precise PSD-domination statement: the full
rectangular truncation contains the selected common degree as a Hilbert direct
sector, while every remaining multi-degree contribution stays in the PSD cone. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeWilsonPartialSelectedRemainderCertificate
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree selected : ℕ) :
    RealKernelPositiveSemidefiniteCertificate
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (specialUnitaryTwoCyclicFourEdgeWilsonPartialSelectedRemainderKernel
        beta degree selected) := by
  let A₂ := specialUnitaryTwoFourEdgeWilsonPartialCoordinateCertificate
    beta hbeta degree 2
  let A₃ := specialUnitaryTwoFourEdgeWilsonPartialCoordinateCertificate
    beta hbeta degree 3
  let A₀ := specialUnitaryTwoFourEdgeWilsonPartialCoordinateCertificate
    beta hbeta degree 0
  let A₁ := specialUnitaryTwoFourEdgeWilsonPartialCoordinateCertificate
    beta hbeta degree 1
  let S₂ := specialUnitaryTwoFourEdgeWilsonSelectedCoordinateCertificate
    beta hbeta selected 2
  let S₃ := specialUnitaryTwoFourEdgeWilsonSelectedCoordinateCertificate
    beta hbeta selected 3
  let S₀ := specialUnitaryTwoFourEdgeWilsonSelectedCoordinateCertificate
    beta hbeta selected 0
  let R₂ := specialUnitaryTwoFourEdgeWilsonPartialRemainderCoordinateCertificate
    beta hbeta degree selected 2
  let R₃ := specialUnitaryTwoFourEdgeWilsonPartialRemainderCoordinateCertificate
    beta hbeta degree selected 3
  let R₀ := specialUnitaryTwoFourEdgeWilsonPartialRemainderCoordinateCertificate
    beta hbeta degree selected 0
  let R₁ := specialUnitaryTwoFourEdgeWilsonPartialRemainderCoordinateCertificate
    beta hbeta degree selected 1
  simpa [specialUnitaryTwoCyclicFourEdgeWilsonPartialSelectedRemainderKernel,
    A₂, A₃, A₀, A₁, S₂, S₃, S₀, R₂, R₃, R₀, R₁] using
    (((R₂.mul A₃).mul (A₀.mul A₁)).add
      ((S₂.mul R₃).mul (A₀.mul A₁))).add
    (((S₂.mul S₃).mul (R₀.mul A₁)).add
      ((S₂.mul S₃).mul (S₀.mul R₁)))

/-- Exact finite rectangular decomposition into the selected diagonal Fock
sector plus a PSD remainder. -/
theorem specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel_eq_remainder_add_selectedDegree
    (beta : ℝ)
    (degree selected : ℕ)
    (hselected : selected ≤ degree)
    (u v : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree u v =
      specialUnitaryTwoCyclicFourEdgeWilsonPartialSelectedRemainderKernel
          beta degree selected u v +
        specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected u v := by
  have h₂ := specialUnitaryWilsonRelativeKernelPartial_eq_selected_add_remainder
    2 beta degree selected hselected (u 2) (v 2)
  have h₃ := specialUnitaryWilsonRelativeKernelPartial_eq_selected_add_remainder
    2 beta degree selected hselected (u 3) (v 3)
  have h₀ := specialUnitaryWilsonRelativeKernelPartial_eq_selected_add_remainder
    2 beta degree selected hselected (u 0) (v 0)
  have h₁ := specialUnitaryWilsonRelativeKernelPartial_eq_selected_add_remainder
    2 beta degree selected hselected (u 1) (v 1)
  rw [← specialUnitaryTwoCyclicFourEdgeWilsonSelectedCoordinateProductKernel_eq_selectedDegree
    beta selected u v]
  unfold specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel
  unfold specialUnitaryTwoCyclicFourEdgeWilsonPartialSelectedRemainderKernel
  unfold specialUnitaryTwoCyclicFourEdgeWilsonSelectedCoordinateProductKernel
  rw [h₂, h₃, h₀, h₁]
  ring

/-- Subtraction form of the finite rectangular PSD remainder, used only to
identify its pointwise limit. -/
theorem specialUnitaryTwoCyclicFourEdgeWilsonPartialSelectedRemainderKernel_eq_sub
    (beta : ℝ)
    (degree selected : ℕ)
    (hselected : selected ≤ degree)
    (u v : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryTwoCyclicFourEdgeWilsonPartialSelectedRemainderKernel
        beta degree selected u v =
      specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree u v -
        specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected u v := by
  have hdecomp :=
    specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel_eq_remainder_add_selectedDegree
      beta degree selected hselected u v
  rw [hdecomp]
  ring

/-- Exact Wilson remainder after removing one common diagonal four-edge degree. -/
def specialUnitaryTwoCyclicFourEdgeWilsonSelectedRemainderKernel
    (beta : ℝ)
    (selected : ℕ)
    (u v : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta u v -
    specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected u v

/-- The finite PSD rectangular remainders converge pointwise to the exact
Wilson remainder after the same common degree is removed. -/
theorem specialUnitaryTwoCyclicFourEdgeWilsonPartialSelectedRemainderKernel_tendsto_exact
    (beta : ℝ)
    (selected : ℕ)
    (u v : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Tendsto
      (fun tail =>
        specialUnitaryTwoCyclicFourEdgeWilsonPartialSelectedRemainderKernel
          beta (tail + selected) selected u v)
      atTop
      (𝓝
        (specialUnitaryTwoCyclicFourEdgeWilsonSelectedRemainderKernel
          beta selected u v)) := by
  have hProduct :
      Tendsto
        (fun degree =>
          specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree u v)
        atTop
        (𝓝 (specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta u v)) := by
    simpa [specialUnitaryTwoCyclicFourEdgeWilsonProductKernel] using
      specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel_tendsto beta u v
  have hBase :
      Tendsto
        (fun degree =>
          specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree u v -
            specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected u v)
        atTop
        (𝓝
          (specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta u v -
            specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected u v)) :=
    hProduct.sub tendsto_const_nhds
  have hShift :
      Tendsto
        (fun tail =>
          specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel
              beta (tail + selected) u v -
            specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected u v)
        atTop
        (𝓝
          (specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta u v -
            specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected u v)) := by
    rw [tendsto_add_atTop_iff_nat
      (f := fun degree =>
        specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree u v -
          specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected u v)
      selected]
    exact hBase
  have hfun :
      (fun tail =>
        specialUnitaryTwoCyclicFourEdgeWilsonPartialSelectedRemainderKernel
          beta (tail + selected) selected u v) =
      (fun tail =>
        specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel
            beta (tail + selected) u v -
          specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected u v) := by
    funext tail
    exact
      specialUnitaryTwoCyclicFourEdgeWilsonPartialSelectedRemainderKernel_eq_sub
        beta (tail + selected) selected (by omega) u v
  rw [hfun]
  simpa [specialUnitaryTwoCyclicFourEdgeWilsonSelectedRemainderKernel] using hShift

/-- The exact four-edge Wilson remainder is symmetric positive semidefinite.
No scalar-sign argument is used: it is the pointwise closed limit of the finite
rectangular PSD remainders. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeWilsonSelectedRemainderCertificate
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (selected : ℕ) :
    RealKernelPositiveSemidefiniteCertificate
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (specialUnitaryTwoCyclicFourEdgeWilsonSelectedRemainderKernel beta selected) :=
  RealKernelPositiveSemidefiniteCertificate.pointwiseLimit
    (fun tail =>
      specialUnitaryTwoCyclicFourEdgeWilsonPartialSelectedRemainderCertificate
        beta hbeta (tail + selected) selected)
    (specialUnitaryTwoCyclicFourEdgeWilsonPartialSelectedRemainderKernel_tendsto_exact
      beta selected)

/-- Exact decomposition of the four-edge Wilson product into the selected
common Taylor degree plus a symmetric PSD remainder. -/
theorem specialUnitaryTwoCyclicFourEdgeWilsonProductKernel_eq_remainder_add_selectedDegree
    (beta : ℝ)
    (selected : ℕ)
    (u v : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta u v =
      specialUnitaryTwoCyclicFourEdgeWilsonSelectedRemainderKernel beta selected u v +
        specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected u v := by
  unfold specialUnitaryTwoCyclicFourEdgeWilsonSelectedRemainderKernel
  ring

/-- The selected degree pulled to the four actual fixed boundary edges.  It is
defined as a nonnegative scaling after the pullback so its right-coordinate
moment is exposed definitionally to the generic direct-sum projection theorem. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedDegreeFeature
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    RealHilbertKernelFeature
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2)
      (fun b c =>
        specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient beta n *
          specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H c) ^ n) := by
  have hOne : 0 ≤ specialUnitaryWilsonSelectedTaylorCoefficient beta n := by
    unfold specialUnitaryWilsonSelectedTaylorCoefficient
    exact mul_nonneg (Real.exp_nonneg _)
      (div_nonneg (pow_nonneg hbeta _) (by positivity))
  have hFour :
      0 ≤ specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient beta n := by
    unfold specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient
    exact pow_nonneg hOne _
  exact
    RealHilbertKernelFeature.nonnegSMul
      (specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient beta n)
      hFour
      ((specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n).comap
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H))

/-- The exact PSD remainder pulled to the actual four fixed boundary edges. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedRemainderFeature
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    RealHilbertKernelFeature
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2)
      (fun b c =>
        specialUnitaryTwoCyclicFourEdgeWilsonSelectedRemainderKernel beta n
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H c)) :=
  (specialUnitaryTwoCyclicFourEdgeWilsonSelectedRemainderCertificate beta hbeta n).toHilbertFeature.comap
    (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H)

/-- Boundary Hilbert feature of the exact four-edge Wilson product, explicitly
realized as `PSD remainder ⊕ selected strict degree`. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :=
  RealHilbertKernelFeature.add
    (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedRemainderFeature
      H beta hbeta n)
    (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedDegreeFeature
      H beta hbeta n)

private theorem continuous_cyclicFourEdgeWilsonPSDBoundaryWord
    (H : ℕ) :
    Continuous (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H) := by
  apply continuous_pi
  intro j
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord] using
    (continuous_apply
      (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H j))

private theorem continuous_cyclicFourEdgeWilsonPSDCoordinateKernel
    (beta : ℝ)
    (j : Fin 4) :
    Continuous fun q :
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) ×
        (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
      specialUnitaryWilsonRelativeKernel 2 beta (q.1 j) (q.2 j) := by
  exact (continuous_specialUnitaryWilsonRelativeKernel 2 beta).comp₂
    ((continuous_apply j).comp continuous_fst)
    ((continuous_apply j).comp continuous_snd)

private theorem continuous_cyclicFourEdgeWilsonProductKernel
    (beta : ℝ) :
    Continuous fun q :
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) ×
        (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
      specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta q.1 q.2 := by
  unfold specialUnitaryTwoCyclicFourEdgeWilsonProductKernel
  exact
    ((continuous_cyclicFourEdgeWilsonPSDCoordinateKernel beta 2).mul
      (continuous_cyclicFourEdgeWilsonPSDCoordinateKernel beta 3)).mul
      ((continuous_cyclicFourEdgeWilsonPSDCoordinateKernel beta 0).mul
        (continuous_cyclicFourEdgeWilsonPSDCoordinateKernel beta 1))

/-- The exact boundary decomposition feature is continuous. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature_continuous
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    Continuous
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature
        H beta hbeta n).feature := by
  let C := periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature
    H beta hbeta n
  have hExact : Continuous fun q :
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) ×
        (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) =>
      specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H q.1)
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H q.2) :=
    (continuous_cyclicFourEdgeWilsonProductKernel beta).comp₂
      ((continuous_cyclicFourEdgeWilsonPSDBoundaryWord H).comp continuous_fst)
      ((continuous_cyclicFourEdgeWilsonPSDBoundaryWord H).comp continuous_snd)
  have hKernel : Continuous fun q :
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) ×
        (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) =>
      specialUnitaryTwoCyclicFourEdgeWilsonSelectedRemainderKernel beta n
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H q.1)
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H q.2) +
        specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta n
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H q.1)
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H q.2) := by
    rw [show
      (fun q :
        (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) ×
          (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) =>
        specialUnitaryTwoCyclicFourEdgeWilsonSelectedRemainderKernel beta n
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H q.1)
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H q.2) +
          specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta n
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H q.1)
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H q.2)) =
      (fun q =>
        specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H q.1)
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H q.2)) by
        funext q
        exact
          (specialUnitaryTwoCyclicFourEdgeWilsonProductKernel_eq_remainder_add_selectedDegree
            beta n _ _).symm]
    exact hExact
  simpa [C,
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature,
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedRemainderFeature,
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedDegreeFeature,
    specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel] using
    RealHilbertKernelFeature.continuous_feature_of_continuous_kernel C hKernel

/-- The exact four-edge Wilson decomposition feature has unit norm on every
actual boundary configuration. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature_norm
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    ‖(periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature
        H beta hbeta n).feature b‖ = 1 := by
  let C := periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature
    H beta hbeta n
  apply RealHilbertKernelFeature.feature_norm_eq_one C
  intro d
  change
    specialUnitaryTwoCyclicFourEdgeWilsonSelectedRemainderKernel beta n
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d)
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d) +
      specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta n
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d)
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d) = 1
  rw [← specialUnitaryTwoCyclicFourEdgeWilsonProductKernel_eq_remainder_add_selectedDegree]
  unfold specialUnitaryTwoCyclicFourEdgeWilsonProductKernel
  rw [specialUnitaryWilsonRelativeKernel_self
      2 cyclicFourEdgeWilsonPSDTwoRankPositive beta
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d 2),
    specialUnitaryWilsonRelativeKernel_self
      2 cyclicFourEdgeWilsonPSDTwoRankPositive beta
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d 3),
    specialUnitaryWilsonRelativeKernel_self
      2 cyclicFourEdgeWilsonPSDTwoRankPositive beta
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d 0),
    specialUnitaryWilsonRelativeKernel_self
      2 cyclicFourEdgeWilsonPSDTwoRankPositive beta
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d 1)]
  norm_num

/-- Polynomial-weighted exact four-edge Wilson decomposition features are
Bochner integrable in the interacting boundary marginal. -/
theorem periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeWilsonDecompositionFeature_integrable
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (n : ℕ) :
    Integrable
      (fun b =>
        periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature
            H beta hbeta n).feature b)
      (periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 cyclicFourEdgeWilsonPSDTwoRankPositive beta hbeta) := by
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  let C := periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature
    H beta hbeta n
  have hContinuous : Continuous (fun b => p b • C.feature b) := by
    exact p.continuous.smul
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature_continuous
        H beta hbeta n)
  refine Integrable.of_bound hContinuous.aestronglyMeasurable ‖p‖ ?_
  filter_upwards [] with b
  rw [norm_smul,
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature_norm]
  simpa [p] using p.norm_coe_le_norm b

/-- A cyclic dual probe detecting the genuine degree-`n` source moment also
detects the exactly scaled selected four-edge Wilson sector. -/
theorem periodicHypercubicEvenBoundaryMarginal_selectedFourEdgeWilsonDegreeFeature_integral_ne_zero_of_cyclicDualProbe
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (k n : ℕ)
    (c : Fin (k + 1) → ℝ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (hq :
      (∫ b,
        inner ℝ q
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
              H n).feature b)
        ∂(periodicHypercubicEvenBoundaryMarginalMeasure
          H 2 cyclicFourEdgeWilsonPSDTwoRankPositive beta hbeta.le)) ≠ 0) :
    (∫ b,
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedDegreeFeature
          H beta hbeta.le n).feature b
      ∂(periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 cyclicFourEdgeWilsonPSDTwoRankPositive beta hbeta.le)) ≠ 0 := by
  let μ := periodicHypercubicEvenBoundaryMarginalMeasure
    H 2 cyclicFourEdgeWilsonPSDTwoRankPositive beta hbeta.le
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  let C₀ :=
    (specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n).comap
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H)
  let s := specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient beta n
  have hTaylor : 0 < specialUnitaryWilsonSelectedTaylorCoefficient beta n := by
    unfold specialUnitaryWilsonSelectedTaylorCoefficient
    exact mul_pos (Real.exp_pos _)
      (div_pos (pow_pos hbeta _) (by positivity))
  have hs : 0 < s := by
    dsimp [s, specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient]
    exact pow_pos hTaylor _
  have hBase : (∫ b, p b • C₀.feature b ∂μ) ≠ 0 := by
    simpa [μ, p, C₀,
      periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature,
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue] using
      periodicHypercubicEvenBoundaryMarginal_weightedFourEdgeDegreeFeature_integral_ne_zero_of_cyclicDualProbe
        H beta hbeta.le k n c q hq
  have hScaled : Real.sqrt s • (∫ b, p b • C₀.feature b ∂μ) ≠ 0 := by
    exact smul_ne_zero (ne_of_gt (Real.sqrt_pos.2 hs)) hBase
  have hEq :=
    RealHilbertKernelFeature.nonnegSMul_weighted_integral_eq_sqrt_smul
      C₀ μ p s hs.le
  simpa [μ, p, C₀, s,
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedDegreeFeature] using
    hEq.trans_ne hScaled

/-- Weighted inner products of the exact decomposition feature are literally
the scalar exact four-edge Wilson product kernel. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature_weighted_inner_eq_exactKernel
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 → ℝ)
    (b c : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    inner ℝ
        (a b •
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature
            H beta hbeta n).feature b)
        (a c •
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature
            H beta hbeta n).feature c) =
      a b * a c *
        specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H c) := by
  let C := periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature
    H beta hbeta n
  rw [real_inner_smul_left, real_inner_smul_right]
  rw [← C.kernel_eq_inner]
  change
    a b *
        (a c *
          (specialUnitaryTwoCyclicFourEdgeWilsonSelectedRemainderKernel beta n
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H c) +
            specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta n
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H c))) = _
  rw [← specialUnitaryTwoCyclicFourEdgeWilsonProductKernel_eq_remainder_add_selectedDegree]
  ring

/-- Main strictness package: every centered nonzero normalized-trace boundary
polynomial at positive coupling has a positive Taylor degree whose genuine
four-edge source moment forces strict positivity of the **exact** four-edge
Wilson product Gram form.

The proof is cancellation-free.  The finite rectangular Taylor kernel is split
into the selected common degree plus a PSD remainder, the remainder stays PSD
in the exact pointwise limit, Moore--Aronszajn realizes that limit as a Hilbert
feature, and the direct-sum right projection transports the #1667 nonzero
moment into the exact Wilson feature. -/
theorem periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomial_exists_positiveDegree_exactFourEdgeWilsonGram_strict
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hc : c ≠ 0)
    (hzero :
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 cyclicFourEdgeWilsonPSDTwoRankPositive beta hbeta.le) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
            (0 : ℕ)))
        (∑ j : Fin (k + 1), c j •
          ContinuousMap.toLp
            (E := ℝ) 2
            (periodicHypercubicEvenBoundaryMarginalMeasure
              H 2 cyclicFourEdgeWilsonPSDTwoRankPositive beta hbeta.le) ℝ
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
              (j : ℕ))) = 0) :
    ∃ i : Fin (k + 1),
      0 < (i : ℕ) ∧
      ∃ q :
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
          H (i : ℕ)).FeatureHilbert,
        (∫ b,
          inner ℝ q
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
              (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
                H (i : ℕ)).feature b)
          ∂(periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 cyclicFourEdgeWilsonPSDTwoRankPositive beta hbeta.le)) ≠ 0 ∧
        0 < ∫ b₁, ∫ b₂,
          periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b₁ *
            periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b₂ *
            specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b₁)
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b₂)
          ∂(periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 cyclicFourEdgeWilsonPSDTwoRankPositive beta hbeta.le)
          ∂(periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 cyclicFourEdgeWilsonPSDTwoRankPositive beta hbeta.le) := by
  rcases
    periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomial_exists_positiveDegree_fourEdgeDiagonalGram_strict
      H beta hbeta k c hc hzero with
    ⟨i, hi, hCoefficient, q, hq, hDiagonalStrict⟩
  let n := (i : ℕ)
  let μ := periodicHypercubicEvenBoundaryMarginalMeasure
    H 2 cyclicFourEdgeWilsonPSDTwoRankPositive beta hbeta.le
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  let R := periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedRemainderFeature
    H beta hbeta.le n
  let S := periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedDegreeFeature
    H beta hbeta.le n
  let C := RealHilbertKernelFeature.add R S
  have hIntegrable : Integrable (fun b => p b • C.feature b) μ := by
    simpa [C, R, S, p, μ,
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature] using
      periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeWilsonDecompositionFeature_integrable
        H beta hbeta.le k c n
  have hSelectedMoment : (∫ b, p b • S.feature b ∂μ) ≠ 0 := by
    simpa [S, p, μ, n] using
      periodicHypercubicEvenBoundaryMarginal_selectedFourEdgeWilsonDegreeFeature_integral_ne_zero_of_cyclicDualProbe
        H beta hbeta k n c q hq
  have hFullMoment : (∫ b, p b • C.feature b ∂μ) ≠ 0 :=
    RealHilbertKernelFeature.add_weighted_integral_ne_zero_of_right
      R S μ p hIntegrable hSelectedMoment
  have hGram :
      0 < ∫ b₁, ∫ b₂,
        inner ℝ (p b₁ • C.feature b₁) (p b₂ • C.feature b₂) ∂μ ∂μ :=
    C.weighted_inner_doubleIntegral_pos_of_integral_ne_zero
      μ p hIntegrable hFullMoment
  refine ⟨i, hi, q, hq, ?_⟩
  have hC :
      C = periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature
        H beta hbeta.le n := by
    rfl
  rw [hC] at hGram
  simp only [
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonDecompositionFeature_weighted_inner_eq_exactKernel] at hGram
  simpa [p, μ, n] using hGram

end

end MathlibAnalytic
end MGAP4D