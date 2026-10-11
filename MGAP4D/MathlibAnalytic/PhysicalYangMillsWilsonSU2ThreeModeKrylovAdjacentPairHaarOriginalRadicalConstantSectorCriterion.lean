import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalDirichletKernelOrderUnit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGroundStateTwelveColorCenteredVarianceBound
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

/-!
# P4-Q2-CC: original Wilson Haar reference radical, constant-sector reduction,
  and the EXACT missing reverse-kernel obligation

At BZ--CB the ORIGINAL physical mass-weighted Wilson Haar reference has its
ACTUAL bounded positive self-adjoint Riesz operator `A_original`, and the
independently constructed physical 12-color conditional-projection Dirichlet
operator `D12` has exact kernel equal to the intrinsic constant line V.
The proven order is ONLY
  0 ≤ A_original ≤ 12 • D12,  0 ≤ D12 ≤ id,
hence V = ker D12 ≤ ker A_original.

We prove without any further physical assumption:
* original Wilson Haar Riesz operator kills every constant-sector vector;
* its Hilbert matrix elements are orthogonal to those constants;
* the original operator and quadratic energy depend ONLY on the
  genuine physical joint-L² constant-centered vector;
* equality of its kernel with V is EQUIVALENT to STRICT positivity of the
  literal original Wilson reference on every nonconstant physical class;
* any failure of kernel equality produces a nonconstant EXACT zero-reference
  energy witness, not just a small-energy sequence;
* a genuine reverse quadratic comparison c E12 ≤ Q_original with c>0 WOULD
  imply kernel equality, but is taken as an EXPLICIT premise, not a theorem.

The existing AW--BB single-link Haar posterior comparison provides only the
OPPOSITE full-space inequality. Local positivity alone is not substituted
for the missing full-space reverse inequality. No numerical gap, continuum
mass gap, kernel equality or extra physical measure is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "V" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
    H N hN beta hbeta
local notation "Q" =>
  p4Q2BX_originalFullJointQuadratic H N hN beta hbeta
local notation "W" =>
  p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta
local notation "E12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    H N hN beta hbeta

/-- The literal original Wilson Haar-reference Riesz endomorphism annihilates
every genuine physical constant-sector vector, with no beta cutoff. -/
theorem p4Q2CC_originalWilsonRiesz_zero_of_mem_constantLine
    (c : J) (hc : c ∈ V) : W c = 0 :=
  LinearMap.mem_ker.mp
    (p4Q2BZ_jointConstantLine_le_originalRiesz_ker H N hN beta hbeta hc)

/-- Every matrix element of the genuine Wilson reference Riesz image against
an intrinsic physical constant vanishes, because W is self-adjoint. -/
theorem p4Q2CC_originalWilsonRiesz_inner_constant_eq_zero
    (f c : J) (hc : c ∈ V) :
    inner ℝ (W f) c = 0 := by
  have hs :
      inner ℝ (W f) c = inner ℝ f (W c) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (p4Q2BY_originalFullJointRieszOperator_isSelfAdjoint
        H N hN beta hbeta) f c
  rw [hs, p4Q2CC_originalWilsonRiesz_zero_of_mem_constantLine
    H N hN beta hbeta c hc, inner_zero_right]

/-- This is a statement about the LITERAL original Wilson reference
bilinear extension, not the distinct physical D12 Gram pairing. -/
theorem p4Q2CC_originalWilsonBilinear_constant_right_eq_zero
    (f c : J) (hc : c ∈ V) :
    p4Q2BW_originalFullJointContinuousBilin H N hN beta hbeta f c = 0 := by
  rw [← p4Q2BY_originalFullJointRieszOperator_inner]
  exact p4Q2CC_originalWilsonRiesz_inner_constant_eq_zero
    H N hN beta hbeta f c hc

/-- Adding any intrinsic physical constant leaves the literal original Wilson
Riesz image completely unchanged. -/
theorem p4Q2CC_originalWilsonRiesz_add_constant
    (f c : J) (hc : c ∈ V) :
    W (f + c) = W f := by
  rw [map_add,
    p4Q2CC_originalWilsonRiesz_zero_of_mem_constantLine
      H N hN beta hbeta c hc, add_zero]

/-- The literal original Wilson Haar-reference quadratic energy is invariant
under ALL constant shifts in the original physical joint Hilbert space. -/
theorem p4Q2CC_originalWilsonQuadratic_add_constant
    (f c : J) (hc : c ∈ V) :
    Q (f + c) = Q f := by
  calc
    Q (f + c) = inner ℝ (W (f + c)) (f + c) :=
      (p4Q2BY_originalFullJointRieszOperator_quadratic
        H N hN beta hbeta (f + c)).symm
    _ = inner ℝ (W f) (f + c) := by
      rw [p4Q2CC_originalWilsonRiesz_add_constant H N hN beta hbeta f c hc]
    _ = inner ℝ (W f) f := by
      rw [inner_add_right,
        p4Q2CC_originalWilsonRiesz_inner_constant_eq_zero
          H N hN beta hbeta f c hc, add_zero]
    _ = Q f :=
      p4Q2BY_originalFullJointRieszOperator_quadratic H N hN beta hbeta f

/-- The EXACT qualitative missing obligation: kernel equality holds if and
only if the ORIGINAL Haar reference is strictly positive on every
nonconstant physical joint-L² equivalence class. Strict positive does not
imply a uniform lower spectral gap in an infinite-dimensional Hilbert space. -/
theorem p4Q2CC_originalWilsonKernel_eq_constantLine_iff_strict_energy :
    (W : J →ₗ[ℝ] J).ker = V ↔
      ∀ f : J, f ∉ V → 0 < Q f := by
  constructor
  · intro hker f hf
    have hnonneg : 0 ≤ Q f :=
      p4Q2BX_originalFullJointQuadratic_nonneg H N hN beta hbeta f
    by_contra hnpos
    have hzero : Q f = 0 :=
      le_antisymm (not_lt.mp hnpos) hnonneg
    have hWzero : W f = 0 :=
      (p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero
        H N hN beta hbeta f).mp hzero
    have hfV : f ∈ V := by
      rw [← hker]
      exact LinearMap.mem_ker.mpr hWzero
    exact hf hfV
  · intro hstrict
    apply le_antisymm ?_
      (p4Q2BZ_jointConstantLine_le_originalRiesz_ker H N hN beta hbeta)
    intro f hfker
    have hWzero : W f = 0 := LinearMap.mem_ker.mp hfker
    have hQzero : Q f = 0 :=
      (p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero
        H N hN beta hbeta f).mpr hWzero
    by_contra hfnot
    exact (ne_of_gt (hstrict f hfnot)) hQzero

/-- If equality of the two genuine physical kernels fails, there MUST be
a nonconstant physical L² class with EXACTLY ZERO original Wilson Haar
reference energy. It is not enough to exhibit energy merely approaching 0. -/
theorem p4Q2CC_originalWilsonKernel_ne_constantLine_has_zero_witness
    (hneq : (W : J →ₗ[ℝ] J).ker ≠ V) :
    ∃ f : J, f ∉ V ∧ Q f = 0 := by
  have hV : V ≤ (W : J →ₗ[ℝ] J).ker :=
    p4Q2BZ_jointConstantLine_le_originalRiesz_ker H N hN beta hbeta
  have hnot : ¬ ((W : J →ₗ[ℝ] J).ker ≤ V) := by
    intro h
    exact hneq (le_antisymm h hV)
  have hwit : ∃ f : J, f ∈ (W : J →ₗ[ℝ] J).ker ∧ f ∉ V := by
    by_contra h
    apply hnot
    intro f hf
    by_contra hfnot
    exact h ⟨f, hf, hfnot⟩
  rcases hwit with ⟨f, hf, hfnot⟩
  exact ⟨f, hfnot,
    (p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero
      H N hN beta hbeta f).mpr (LinearMap.mem_ker.mp hf)⟩

/-- This IS the missing reverse comparison, explicitly parameterized as a
future-proof OBLIGATION. If a positive constant c controls physical E12
from below by the LITERAL original Wilson Haar reference Q on the SAME
physical joint L², the physical constant-line kernel equality follows.
Nothing preceding CC supplies this hypothesis. -/
theorem p4Q2CC_originalWilsonKernel_eq_constantLine_of_reverse_energy
    (c : ℝ) (hc : 0 < c)
    (hreverse : ∀ f : J, c * E12 f ≤ Q f) :
    (W : J →ₗ[ℝ] J).ker = V := by
  apply le_antisymm ?_
    (p4Q2BZ_jointConstantLine_le_originalRiesz_ker H N hN beta hbeta)
  intro f hf
  have hWzero : W f = 0 := LinearMap.mem_ker.mp hf
  have hQzero : Q f = 0 :=
    (p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero
      H N hN beta hbeta f).mpr hWzero
  have hbd := hreverse f
  rw [hQzero] at hbd
  have hE0 : 0 ≤ E12 f := by
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    exact groundStateJointColorNormalizedResidualEnergy_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
        H N hN beta hbeta) f
  have hEeq : E12 f = 0 := by nlinarith
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_zero_iff_mem_constantLine
      H N hN beta hbeta f).mp hEeq

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
