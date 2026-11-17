import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PrimarySpatialSliceGaussLawClassModeV5_PZ37AMT
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceSimplicity
import MGAP4D.MathlibAnalytic.InfiniteLinearIndependentCompletionNotFiniteDimensional
import MGAP4D.MathlibAnalytic.InfiniteDimensionalHilbertVacuumOrthogonalSequence
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMU — genuine finite-volume SU(2) physical Gauss-law excitations

The AMT theorem supplies the missing actual native time-zero Gauss-law
membership of the AMS Wilson-energy Haar-Gram–Schmidt family.  We now lift
those same concrete modes into the original physical gauge-fixed Hilbert
carrier, prove its infinite dimensionality without an assumption, and combine
the established simplicity of the genuine normalized Wilson transfer's full
top eigenspace with the library's theorem-generated Hilbert vacuum-orthogonal
sequence to construct a real nonzero physical excitation.
This does not identify the OS and Wilson one-slab dynamics.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37AMU_spatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p4Q2PZ37AMU_physicalComplete (H : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

/-- The actual AMS native spatial-slice Wilson-energy Haar mode, as an element
of the ORIGINAL finite-volume physical Gauss-law Hilbert carrier.  The property
proof is precisely the new AMT native closed fixed-sector theorem. -/
noncomputable def p4Q2PZ37AMU_actualPhysicalGaussMode
    (H k : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
  ⟨p4Q2PZ37AMS_primarySpatialSliceHolonomyL2Pullback H 2
      (specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode k), by
    rw [← periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule_toSubmodule_eq
      H 2]
    exact p4Q2PZ37AMT_spatialMode_mem_closedGaussLaw H k⟩

/-- The actual physical Gauss-law Hilbert carrier contains the exact countably
infinite orthonormal family of native Wilson-energy modes, not merely ambient
spatial Haar functions. -/
theorem p4Q2PZ37AMU_actualPhysicalGaussMode_orthonormal (H : ℕ) :
    Orthonormal ℝ (p4Q2PZ37AMU_actualPhysicalGaussMode H) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h :=
    (orthonormal_iff_ite.mp
      (p4Q2PZ37AMS_primarySpatialSliceWilsonEnergy_orthonormal H)) i j
  simpa only [p4Q2PZ37AMU_actualPhysicalGaussMode,
    Function.comp_def] using h

/-- No finite-dimensionality hypothesis: the genuinely gauge-invariant
physical finite-lattice SU(2) Hilbert carrier is infinite dimensional,
because its concrete Wilson-energy modes are orthonormal over all natural
numbers. -/
theorem p4Q2PZ37AMU_actualPhysicalGaussHilbert_not_finiteDimensional
    (H : ℕ) :
    ¬ FiniteDimensional ℝ
      (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) := by
  exact not_finiteDimensional_of_nat_linearIndependent
    (p4Q2PZ37AMU_actualPhysicalGaussMode H)
    (p4Q2PZ37AMU_actualPhysicalGaussMode_orthonormal H).linearIndependent

/-- A unit excitation in the ORTHOGONAL COMPLEMENT of the original physical
normalized Wilson transfer's entire eigenvalue-one subspace.

The genuine finite-volume top simplicity theorem proves that full top is
exactly the line of the nonnegative normalized top eigenvector. Combined
with infinite-dimensionality from the ACTUAL AMT Gauss modes, the existing
Hilbert-basis extension theorem constructs the desired orthogonal vector.
No one-dimensionality, OS-surjectivity or abstract physical-excitation
existence assumption is introduced. -/
theorem p4Q2PZ37AMU_exists_originalPhysical_unitTopOrthogonalExcitation
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ v : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2,
      ‖v‖ = 1 ∧
        v ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H 2 (by norm_num) beta hbeta := by
  let hTwo : 0 < (2 : ℕ) := by norm_num
  let Ω : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 hTwo beta hbeta
  have hΩ : ‖Ω‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H 2 hTwo beta hbeta
  let J : VacuumOrthogonalOrthonormalSequenceData Ω :=
    vacuumOrthogonalOrthonormalSequenceDataOfNotFiniteDimensional
      Ω hΩ (p4Q2PZ37AMU_actualPhysicalGaussHilbert_not_finiteDimensional H)
  have htop :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H 2 hTwo beta hbeta = ℝ ∙ Ω := by
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_nonnegativeTopEigenvector
      H 2 hTwo beta hbeta
  have hOrth : ⟪Ω, J.excitation 0⟫_ℝ = 0 :=
    J.vacuum_orthogonal_excitation 0
  refine ⟨J.excitation 0, J.excitation_orthonormal.1 0, ?_⟩
  change J.excitation 0 ∈
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H 2 hTwo beta hbeta)ᗮ
  rw [htop]
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right
    (𝕜 := ℝ) (u := Ω) (v := J.excitation 0)).mpr hOrth

/-- Explicit typed nonzero existence follows from the constructed unit
excitation; this is stronger than an abstract Nontrivial instance and is in
the original normalized finite Wilson top-eigenspace orthogonal complement. -/
theorem p4Q2PZ37AMU_exists_originalPhysical_nonzeroTopOrthogonalExcitation
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ v : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2,
      v ≠ 0 ∧
        v ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H 2 (by norm_num) beta hbeta := by
  obtain ⟨v, hvUnit, hvOrth⟩ :=
    p4Q2PZ37AMU_exists_originalPhysical_unitTopOrthogonalExcitation H beta hbeta
  refine ⟨v, ?_, hvOrth⟩
  intro hvZero
  have hNormZero : ‖v‖ = 0 := by simp [hvZero]
  linarith

end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMU_actualPhysicalGaussMode_orthonormal
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMU_actualPhysicalGaussHilbert_not_finiteDimensional
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMU_exists_originalPhysical_unitTopOrthogonalExcitation
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMU_exists_originalPhysical_nonzeroTopOrthogonalExcitation
