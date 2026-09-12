import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVariationalInfraredMass
import Mathlib.Tactic

/-!
# Variational OS infrared mass below the derived physical Yang--Mills mass

The state-independent OS infrared mass is already the infimum of all nonzero
vacuum-orthogonal statewise infrared exponents.  On the canonical right-
generator domain, each such infrared exponent is bounded above by the
Hamiltonian Rayleigh quotient.  This file passes that scalar lower bound through
the existing graph closure without introducing a spectral theorem or an
attainment hypothesis.

The key reusable statement is graph-theoretic: any vacuum-orthogonal quadratic
lower bound on the canonical right Hamiltonian extends to the graph-closed right
Hamiltonian.  The proof uses the same normalized-vacuum orthogonalization of
graph approximants as the existing transfer-gap closure theorem, but no
`VacuumSemigroupGapSlope` is needed.

Consequently

`physicalYangMillsOSInfraredMass <= physicalYangMillsMass`.

Combined with the preceding transfer theorem this yields

`0 < G.mass <= physicalYangMillsOSInfraredMass <= physicalYangMillsMass`.

No numerical mass value, PVM hypothesis, spectral-attainment assumption, or new
physical axiom is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Any vacuum-orthogonal quadratic lower bound on the canonical right
Hamiltonian passes through its graph closure.

Normalization makes the vacuum a unit vector.  Every graph-approximating core
vector can therefore be orthogonalized by subtracting its vacuum coefficient;
the right Hamiltonian annihilates the vacuum, so this changes only the base
component and leaves the Hamiltonian value unchanged. -/
theorem closedRightHamiltonian_inner_ge_of_rightHamiltonian_inner_ge
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (m : ℝ)
    (hCore :
      ∀ phi : T.rightGeneratorDomain,
        inner ℝ (phi : P.PhysicalHilbert) P.vacuum = 0 →
        m * ‖(phi : P.PhysicalHilbert)‖ ^ 2 ≤
          inner ℝ (T.rightHamiltonian phi) (phi : P.PhysicalHilbert))
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    m * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  have hgraph :
      ((psi : P.PhysicalHilbert), T.closedRightHamiltonian psi) ∈
        T.rightHamiltonianLinearPMap.graph.topologicalClosure := by
    rw [T.closedRightHamiltonian_graph_eq]
    exact T.closedRightHamiltonian.mem_graph psi
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    mem_closure_iff_seq_limit] at hgraph
  rcases hgraph with ⟨u, huGraph, hu⟩
  choose z hzBase hzValue using fun n =>
    (LinearPMap.mem_graph_iff T.rightHamiltonianLinearPMap).1 (huGraph n)
  have huFst :
      Tendsto (fun n => (u n).1) atTop
        (nhds (psi : P.PhysicalHilbert)) := by
    simpa only [Function.comp_apply] using
      (continuous_fst.tendsto
        ((psi : P.PhysicalHilbert), T.closedRightHamiltonian psi)).comp hu
  have hbaseEq :
      (fun n => (u n).1) =
        fun n => ((z n : T.rightHamiltonianLinearPMap.domain) :
          P.PhysicalHilbert) :=
    funext fun n => (hzBase n).symm
  rw [hbaseEq] at huFst
  have huSnd :
      Tendsto (fun n => (u n).2) atTop
        (nhds (T.closedRightHamiltonian psi)) := by
    simpa only [Function.comp_apply] using
      (continuous_snd.tendsto
        ((psi : P.PhysicalHilbert), T.closedRightHamiltonian psi)).comp hu
  have hvalueEq :
      (fun n => (u n).2) =
        fun n => T.rightHamiltonianLinearPMap (z n) := by
    funext n
    exact (hzValue n).symm
  rw [hvalueEq] at huSnd

  let zCore : ℕ → T.rightGeneratorDomain := fun n =>
    (show T.rightGeneratorDomain from z n)
  have hzCoreFst :
      Tendsto (fun n => ((zCore n : T.rightGeneratorDomain) :
        P.PhysicalHilbert)) atTop
        (nhds (psi : P.PhysicalHilbert)) := by
    simpa only [zCore] using huFst
  have hzCoreSnd :
      Tendsto (fun n => T.rightHamiltonian (zCore n)) atTop
        (nhds (T.closedRightHamiltonian psi)) := by
    simpa only [zCore, T.rightHamiltonianLinearPMap_apply] using huSnd

  let vacuumDomain : T.rightGeneratorDomain :=
    ⟨P.vacuum, T.vacuum_mem_rightHamiltonianDomain⟩
  let coefficient : ℕ → ℝ := fun n =>
    inner ℝ ((zCore n : T.rightGeneratorDomain) : P.PhysicalHilbert) P.vacuum
  let zOrth : ℕ → T.rightGeneratorDomain := fun n =>
    zCore n - coefficient n • vacuumDomain

  have hvacuumInner : inner ℝ P.vacuum P.vacuum = 1 := by
    rw [real_inner_self_eq_norm_sq, P.norm_vacuum hP]
    norm_num
  have hVacuumHamiltonian : T.rightHamiltonian vacuumDomain = 0 := by
    simpa only [vacuumDomain] using T.rightHamiltonian_vacuum
  have hzOrthogonal (n : ℕ) :
      inner ℝ ((zOrth n : T.rightGeneratorDomain) : P.PhysicalHilbert)
        P.vacuum = 0 := by
    change inner ℝ
        (((zCore n : T.rightGeneratorDomain) : P.PhysicalHilbert) -
          coefficient n • P.vacuum)
        P.vacuum = 0
    rw [inner_sub_left, real_inner_smul_left, hvacuumInner, mul_one]
    simp [coefficient]
  have hCoefficient : Tendsto coefficient atTop (nhds 0) := by
    have hinner :
        Tendsto
          (fun n => inner ℝ
            ((zCore n : T.rightGeneratorDomain) : P.PhysicalHilbert)
            P.vacuum)
          atTop
          (nhds (inner ℝ (psi : P.PhysicalHilbert) P.vacuum)) :=
      hzCoreFst.inner (𝕜 := ℝ) tendsto_const_nhds
    simpa only [coefficient, hpsi] using hinner
  have hzOrthFst :
      Tendsto (fun n => ((zOrth n : T.rightGeneratorDomain) :
        P.PhysicalHilbert)) atTop
        (nhds (psi : P.PhysicalHilbert)) := by
    change Tendsto
      (fun n =>
        ((zCore n : T.rightGeneratorDomain) : P.PhysicalHilbert) -
          coefficient n • P.vacuum)
      atTop (nhds (psi : P.PhysicalHilbert))
    simpa using hzCoreFst.sub (hCoefficient.smul_const P.vacuum)
  have hzOrthValue (n : ℕ) :
      T.rightHamiltonian (zOrth n) = T.rightHamiltonian (zCore n) := by
    change T.rightHamiltonian (zCore n - coefficient n • vacuumDomain) =
      T.rightHamiltonian (zCore n)
    rw [map_sub, map_smul, hVacuumHamiltonian, smul_zero, sub_zero]
  have hzOrthSnd :
      Tendsto (fun n => T.rightHamiltonian (zOrth n)) atTop
        (nhds (T.closedRightHamiltonian psi)) := by
    rw [show (fun n => T.rightHamiltonian (zOrth n)) =
        (fun n => T.rightHamiltonian (zCore n)) by
      funext n
      exact hzOrthValue n]
    exact hzCoreSnd

  have hLeft :
      Tendsto
        (fun n => m *
          ‖((zOrth n : T.rightGeneratorDomain) : P.PhysicalHilbert)‖ ^ 2)
        atTop
        (nhds (m * ‖(psi : P.PhysicalHilbert)‖ ^ 2)) :=
    tendsto_const_nhds.mul ((hzOrthFst.norm).pow 2)
  have hRight :
      Tendsto
        (fun n => inner ℝ (T.rightHamiltonian (zOrth n))
          ((zOrth n : T.rightGeneratorDomain) : P.PhysicalHilbert))
        atTop
        (nhds
          (inner ℝ (T.closedRightHamiltonian psi)
            (psi : P.PhysicalHilbert))) :=
    hzOrthSnd.inner hzOrthFst
  apply le_of_tendsto_of_tendsto hLeft hRight
  exact Filter.Eventually.of_forall fun n => hCore (zOrth n) (hzOrthogonal n)

/-- The variational OS infrared mass is a quadratic lower bound for the
canonical right Hamiltonian on the vacuum-orthogonal generator domain. -/
theorem physicalYangMillsOSInfraredMass_mul_norm_sq_le_rightHamiltonian_inner
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    T.physicalYangMillsOSInfraredMass *
        ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) := by
  by_cases hpsi_ne : (psi : P.PhysicalHilbert) ≠ 0
  · have hIR :
        T.physicalYangMillsOSInfraredMass ≤
          T.physicalCorrelationRealClampInfraredEffectiveMass
            (psi : P.PhysicalHilbert) :=
      T.physicalYangMillsOSInfraredMass_le_statewise
        hSymmetric hpsi_ne hpsi
    have hRayleigh :
        T.physicalCorrelationRealClampInfraredEffectiveMass
            (psi : P.PhysicalHilbert) ≤
          inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) /
            ‖(psi : P.PhysicalHilbert)‖ ^ 2 :=
      T.physicalCorrelationRealClampInfraredEffectiveMass_le_rightHamiltonian_rayleigh
        hSymmetric psi hpsi_ne
    have hden : 0 < ‖(psi : P.PhysicalHilbert)‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hpsi_ne)
    exact (le_div_iff₀ hden).mp (hIR.trans hRayleigh)
  · push_neg at hpsi_ne
    simp [hpsi_ne]

/-- The same OS infrared lower edge therefore controls every vacuum-orthogonal
state in the graph-closed Hamiltonian domain. -/
theorem physicalYangMillsOSInfraredMass_mul_norm_sq_le_closedRightHamiltonian_inner
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    T.physicalYangMillsOSInfraredMass *
        ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  apply T.closedRightHamiltonian_inner_ge_of_rightHamiltonian_inner_ge
    hP T.physicalYangMillsOSInfraredMass
  · intro phi hphi
    exact T.physicalYangMillsOSInfraredMass_mul_norm_sq_le_rightHamiltonian_inner
      hSymmetric phi hphi
  · exact hpsi

/-- The state-independent OS infrared mass lies below the variational mass of
the actual graph-closed physical Yang--Mills Hamiltonian. -/
theorem physicalYangMillsOSInfraredMass_le_physicalYangMillsMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    T.physicalYangMillsOSInfraredMass ≤ T.physicalYangMillsMass := by
  apply T.uniformRayleighLowerBound_le_physicalYangMillsMass W
  intro psi _hpsi horthogonal
  exact T.physicalYangMillsOSInfraredMass_mul_norm_sq_le_closedRightHamiltonian_inner
    hP hSymmetric psi horthogonal

/-- A positive vacuum transfer slope, the state-independent OS infrared mass,
and the actual graph-closed Hamiltonian mass form one ordered physical chain. -/
theorem VacuumSemigroupGapSlope.mass_le_osInfraredMass_le_physicalYangMillsMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    0 < G.mass ∧
      G.mass ≤ T.physicalYangMillsOSInfraredMass ∧
      T.physicalYangMillsOSInfraredMass ≤ T.physicalYangMillsMass := by
  exact ⟨G.mass_pos,
    G.mass_le_physicalYangMillsOSInfraredMass T hSymmetric W,
    T.physicalYangMillsOSInfraredMass_le_physicalYangMillsMass
      hP hSymmetric W⟩

/-- Finite-volume transfer data expose the same ordered chain through their
associated continuum vacuum gap slope. -/
theorem FiniteVolumeVacuumGapTransfer.mass_le_osInfraredMass_le_physicalYangMillsMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    0 < G.mass ∧
      G.mass ≤ T.physicalYangMillsOSInfraredMass ∧
      T.physicalYangMillsOSInfraredMass ≤ T.physicalYangMillsMass := by
  exact ⟨G.mass_pos,
    G.mass_le_physicalYangMillsOSInfraredMass T hSymmetric W,
    T.physicalYangMillsOSInfraredMass_le_physicalYangMillsMass
      hP hSymmetric W⟩

/-- After self-adjoint reconstruction, nontriviality of the complete excitation
Hilbert space supplies the witness for the full variational chain. -/
theorem VacuumSemigroupGapSlope.mass_le_osInfraredMass_le_physicalYangMillsMass_of_nontrivial
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    [Nontrivial P.VacuumOrthogonalHilbert] :
    0 < G.mass ∧
      G.mass ≤ T.physicalYangMillsOSInfraredMass ∧
      T.physicalYangMillsOSInfraredMass ≤ T.physicalYangMillsMass := by
  let W := T.physicalYangMillsExcitationDomainWitness_of_nontrivial hP hSelf
  exact G.mass_le_osInfraredMass_le_physicalYangMillsMass
    T hP hSymmetric W

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
