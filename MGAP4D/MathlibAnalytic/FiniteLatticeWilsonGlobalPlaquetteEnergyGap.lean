import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonConditionalActionOscillation

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The finite set of values taken by the plaquette energy. -/
noncomputable def FiniteLatticeWilsonSystem.plaquetteEnergyValues
    (L : FiniteLatticeWilsonSystem) : Finset ℝ := by
  classical
  exact Finset.univ.image L.plaquetteEnergy

/-- The finite plaquette-energy value set is nonempty. -/
theorem finite_lattice_plaquetteEnergyValues_nonempty
    (L : FiniteLatticeWilsonSystem) :
    L.plaquetteEnergyValues.Nonempty := by
  classical
  refine ⟨L.plaquetteEnergy default, ?_⟩
  unfold FiniteLatticeWilsonSystem.plaquetteEnergyValues
  exact Finset.mem_image.mpr ⟨default, Finset.mem_univ _, rfl⟩

/-- Exact maximum of the plaquette energy on the finite gauge group. -/
noncomputable def FiniteLatticeWilsonSystem.plaquetteEnergyMax
    (L : FiniteLatticeWilsonSystem) : ℝ :=
  L.plaquetteEnergyValues.max'
    (finite_lattice_plaquetteEnergyValues_nonempty L)

/-- Every concrete plaquette energy is bounded by the exact finite maximum. -/
theorem finite_lattice_plaquetteEnergy_le_max
    (L : FiniteLatticeWilsonSystem)
    (g : L.Gauge) :
    L.plaquetteEnergy g ≤ L.plaquetteEnergyMax := by
  classical
  unfold FiniteLatticeWilsonSystem.plaquetteEnergyMax
  apply Finset.le_max'
  unfold FiniteLatticeWilsonSystem.plaquetteEnergyValues
  exact Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩

/-- The exact plaquette-energy maximum is nonnegative. -/
theorem finite_lattice_plaquetteEnergyMax_nonneg
    (L : FiniteLatticeWilsonSystem) :
    0 ≤ L.plaquetteEnergyMax :=
  le_trans (L.plaquetteEnergy_nonneg default)
    (finite_lattice_plaquetteEnergy_le_max L default)

/-- Coarse explicit action-oscillation scale: twice the plaquette count times
its exact energy maximum. -/
def FiniteLatticeWilsonSystem.globalPlaquetteEnergyActionOscillation
    (L : FiniteLatticeWilsonSystem) : ℝ :=
  2 * (Fintype.card L.Plaquette : ℝ) * L.plaquetteEnergyMax

/-- The global plaquette-energy action scale is nonnegative. -/
theorem finite_lattice_globalPlaquetteEnergyActionOscillation_nonneg
    (L : FiniteLatticeWilsonSystem) :
    0 ≤ L.globalPlaquetteEnergyActionOscillation := by
  unfold FiniteLatticeWilsonSystem.globalPlaquetteEnergyActionOscillation
  exact mul_nonneg
    (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    (finite_lattice_plaquetteEnergyMax_nonneg L)

/-- Every target-local Wilson action is nonnegative. -/
theorem finite_lattice_targetLocalPlaquetteAction_nonneg
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    0 ≤ L.targetLocalPlaquetteAction A target := by
  classical
  unfold FiniteLatticeWilsonSystem.targetLocalPlaquetteAction
  apply Finset.sum_nonneg
  intro p _hp
  by_cases hTouch : L.PlaquetteTouchesEdge p target
  · simp [hTouch, L.plaquetteEnergy_nonneg]
  · simp [hTouch]

/-- The target-local action is bounded by the total plaquette count times the
exact finite plaquette-energy maximum. -/
theorem finite_lattice_targetLocalPlaquetteAction_le_globalEnergy
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.targetLocalPlaquetteAction A target ≤
      (Fintype.card L.Plaquette : ℝ) * L.plaquetteEnergyMax := by
  classical
  unfold FiniteLatticeWilsonSystem.targetLocalPlaquetteAction
  calc
    (∑ p ∈ Finset.univ,
        if L.PlaquetteTouchesEdge p target then
          L.plaquetteEnergy (L.plaquetteHolonomy A p)
        else 0) ≤
      ∑ _p : L.Plaquette, L.plaquetteEnergyMax := by
        apply Finset.sum_le_sum
        intro p _hp
        by_cases hTouch : L.PlaquetteTouchesEdge p target
        · simp only [if_pos hTouch]
          exact finite_lattice_plaquetteEnergy_le_max L _
        · simp only [if_neg hTouch]
          exact finite_lattice_plaquetteEnergyMax_nonneg L
    _ = (Fintype.card L.Plaquette : ℝ) * L.plaquetteEnergyMax := by
      simp [nsmul_eq_mul]

/-- Any two target-local actions differ by at most the global energy scale. -/
theorem finite_lattice_targetLocalPlaquetteAction_abs_sub_le_globalEnergy
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (target : L.Edge) :
    |L.targetLocalPlaquetteAction A target -
        L.targetLocalPlaquetteAction B target| ≤
      (Fintype.card L.Plaquette : ℝ) * L.plaquetteEnergyMax := by
  have hA0 := finite_lattice_targetLocalPlaquetteAction_nonneg L A target
  have hB0 := finite_lattice_targetLocalPlaquetteAction_nonneg L B target
  have hA := finite_lattice_targetLocalPlaquetteAction_le_globalEnergy L A target
  have hB := finite_lattice_targetLocalPlaquetteAction_le_globalEnergy L B target
  apply abs_sub_le_iff.mpr
  constructor <;> linarith

/-- The local action-difference oscillation is explicitly bounded by twice the
global target-local action scale. -/
theorem finite_lattice_activeLocalActionDifferenceOscillationBound_globalEnergy
    (L : FiniteLatticeWilsonSystem) :
    L.ActiveLocalActionDifferenceOscillationBound
      L.globalPlaquetteEnergyActionOscillation := by
  intro target source A g _hActive u v
  have hu :=
    finite_lattice_targetLocalPlaquetteAction_abs_sub_le_globalEnergy
      L (L.replaceLink A target u)
        (L.replaceLink (L.replaceLink A source g) target u) target
  have hv :=
    finite_lattice_targetLocalPlaquetteAction_abs_sub_le_globalEnergy
      L (L.replaceLink A target v)
        (L.replaceLink (L.replaceLink A source g) target v) target
  have huBounds := abs_le.mp hu
  have hvBounds := abs_le.mp hv
  unfold FiniteLatticeWilsonSystem.globalPlaquetteEnergyActionOscillation
  linarith

/-- Concrete conditional likelihood-ratio control from the finite energy
maximum and plaquette count. -/
theorem finite_lattice_activeConditionalExpRatioBound_globalPlaquetteEnergy
    (L : FiniteLatticeWilsonSystem) :
    L.ActiveConditionalExpRatioBound
      (L.beta * L.globalPlaquetteEnergyActionOscillation) :=
  finite_lattice_activeConditionalExpRatioBound_of_localActionOscillation
    L L.globalPlaquetteEnergyActionOscillation
      (finite_lattice_globalPlaquetteEnergyActionOscillation_nonneg L)
      (finite_lattice_activeLocalActionDifferenceOscillationBound_globalEnergy L)

/-- The exact active influence maximum is bounded by the corresponding explicit
normalized-exponential majorant. -/
theorem finite_lattice_canonicalActivePlaquetteInfluenceBound_le_globalEnergyExpRatio
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalActivePlaquetteInfluenceBound hEdge ≤
      (Real.exp
          (L.beta * L.globalPlaquetteEnergyActionOscillation) - 1) /
        (Real.exp
          (L.beta * L.globalPlaquetteEnergyActionOscillation) + 1) :=
  finite_lattice_canonicalActivePlaquetteInfluenceBound_le_expRatioBound
    L hEdge (L.beta * L.globalPlaquetteEnergyActionOscillation)
      (mul_nonneg L.beta_nonneg
        (finite_lattice_globalPlaquetteEnergyActionOscillation_nonneg L))
      (finite_lattice_activeConditionalExpRatioBound_globalPlaquetteEnergy L)

/-- The explicit scalar threshold implies strict canonical Dobrushin
contraction. -/
theorem finite_lattice_canonicalDobrushinCoefficient_lt_one_of_globalPlaquetteEnergy
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (hDegreePos : 0 < L.canonicalActivePlaquetteDegree hEdge)
    (hThreshold :
      (Real.exp
          (L.beta * L.globalPlaquetteEnergyActionOscillation) - 1) /
          (Real.exp
            (L.beta * L.globalPlaquetteEnergyActionOscillation) + 1) <
        (L.canonicalActivePlaquetteDegree hEdge : ℝ)⁻¹) :
    L.canonicalDobrushinCoefficient hEdge < 1 :=
  finite_lattice_canonicalDobrushinCoefficient_lt_one_of_activeConditionalExpRatio
    L hEdge hDegreePos
      (L.beta * L.globalPlaquetteEnergyActionOscillation)
      (mul_nonneg L.beta_nonneg
        (finite_lattice_globalPlaquetteEnergyActionOscillation_nonneg L))
      (finite_lattice_activeConditionalExpRatioBound_globalPlaquetteEnergy L)
      hThreshold

/-- Family-level concrete input using each finite Wilson system's plaquette
count, exact energy maximum, coupling, and active degree. -/
structure FiniteWilsonGlobalPlaquetteEnergyFamilyData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  edgeCard_pos : ∀ i : W.index, 0 < Fintype.card (W.system i).Edge
  activeDegree_pos : ∀ i : W.index,
    0 < (W.system i).canonicalActivePlaquetteDegree (edgeCard_pos i)
  globalEnergyThreshold : ∀ i : W.index,
    (Real.exp
        ((W.system i).beta *
          (W.system i).globalPlaquetteEnergyActionOscillation) - 1) /
        (Real.exp
          ((W.system i).beta *
            (W.system i).globalPlaquetteEnergyActionOscillation) + 1) <
      ((W.system i).canonicalActivePlaquetteDegree (edgeCard_pos i) : ℝ)⁻¹

/-- Convert the concrete energy criterion into the action-oscillation family
package. -/
noncomputable def
    FiniteWilsonGlobalPlaquetteEnergyFamilyData.toActionOscillationFamilyData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonGlobalPlaquetteEnergyFamilyData W) :
    FiniteWilsonActiveLocalActionOscillationFamilyData W :=
  { edgeCard_pos := D.edgeCard_pos
    activeDegree_pos := D.activeDegree_pos
    actionOscillation := fun i =>
      (W.system i).globalPlaquetteEnergyActionOscillation
    actionOscillation_nonneg := fun i =>
      finite_lattice_globalPlaquetteEnergyActionOscillation_nonneg (W.system i)
    activeLocalActionOscillationBound := fun i =>
      finite_lattice_activeLocalActionDifferenceOscillationBound_globalEnergy
        (W.system i)
    normalizedExpTV_lt_inv_activeDegree := D.globalEnergyThreshold }

/-- Concrete finite plaquette-energy data generate normalized Hamiltonian gap
data at every scale. -/
noncomputable def
    FiniteWilsonGlobalPlaquetteEnergyFamilyData.hamiltonianGapData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonGlobalPlaquetteEnergyFamilyData W)
    (i : W.index) :
    FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData :=
  D.toActionOscillationFamilyData.hamiltonianGapData i

/-- The concrete global energy threshold gives normalized Hamiltonian exact-gap
coercivity on every finite-volume vacuum-orthogonal sector. -/
theorem finite_wilson_global_plaquette_energy_family_hamiltonian_gap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonGlobalPlaquetteEnergyFamilyData W)
    (i : W.index)
    (x : (W.system i).GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal (W.system i).gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ
        ((W.system i).gibbsDobrushinScaledHeatBathHamiltonianLinearMap
          (D.toActionOscillationFamilyData.toConditionalExpRatioFamilyData.toReciprocalInfluenceFamilyData.toProductFamilyData.rayleighFamilyData.atScale i)
          x) x :=
  finite_wilson_active_local_action_oscillation_family_hamiltonian_gap
    W D.toActionOscillationFamilyData i x hx

/-- Every excitation-sector eigenvalue generated by the concrete global energy
criterion is bounded below by the public exact gap. -/
theorem finite_wilson_global_plaquette_energy_family_restricted_eigenvalues_ge_exactGap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonGlobalPlaquetteEnergyFamilyData W)
    (i : W.index)
    (j : Fin (D.hamiltonianGapData i).ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        (D.hamiltonianGapData i).toVacuumOrthogonalGapData 0).eigenvalues
          (D.hamiltonianGapData i).excitedFinrank j :=
  finite_wilson_active_local_action_oscillation_family_restricted_eigenvalues_ge_exactGap
    W D.toActionOscillationFamilyData i j

end

end MathlibAnalytic
end MGAP4D
