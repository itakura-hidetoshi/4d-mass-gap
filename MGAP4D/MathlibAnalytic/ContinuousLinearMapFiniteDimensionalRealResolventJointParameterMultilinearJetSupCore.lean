import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterMultilinearJetOperatorNormResponse
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The maximum of a real-valued finite dependent family.  The explicit
`Nonempty` hypothesis is exactly what is needed by `Finset.sup'`. -/
def finiteDependentSupGauge
    {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) : ℝ :=
  (Finset.univ : Finset I).sup' Finset.univ_nonempty f

/-- The finite dependent supremum is below a threshold exactly when every
component is below that threshold. -/
theorem finiteDependentSupGauge_lt_iff
    {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) (c : ℝ) :
    finiteDependentSupGauge f < c ↔ ∀ i, f i < c := by
  unfold finiteDependentSupGauge
  rw [Finset.sup'_lt_iff Finset.univ_nonempty]
  simp

/-- A finite rectangular supremum, used for a Taylor-order by joint-Fréchet-
order jet. -/
def finiteRectangularSupGauge
    {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (f : I → J → ℝ) : ℝ :=
  finiteDependentSupGauge (fun i => finiteDependentSupGauge (f i))

/-- A finite rectangular supremum is below a threshold exactly when all of its
components are below that threshold. -/
theorem finiteRectangularSupGauge_lt_iff
    {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (f : I → J → ℝ) (c : ℝ) :
    finiteRectangularSupGauge f < c ↔ ∀ i j, f i j < c := by
  simp [finiteRectangularSupGauge, finiteDependentSupGauge_lt_iff]

/-- The finite dependent supremum of nonnegative components is nonnegative. -/
theorem finiteDependentSupGauge_nonneg
    {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    0 ≤ finiteDependentSupGauge f := by
  by_contra h
  have hlt : finiteDependentSupGauge f < 0 := lt_of_not_ge h
  have hall := (finiteDependentSupGauge_lt_iff f 0).1 hlt
  exact (not_lt_of_ge (hf (Classical.choice inferInstance)))
    (hall (Classical.choice inferInstance))

/-- The finite rectangular supremum of nonnegative components is
nonnegative. -/
theorem finiteRectangularSupGauge_nonneg
    {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (f : I → J → ℝ) (hf : ∀ i j, 0 ≤ f i j) :
    0 ≤ finiteRectangularSupGauge f := by
  apply finiteDependentSupGauge_nonneg
  intro i
  exact finiteDependentSupGauge_nonneg (f i) (hf i)

/-- A complete finite jet of joint spectral/operator Fréchet multilinear
carriers, indexed through order `order`.  The multilinear arity genuinely
depends on the jet index. -/
abbrev ContinuousLinearMapJointMultilinearCarrierJet
    (V W : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (m order : ℕ) :=
  ∀ n : Fin (order + 1),
    ContinuousMultilinearMap ℝ
      (fun _ : Fin n.1 => (Fin (m + 1) → ℝ)) W

/-- A finite Taylor-order by joint-Fréchet-order rectangular carrier jet. -/
abbrev ContinuousLinearMapJointMultilinearCarrierRectangularJet
    (V W : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (m taylorOrder mixedOrder : ℕ) :=
  ∀ _k : Fin (taylorOrder + 1),
    ContinuousLinearMapJointMultilinearCarrierJet V W m mixedOrder

/-- Intrinsic maximum component distance on a complete finite dependent jet. -/
def continuousLinearMapJointMultilinearCarrierJetSupDistance
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {m order : ℕ}
    (A B : ContinuousLinearMapJointMultilinearCarrierJet V W m order) : ℝ :=
  finiteDependentSupGauge (fun n => ‖A n - B n‖)

/-- Intrinsic maximum component distance on a finite rectangular jet. -/
def continuousLinearMapJointMultilinearCarrierRectangularJetSupDistance
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {m taylorOrder mixedOrder : ℕ}
    (A B : ContinuousLinearMapJointMultilinearCarrierRectangularJet
      V W m taylorOrder mixedOrder) : ℝ :=
  finiteRectangularSupGauge (fun k n => ‖A k n - B k n‖)

/-- The complete-jet sup distance is below `epsilon` exactly when every
multilinear component is below `epsilon`. -/
theorem continuousLinearMapJointMultilinearCarrierJetSupDistance_lt_iff
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {m order : ℕ}
    (A B : ContinuousLinearMapJointMultilinearCarrierJet V W m order)
    (epsilon : ℝ) :
    continuousLinearMapJointMultilinearCarrierJetSupDistance A B < epsilon ↔
      ∀ n, ‖A n - B n‖ < epsilon := by
  exact finiteDependentSupGauge_lt_iff (fun n => ‖A n - B n‖) epsilon

/-- The rectangular-jet sup distance is below `epsilon` exactly when every
Taylor-order/joint-order component is below `epsilon`. -/
theorem continuousLinearMapJointMultilinearCarrierRectangularJetSupDistance_lt_iff
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {m taylorOrder mixedOrder : ℕ}
    (A B : ContinuousLinearMapJointMultilinearCarrierRectangularJet
      V W m taylorOrder mixedOrder) (epsilon : ℝ) :
    continuousLinearMapJointMultilinearCarrierRectangularJetSupDistance A B < epsilon ↔
      ∀ k n, ‖A k n - B k n‖ < epsilon := by
  exact finiteRectangularSupGauge_lt_iff
    (fun k n => ‖A k n - B k n‖) epsilon

/-- Complete Banach-valued response jet generated by one compressed real
resolvent. -/
def continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m order : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (R : V →L[ℝ] V) :
    ContinuousLinearMapJointMultilinearCarrierJet V W m order :=
  fun n =>
    continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
      φ m n.1 H R

@[simp]
theorem continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent_apply
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m order : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (R : V →L[ℝ] V)
    (n : Fin (order + 1)) :
    continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
      φ m order H R n =
    continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
      φ m n.1 H R :=
  rfl

/-- Complete basis-independent trace jet generated by one compressed real
resolvent. -/
def continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m order : ℕ) (H : Fin m → (V →L[ℝ] V)) (R : V →L[ℝ] V) :
    ContinuousLinearMapJointMultilinearCarrierJet V ℝ m order :=
  continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
    (continuousLinearMapTrace (V := V)) m order H R

@[simp]
theorem continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent_apply
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m order : ℕ) (H : Fin m → (V →L[ℝ] V)) (R : V →L[ℝ] V)
    (n : Fin (order + 1)) :
    continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent
      V m order H R n =
    continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent
      V m n.1 H R :=
  rfl

/-- Rectangular carrier jet generated by a finite family of compressed real
resolvents, one at each ambient Taylor order. -/
def continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierRectangularJetFromResolventFamily
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m taylorOrder mixedOrder : ℕ) (H : Fin m → (V →L[ℝ] V))
    (R : Fin (taylorOrder + 1) → (V →L[ℝ] V)) :
    ContinuousLinearMapJointMultilinearCarrierRectangularJet
      V (V →L[ℝ] V) m taylorOrder mixedOrder :=
  fun k =>
    continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent
      m (mixedOrder + 1) H (R k)

/-- Rectangular Banach-valued response jet generated by a finite resolvent
family. -/
def continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m taylorOrder mixedOrder : ℕ)
    (H : Fin m → (V →L[ℝ] V))
    (R : Fin (taylorOrder + 1) → (V →L[ℝ] V)) :
    ContinuousLinearMapJointMultilinearCarrierRectangularJet
      V W m taylorOrder mixedOrder :=
  fun k =>
    continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
      φ m mixedOrder H (R k)

/-- Rectangular basis-independent trace jet generated by a finite resolvent
family. -/
def continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m taylorOrder mixedOrder : ℕ) (H : Fin m → (V →L[ℝ] V))
    (R : Fin (taylorOrder + 1) → (V →L[ℝ] V)) :
    ContinuousLinearMapJointMultilinearCarrierRectangularJet
      V ℝ m taylorOrder mixedOrder :=
  continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily
    (continuousLinearMapTrace (V := V)) m taylorOrder mixedOrder H R

end MathlibAnalytic
end MGAP4D
