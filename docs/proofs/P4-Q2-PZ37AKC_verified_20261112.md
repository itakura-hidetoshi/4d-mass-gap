# P4-Q2-PZ37AKC — genuine all-positive Wilson-power Haar–Cauchy floors

2026年11月12日 JST。これは固定Lean4カーネルの検証結果を記録する説明文書であり、このMarkdown自身は証明ではない。

## 1. Primary source, exact-source certification, and independent push

- Repository: `itakura-hidetoshi/4d-mass-gap`. 唯一の定理正本: `formal/real-hilbert-uniform-coercive-strong-limit`. `main`は文書同一blobミラー。
- [AKC theorem PR #6662](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6662) MERGED。認証source HEAD `0ee259ee8c712b88a0a2a030e86a5322e40f43e4`、formal squash `a36bf6966611c557a07aec182495e21aa3c15f82`。
- [Exact-source CI #43109258870](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43109258870) `completed/SUCCESS`。changed-Lean jobおよびLean実行step `completed/SUCCESS`、依存閉包 **11,443/11,443**、独立completion-receipt job `completed/SUCCESS`、source HEADの`chatgpt-ci-receipt/PR Lean Fast Check` `success`。
- [Post-merge formal push CI #43110233807](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43110233807) `event=push`, canonical squash HEADで独立 `completed/SUCCESS`。changed-Lean jobとLean step `completed/SUCCESS`、**11,443/11,443**、独立completion receipt `completed/SUCCESS`、exact-head status `success`。
- 6新規Lean定理と6個の`#print axioms`を確認。各出力に現れる公理は `propext`、`Classical.choice`、`Quot.sound` のみ。`sorryAx`なし、変更AKCファイルのerror/warning 0/0。
- Source、GitHub test-merge、formal squashのGit treeはすべて `f2cda6c622aa9dedb3f281fb2e40373e76fac533` で一致。追加1ファイル268行、既存Leanファイル変更0、削除0。
- 初回source `2d05047329fa3edcd7c2e3ce0c6156841e807a25` の [CI #43108140913](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43108140913) はFAILURE。84行の不要な`simpa` warningと195・211行の`a 0 = ‖f₀‖² = V` の簡約／型整合不成立を検出。新規AKC leaf内だけで`a 0 = V`を明示し、局所`rw`と定義的等号へ修正。定理文、量、仮定は一切弱めていない。
- 新規leaf: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAllPositivePowersHaarCauchyFloorV5_PZ37AKC.lean`。直接imports: AKB、`Mathlib.Analysis.InnerProductSpace.Projection.Basic`、`Mathlib.Tactic`。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。

## 2. Kernel-checked mathematics and precise scope

有限`H : ℕ`、`β>0`で、`S`を真正SU(2) Wilson normalized physical one-slab transfer、`f₀`を元の中心化ZW物理源、`V=‖f₀‖²>0`を真正Haar分散、`B=m²·Measure.real(μ_H)({u<−m})>0`を元AJA Haar証明書とする。`B≤‖Sf₀‖²`は既存AJA定理。

`a_k=‖S^k f₀‖²`とおくと、真正対称作用素のCauchy–Schwarzから任意の`k`で
```
a_(k+1)² ≤ a_k * a_(k+2).
```
`a₀=V>0`、`a₁≥B>0`から、任意`k`に対し`a_k>0`と`a_k*a₁≤a_(k+1)*a₀`を帰納的に導く。よって任意`n:ℕ`で`a₁^(n+1)≤a₀^n*a_(n+1)`。元AJA定理と真正分散の等式を代入して、次を**すべての有限H・β>0・n∈ℕについて**形式証明:
```
B^(n+1) ≤ V^n * ‖S^(n+1) f₀‖²,
0 < B^(n+1)/V^n ≤ ‖S^(n+1) f₀‖².
```
従ってどの正整数冪でも元ZW源の像は零にならない。これは有限Hごとの正の下界であり、`n`や体積`H`について一様な下界とは述べていない。作用素の極限top射影の大きさや厳密AJA上界は別問題。

## 3. Six certified declarations

1. `real_positive_logConvex_sequence_ratio_akc`
2. `real_positive_logConvex_sequence_powerFloor_akc`
3. `realHilbert_symmetric_power_normSq_logConvex_akc`
4. `GroundStatePosteriorJoint.p4Q2PZ37AKC_originalAllPositivePowers_HaarFloor_mul`
5. `GroundStatePosteriorJoint.p4Q2PZ37AKC_originalAllPositivePowers_HaarFloor_div`
6. `GroundStatePosteriorJoint.p4Q2PZ37AKC_originalAllPositivePowers_energy_pos`

すべて`MGAP4D.MathlibAnalytic`名前空間。形式的な定理署名と公理出力はLean leafが権威を持つ。

## 4. OPEN obstructions (NO_DATA)

`‖S^n f₀‖²<B`という実際の元AJA厳密上界は任意の`n≥2`について**未認証**。とくに無条件の`n=2,n=3`証人・不存在はいずれもOPEN。真の全top射影ノルムとAJA予算の数値比較、top一次元性、空間体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップもOPEN。下界から上界／証人／ギャップへの不正な昇格は禁止。

Append-only / tighten-only / overwrite-forbidden / same-root。元Wilson/Haar/ZW/AJAの量・定義・仮定、Lean/mathlib pin、公開rootを変更しない。docs-only Strict Leanの手動実行なし。
