# P4-Q2-PZ37AJY — 真正AJU二乗冪の十分条件に対する限定障害

2026年11月11日 JST。Lean4定理の機械検証結果と実行来歴を記録する。説明文書自体は形式証明ではない。

## Canonical source and verification
- Repository: `itakura-hidetoshi/4d-mass-gap`。定理正本: `formal/real-hilbert-uniform-coercive-strong-limit`。mainは文書ミラー。
- 新規leaf: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAJUSecondPowerBudgetNoGoV5_PZ37AJY.lean`。既存Lean/物理定義は変更なし。
- [定理PR #6649](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6649) MERGED。source HEAD `86ae17bbf2a4789d55843029a96291877aa6eeca`。
- [Exact-source CI #43005620828](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43005620828) completed/SUCCESS、Lean依存閉包 11,439/11,439。新規6宣言・公理監査6/6は `propext`, `Classical.choice`, `Quot.sound` のみ。新規 `sorryAx` なし、変更leafのwarning/error 0/0。独立completion receipt jobおよびexact-head commit status SUCCESS。
- formal squash HEAD `879bd96508d4d89f92a8d1cd6659fe858ce81091`。source／GitHub test-merge／squash のGit treeはすべて `cdab9308ad43709912e18a0037f167ea67dc3696`。
- 統合後push [#43006708442](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43006708442) は起草時点で完了未確認。後続の完了受領書と区別する。
- Pin: Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。

## 証明された局所的評価
固定有限H、β>0で、`V_H=‖f_{0,H}‖²>0` を元ZW源のHaar分散、`B_{H,β}` を変更のない真正AJA margin×負領域Haar質量証明書とする。AJUの真正直交制限のノルム `q=‖R‖` と物理L²欠損下界 `d=βv_H/exp(βp_H)` を変えず、AJU二乗冪補正 `C₂=(1−q⁴)(d/(1+q))²` とおく。既証明 `v_H≤V_H≤p_H²/4`、`βp_H exp(−βp_H)≤1` とAJXの `B≤V_H/16` から、今回新しく

```
C₂ ≤ d² ≤ V_H / 4
B + C₂ ≤ 5 V_H / 16 < V_H
B < V_H − C₂
¬ (V_H − C₂ < B)
```

を元物理量のままLean4で形式証明した。すなわちAJUの**特定の十分条件** `V_H−C₂<B` はどの有限H、β>0でも成立しない。

## 範囲と未認証
AJUの `‖S²f₀‖²≤V_H−C₂` は実際の冪ノルムの**上界**にすぎない。上界がBを超えても、実際の `‖S²f₀‖²<B` を否定できない。このPRはn=2証人の不存在も、全有限冪証人の不存在も、top一次元性も、H一様coercivityも、Hamiltonian gapも、4D continuum mass gapも証明していない。真の全top射影／有限冪の直接AJA比較はNO_DATAとして保持する。

## Lean4修正履歴
- 初回source `3f35e6da74b705aadccd07f8a13ae430034810de`、[CI #43003622111](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43003622111) FAILURE。局所記法 `dY` は `ℝ → ℝ` 型のため、β適用を欠いた。
- 二回目source `1865f7e52fe9072b4096fbf7e90b8147baa8990c`、[CI #43004760337](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43004760337) FAILURE。 `norm_nonneg _` の暗黙引数推論が曖昧。
- 三回目source `86ae17bbf2a4789d55843029a96291877aa6eeca`、[CI #43005620828](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43005620828) SUCCESS。 `dY beta` と `norm_nonneg (RY beta hbeta.le)` を明示し、定理署名・物理仮定を弱めず6宣言すべて確認。

次段AJZは、粗い十分条件を繰り返さず、実際の `‖Qf₀‖²` 又は `‖Sⁿf₀‖²` と同じ真正AJA証明書を直接比較する橋を探る。append-only／tighten-only／overwrite-forbidden／same-root。
