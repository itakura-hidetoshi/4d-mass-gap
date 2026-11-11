# P4-Q2-PZ37AJZ — 元Wilson有限冪と真正AJA証明書の厳密な直交残余判定

2026年11月11日 JST。正本のLean4宣言と固定環境CIに基づく形式証明記録。説明文章自体は形式証明ではない。

## 1. 正本、定理と機械認証
- Repository `itakura-hidetoshi/4d-mass-gap`、定理canonical branch `formal/real-hilbert-uniform-coercive-strong-limit`。mainは文書ミラー。
- 新規leaf `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalExactPowerAJABudgetResidualV5_PZ37AJZ.lean` 242行追加。既存LeanやWilson/Haar物理定義は変更なし。
- [定理PR #6652](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6652) MERGED。
- 認証source HEAD: `529a9354426c2d3d18ef78bb44605c6d59ccbdf8`。
- [Exact-source CI #43008681741](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43008681741) completed/SUCCESS。Lean依存閉包 **11,440／11,440**。6新規宣言／6 `#print axioms` は `propext`, `Classical.choice`, `Quot.sound` のみ。新規sorryAxなし、変更AJZ warning/error0/0、独立completion receiptとexact-head commit status success。
- 正式squash HEAD: `a8b410d9a907b00697a3da2f7358060a10d4f17c`。source／test-merge／squash Git tree `bd83d90cf1d67d0d982cc9ff458c0eb63b029693` は一致。
- 固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。root・物理定義・既存定理文を変更していない。
- 統合後push [CI #43009561728](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43009561728) は本文起草時未認証。独立確認後に別途追記する。

## 2. 形式認証された内容
固定有限H、β>0。Sを元の正規化SU(2) Wilson one-slab、f₀を元の中心化signed ZW物理源、Qを **全top固定空間** への正規直交射影、BをAJAの真正正Haar負領域margin²証明書とする。すべて既存定義と同一。AJNの直交Pythagorasを元のHilbert源へ適用し、任意の自然数nについて

```
‖S^n f₀‖² = ‖Qf₀‖² + ‖S^n f₀ − Qf₀‖²
```

を**等式として**Lean4で確認（粗い三角不等式ではない）。この結果、各nにおいて

```
‖S^n f₀‖² < B
  ↔ ‖S^n f₀ − Qf₀‖² < B − ‖Qf₀‖²
```

が厳密に同値。n=2も同じ真の数量での文字通りの同値判定となる。AJIによりn=1の予算内証人は不可能であり、

```
(∃ n≥1, ‖S^n f₀‖²<B)
 ↔ (∃ n≥2, ‖S^n f₀−Qf₀‖²<B−‖Qf₀‖²)
```

も形式認証した。この構成は単に「実際の冪ノルム」の判定を解析的な全top＋減衰残余へ還元するものであり、特定のnの成立や非成立を証明しない。

## 3. 六つのLean宣言
- `realHilbert_fixedSubspace_power_sq_eq_top_add_exactTail_ajz`
- `realHilbert_fixedSubspace_power_lt_budget_iff_exactTail_ajz`
- `p4Q2PZ37AJZ_originalSource_power_sq_eq_fullTop_add_exactTail`
- `p4Q2PZ37AJZ_originalPower_AJA_iff_exactFullTopTail`
- `p4Q2PZ37AJZ_originalSecondPower_AJA_iff_exactFullTopTail`
- `p4Q2PZ37AJZ_originalAJA_existsPositivePower_iff_exists_n_ge_two_exactTail`

各宣言には個別の `#print axioms` 出力があり、実ログで標準3公理のみと確認。

## 4. 論理的障害と次の研究
AJYの `V−C₂<B` という**特定の十分条件の不可能性**と矛盾しない。AJYは上界が粗いことを残し、AJZは真の冪ノルムとその全top直交残余の正確な等式を提供する。しかし `B−‖Qf₀‖²` が正か、真の残余がその閾値を下回るかは **NO_DATA**。無条件AJA有限冪証人、真正n=2証人、top一次元性、H一様coercivity、Hamiltonian spectral gap、4D continuum Yang–Mills mass gapはいずれもOPEN。

次段AKAでは、式を繰り返すのではなく、元の物理Haar/Wilson積分による全top・直交冪残余の独立定量評価を探る。append-only／tighten-only／overwrite-forbidden／same-root。
