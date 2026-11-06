# P4-Q2-PZ37AGU 正式証明記録（2026-11-06 JST）

著作権者：板倉英俊（Hidetoshi Itakura）。唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。mainは文書ミラー。

## 正本とexact-source検証

| 項目 | 確認結果 |
| --- | --- |
| 定理 | [PR #6400](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6400) MERGED |
| 最終source HEAD | `606724cc3a5bbc76f4fcebfbf6ebd91f07e5e3da` |
| canonical squash | `b45fb266700b6398cbd34e915806f846e5a3ea5d` |
| test-merge checkout | `129b6c5cfe5d43c195720b2d7c6dde3ebec2ba84` |
| source/test-merge/squash共通Git tree | `102a23582d4fce24fa3feb492c74fce650eace4c` |
| [exact-source CI #42210989555](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42210989555) | PR Lean Fast Check、completed/SUCCESS |
| Changed Lean job | `127869281882`、completed/SUCCESS |
| Run changed Lean fast check step | completed/SUCCESS |
| Lean依存閉包 | **11356/11356 SUCCESS** |
| 新規公理出力 | **14宣言**、標準公理のみ |
| sorryAx | なし |
| 変更Lean warning/error | **0/0** |
| 独立completion receipt job | `127871205474`、completed/SUCCESS、source SHA一致 |
| 差分 | 新規Lean葉1ファイル・225追加行・削除0 |

固定Lean `leanprover/lean4:v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。全文とimports・依存シグネチャの二重レビュー後、上記固定環境の実CIで検証。旧依存のwarningと変更AGUのwarningを区別し、別workflowのStrict LeanやGovernanceとは読み替えない。

## 問題 — 非添字の存在型からの選択で予算が消える

AGTの `exists_fineOriginalRationalSpatialGrid H R hR` は、指定R以内の真正有理格子を存在量化する正しい定理である。一方、その後段の `exists_fineOriginalGridData` は結論を `Nonempty (AGP_gridData H)` にしており、R・epsへの制約を型に残していなかった。

今回の `p4Q2PZ37AGU_unindexedChoice_budget_independent` は、任意の正予算R,eps,S,etaについて

`AGT_fineOriginalGridData H R eps hR heps = AGT_fineOriginalGridData H S eta hS heta`

を `rfl` で形式証明した。同じ `Nonempty` 命題の証明はLeanのproof irrelevanceで同一視される。旧選択値の真正AGPデータとしての健全性、旧signed-transfer区間の包含保証は有効なままである。問題は、要求予算に従うデータを選ぶ仕様が結論の型にないことだった。

参照：[Lean公式・Propositions](https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/)と[Lean公式・Axioms](https://lean-lang.org/doc/reference/latest/Axioms/)。同一視されるのは命題の証明であり、異なるデータwitness一般が等しくなるという主張ではない。

## CLOSED — 実データと三つの要求精度を保持するType

新しい構造体の仕様は次のとおり。

```lean
structure p4Q2PZ37AGU_precisionGridData (H : ℕ) (R eps : ℚ) where
  data : p4Q2PZ37AGP_gridData H
  hGridRadius : data.grid.radius ≤ (R : ℝ)
  hCellRadius : ∀ i : Fin data.grid.n, data.radii.radius i = R
  hTotalMassWidth :
    (∑ i : Fin data.grid.n,
      (data.masses.upper i - data.masses.lower i)) ≤ eps
```

`data` は元AGPと同じ真正格子・各元リンクのAGL有理座標・セル幾何証明・真のproduct-Haar質量包含を持つ。精度条件を別の無関係な格子へ適用していない。

`hCellRadius` は各セルに設定した**認証有理半径**がRであるという等式。セル集合の最小包絡半径がちょうどRである、または実測距離がRに達するという主張ではない。

## CLOSED — 格子後置の質量予算と選択後の射影

明示的構成子 `precisionDataOfRationalGrid` は、供給された真正格子・座標証拠・半径上界をAGQへ渡す。元の格子とAGQの質量区間オブジェクトを厳密に保持する等式をそれぞれ `rfl` で証明し、`AGQ_totalMassWidth_le` を同じデータのfieldに格納する。

存在定理は

`∀H, ∀R eps:ℚ, 0<R → 0<eps → Nonempty (AGU_precisionGridData H R eps)`

を証明。まずAGTから指定Rの格子を取得し、その格子のセル数が定まった後にAGQの質量予算を付ける。選択関数 `AGU_fineOriginalGridData` は、この**R・epsを添字に持つType**を `Classical.choice` で選ぶ。選択された同じ `data` について、格子半径上界、各セル認証半径の等式、真の質量区間総幅上界の三定理を射影する。

古典選択は存在証明内部の特定witnessの構成履歴をそのまま取り出す演算ではない。明示的構成子の厳密保存定理と、選択packageのfieldによる精度保証を区別する。後者でも必要な真の物理量との関係・予算は型に保持される。

## CLOSED — 同じ選択データの元signed-transfer区間とtighten-only性

`AGU_originalTightenedInterval` は添字付きpackageの `.data` を元AGP評価器に渡す。任意の以前の `AFV_verifiedInterval (t_H(B))` と交差し、

`previous.lower ≤ new.lower`、`new.upper ≤ previous.upper`

を証明する。対象の元transfer値は同一である。

`AGU_fineOriginalTransferInterval` は上の選択packageと元AGNの大域区間を使用。`fineOriginalTransferInterval_eq_sameData` は、区間評価に使うAGPデータが三つの精度条件を持つ**その選択値のdataそのもの**であることを厳密等式で明記する。`fineOriginalTransferInterval_subset_global` で元大域区間を広げないことも証明した。

境界Bの各元リンクに対するAGL有理座標証拠、m,n∈ℕとn>0は既存APIどおり入力として残る。精度付き格子の存在に外部被覆証拠・Haar数値oracleを新設していない。

## 新規公理出力対象14宣言

namespaceはすべて `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`。

- `p4Q2PZ37AGU_unindexedChoice_budget_independent`
- `p4Q2PZ37AGU_precisionDataOfRationalGrid`
- `p4Q2PZ37AGU_precisionDataOfRationalGrid_grid_eq`
- `p4Q2PZ37AGU_precisionDataOfRationalGrid_masses_eq`
- `p4Q2PZ37AGU_exists_precisionGridData`
- `p4Q2PZ37AGU_fineOriginalGridData`
- `p4Q2PZ37AGU_fineOriginalGridData_radius_le`
- `p4Q2PZ37AGU_fineOriginalGridData_cellRadius_eq`
- `p4Q2PZ37AGU_fineOriginalGridData_totalMassWidth_le`
- `p4Q2PZ37AGU_originalTightenedInterval`
- `p4Q2PZ37AGU_originalTightenedInterval_subset`
- `p4Q2PZ37AGU_fineOriginalTransferInterval`
- `p4Q2PZ37AGU_fineOriginalTransferInterval_eq_sameData`
- `p4Q2PZ37AGU_fineOriginalTransferInterval_subset_global`

## OPEN — 最終区間幅と物理的符号

R・epsは幾何と真のHaar質量区間の予算であり、それ自体が最終transfer区間の幅ではない。次段は同じ格子のセル幾何変動、中心値の有理指数核区間幅、セル数を含む質量幅を統合し、最終signed区間幅の明示上界を証明する。その上で、必要なパラメータの精密化と各誤差の制御を行う。

具体的大体積Haar質量表の実計算、最終区間の任意精度収束、元signed-transferの実際の非零符号、二閾値殻、H一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは未解決。本構成は古典的存在証明であり、実行可能な数表列挙を得たとの主張ではない。

元SU(2)・Wilson作用・固定結合・Haar/Perron・中心化source・kernel・transfer・公開root・既存Lean・workflow・固定環境は不変更。新規葉を追加して、既存の仮定を弱めず定量仕様を強めた。

ソース：[AGU Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b45fb266700b6398cbd34e915806f846e5a3ea5d/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPrecisionCarryingFineGridV5_PZ37AGU.lean)。
