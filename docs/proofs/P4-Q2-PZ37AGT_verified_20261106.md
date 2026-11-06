# P4-Q2-PZ37AGT 正式証明記録（2026-11-06 JST）

著作権者：板倉英俊（Hidetoshi Itakura）。唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。mainは文書ミラー。

## 正本とexact-source検証

| 項目 | 確認結果 |
| --- | --- |
| 定理 | [PR #6397](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6397) MERGED |
| 最終source HEAD | `d4612311b7dd34b215e8584176cfa9e3841922fd` |
| canonical squash | `aa51b38715bac6c97f6c988778589c4937e4adc2` |
| test-merge checkout | `76f48d55a2904f6f81de76ab8425e5900f5487e7` |
| source/test-merge/squash共通Git tree | `0c4ed9efc088d7cb99f3c28ba535ce5585c249cd` |
| [exact-source CI #42208149754](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42208149754) | PR Lean Fast Check、completed/SUCCESS |
| Changed Lean job | `127859851431`、completed/SUCCESS |
| Run changed Lean fast check step | completed/SUCCESS |
| Lean依存閉包 | **11,355/11,355 SUCCESS** |
| 新規公理出力 | **AGT 5宣言**、すべて `propext`・`Classical.choice`・`Quot.sound` のみ |
| sorryAx | なし |
| 変更Lean warning/error | **0/0** |
| 独立completion receipt job | `127862689117`、completed/SUCCESS、source SHA一致 |
| 積み上げPR比較 | AGS・AGTの2ファイル、493追加行・削除0 |
| AGS統合後の正本への実追加 | AGT新規1ファイル、139追加行・削除0 |

AGTの実CI checkoutはAGS squash `f0a22c68d82dff012633396c6a4a188acf8519bc` と最終sourceのtest-merge。AGSからAGT squashへのcompareはAGT新規ファイルだけで、既存AGSは変更されていない。ログには依存AGSの10宣言も再掲されるが、AGT新規数は5件である。

固定Lean `leanprover/lean4:v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。Changed Lean依存閉包の成功を記録しており、別workflowのStrict LeanやGovernanceと読み替えない。

## CLOSED — 両チャート中心のType値有理座標

AGSの第一・対蹠チャートについて、元AGLの `rationalCoordinates` を構成した。このTypeは4個の有理数 `value` と、それらの実数castが元ADRの4実座標に等しいという `hValue` を保持する。ADSの球面roundtripとBool分岐から得る真正元行列の座標である。

## CLOSED — 任意正半径での真正有理空間格子の存在

固定有限体積Hの元空間リンク型をLink、その有限濃度をLとする。任意の正の有理数Rについて、一リンク半径を

`rho = (R:ℝ)/(L+1)`

と選ぶ。AGSの有限真正被覆を使い、AGHの元全リンク直積Borel格子を構成する。積弦距離半径は `L*rho≤R` であり、次元因子を省略していない。

主定理 `p4Q2PZ37AGT_exists_fineOriginalRationalSpatialGrid` の結論は正確に

`∃grid:AGH_originalSpatialGrid H, Nonempty (∀i e, AGL_rationalCoordinates (grid.center i e)) ∧ grid.radius≤(R:ℝ)`

である。外部有限被覆証拠、有理中心の存在仮定、外部radius証明を入力しない。各元中心のType値座標証拠は `Nonempty` に含めて保持する。

## CLOSED — 真のHaar質量と元transferへの存在・包含接続

後段の存在証明の内部では、上の格子と座標証拠、半径の証拠をAGQの `gridDataOfRationalCenters` へ渡す。AGQは格子のセル数Nが定まった後に `delta=eps/(2*(N+1))` として、真のproduct-Haarセル質量の有理上下界を構成し、総幅 `≤eps` を独立に証明済みである。

AGTの `fineOriginalTransferInterval` は、元右境界Bの各リンクにAGL有理座標証拠があり、Taylor次数nが正である場合、AGPのセル別評価をAGNの元大域区間と交差した `AFV_verifiedInterval (t_H(B))` を返す。元のsigned-transferそのものの包含保証と、既存区間を広げない交差構成は保持されている。任意の実境界について無条件に有理座標証拠が存在するとの主張ではない。

## 追加点検で特定した精度保持の境界

`p4Q2PZ37AGT_exists_fineOriginalGridData R eps hR heps` の**結論の型**は、R・epsによらない

`Nonempty (p4Q2PZ37AGP_gridData H)`

である。`fineOriginalGridData` はこの命題の証明に `Classical.choice` を適用している。Leanでは同じ命題の証明はproof irrelevanceにより同一視され、`Classical.choice : Nonempty α → α` は証明内部で構成した特定のwitnessを取り出す演算ではない。このため、**この選択値について要求Rの格子半径上界や要求epsの質量総幅上界を、現在の結論から射影することはできない**。

したがって、次を区別する。

- AGTの最初の定理で、指定R以内の真正有理格子の存在は証明済み。
- AGQでは、指定した元格子に対するeps以下の真の質量総幅は証明済み。
- AGTの選択後データから構成される区間は、元transferを含む。
- そのAGT選択値にR・epsの両制約が保持されるという定理、または最終transfer区間幅が任意に小さくなるという定理は、本AGTにはない。

これは証明済み包含の否定ではなく、定量的条件を結論の型に残す必要があるという問題である。次のAGUでは、元AGPデータと半径・各セル半径・総質量幅を一つの添字付きTypeに保持し、その強いTypeを選択する。AGTの既存定理・仮定は変更しない。

参照：[Lean公式・Propositions](https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/)（definitional proof irrelevance）、[Lean公式・Axioms](https://lean-lang.org/doc/reference/latest/Axioms/)（Classical.choice）。CIは上記固定Lean版で検証されている。

## Lean4全文修正の構造的理由

1. Boolによる対蹠分岐で、`change` だけでは必要な簡約・座標castが定義上同じ形にならなかった。false/trueを分け、それぞれ `simp` で元定義と対蹠座標を正規化した。
2. `rationalCoordinates` は命題ではなくTypeであるため、`∧` の命題位置に直接置けない。`Nonempty (∀i e, rationalCoordinates ...)` として型付き証拠の存在を命題に保持した。
3. 後段のType値構成には `Classical.choice hCenters` で座標証拠を用意する。この座標の選択先は特定gridの各元中心で添字付けされており、その座標等式を保持する。一方、上記の予算を添字に持たないgridDataの選択とは区別する。

失敗時のLean診断に出た `sorryAx` を完成証明として採用していない。最終sourceの全文再検証では新規5宣言は標準3公理のみ、sorryAxなし、変更warning/error0/0。数学的前提の弱化は行っていない。

## 公理出力対象

- `MGAP4D.MathlibAnalytic.p4Q2PZ37AGT_originalSignedCenter_rational`
- `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGT_exists_fineOriginalRationalSpatialGrid`
- `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGT_exists_fineOriginalGridData`
- `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGT_fineOriginalGridData`
- `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGT_fineOriginalTransferInterval`

## OPEN

要求予算を選択後も保持する型付きデータ、最終signed-transfer区間幅の任意精度評価、具体的大体積Haar質量表の計算、元transferの実際の非零符号認証、二閾値殻、H一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは、それぞれ別の証明・計算課題である。

元SU(2)・Wilson作用・固定結合・真のHaar・Perron・source・kernel・signed transfer・公開root・workflowは不変更。古典的存在証明を、具体的数値計算済みと解釈しない。

ソース：[AGT Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/aa51b38715bac6c97f6c988778589c4937e4adc2/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalUnconditionalFineHaarGridV5_PZ37AGT.lean)。
