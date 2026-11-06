# P4-Q2-PZ37AGS 正式証明記録（2026-11-06 JST）

著作権者：板倉英俊（Hidetoshi Itakura）。唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。mainは文書ミラー。

## 正本とexact-source検証

| 項目 | 確認結果 |
| --- | --- |
| 定理 | [PR #6396](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6396) MERGED |
| 最終source HEAD | `967da4ed5d8c246a8785199953d0c5509ec93521` |
| canonical squash | `f0a22c68d82dff012633396c6a4a188acf8519bc` |
| test-merge checkout | `2b383f9349fb2d0b173719994904db90f9f33ffa` |
| source/test-merge/squash共通Git tree | `cbe03abc4c0d58354eae9c7cc7695d4d8b421028` |
| [exact-source CI #42196369171](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42196369171) | PR Lean Fast Check、completed/SUCCESS |
| Changed Lean job | `127820491657`、completed/SUCCESS |
| Run changed Lean fast check step | completed/SUCCESS |
| Lean依存閉包 | **11,354/11,354 SUCCESS** |
| 新規公理出力 | **10宣言**、すべて `propext`・`Classical.choice`・`Quot.sound` のみ |
| sorryAx | なし |
| 変更Lean warning/error | **0/0** |
| 独立completion receipt job | `127822723267`、completed/SUCCESS、source SHA一致 |
| 差分 | 新規Lean葉1ファイル・354追加行・削除0 |

固定Lean `leanprover/lean4:v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。上記はChanged Lean依存閉包の検証結果であり、別workflowのStrict LeanやGovernanceの結果を追加したものではない。既存依存のwarningと変更AGSのwarningは区別する。receiptは完了通知であり、workflow・job・Lean step・実ログを併せて確認した。

## CLOSED — 元ステレオ投影の連続性と逆写像

AGRの有理式を実パラメータ `u=(a,b,c)` に延長し、`s=a²+b²+c²` に対し

`q(u)=((1-s)/(1+s),2a/(1+s),2b/(1+s),2c/(1+s))`

を元の `EuclideanSpace ℝ (Fin 4)` に構成した。分母は常に正で、全3変数について連続。有理パラメータの実数castを通すと元AGRの球面点と厳密一致する。

真正単位球面点 `x=(a,b,c,d)` で `a≠-1` なら、`u=(b/(1+a),c/(1+a),d/(1+a))` を代入して `q(u)=x` を証明した。平方和1、分母非零、環恒等式から得る元座標の厳密等式である。

## CLOSED — 有理稠密性と第二チャート

固定mathlibの `Rat.denseRange_cast` と `DenseRange.piMap` から有理3変数が実3変数空間に稠密であることを示した。連続逆投影の球の逆像が非空開集合となることを用い、除外極以外の任意球面点に、任意の正の距離以内で有理球面点が存在する。

元球面内の対蹠写像 `x↦-x` の対合性と距離保存を証明。第一チャートで除外される極では対蹠側のチャートを用いる。これにより

`∀x:S³, ∀r>0, ∃b:Bool, ∃t:Fin 3→ℚ, dist x (signedRationalSphere b t)<r`

が成立する。元球面を別の代理空間へ置き換えていない。

## CLOSED — 外部hCoverを要しない有限真正有理被覆

ADR/ADSの元SU(2)・球面の両側逆対応と、ADTの真正弦距離＝球面距離を用い、全有理チャート中心の真正弦距離開球が元SU(2)を覆うことを証明した。元SU(2)のコンパクト性から有限部分被覆を抽出し、`Finset.equivFin` で有限添字へ整理した。

主定理 `p4Q2PZ37AGS_exists_originalFiniteRationalCover` は

`∀r:ℝ, 0<r → ∃n:ℕ, ∃parameters:Fin n→Bool×(Fin 3→ℚ), ∀g:G, ∃i:Fin n, g∈trueChordalBall(center(parameters i),r)`

を証明する。AGRで条件だった有限被覆 `hCover` は、この存在定理では外部入力ではない。中心は元の `Matrix.specialUnitaryGroup (Fin 2) ℂ` の実際の行列値である。

## 公理出力対象

namespaceは `MGAP4D.MathlibAnalytic`。

- `p4Q2PZ37AGS_rationalVector_exact`
- `p4Q2PZ37AGS_realStereographicVector_continuous`
- `p4Q2PZ37AGS_chartAlgebra`
- `p4Q2PZ37AGS_chart_surjective_offPole`
- `p4Q2PZ37AGS_rationalParameters_dense`
- `p4Q2PZ37AGS_rationalSphere_approaches_offPole`
- `p4Q2PZ37AGS_antipode_involutive`
- `p4Q2PZ37AGS_antipode_dist`
- `p4Q2PZ37AGS_signedRationalSphere_approaches`
- `p4Q2PZ37AGS_exists_originalFiniteRationalCover`

## 境界と次の接続

有限部分被覆の選択は古典的存在証明であり、具体的中心列の高速列挙・最小中心数・大体積数値表の実行を主張しない。ファイル冒頭の初期説明には有限被覆が後続課題である表現が残るが、同ファイル末尾の最終主定理で有限被覆まで検証済み。既存ソースは変更せず、本記録は最終定理本文に従う。

全元空間リンクへの直積とBorel格子・有理座標証拠の接続は[AGT記録](P4-Q2-PZ37AGT_verified_20261106.md)を参照。元Wilson作用・固定結合・Haar・source・kernel・Perron・signed-transferは不変更。非零transfer符号、二閾値殻、H一様coercivity、Hamiltonian gap、連続体Yang–Mills質量ギャップは未証明。

ソース：[AGS Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/f0a22c68d82dff012633396c6a4a188acf8519bc/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalRationalDensityV5_PZ37AGS.lean)。
