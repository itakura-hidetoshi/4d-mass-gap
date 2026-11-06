# P4-Q2-PZ37AGR 正式証明記録（2026-11-06 JST）

著作権者：板倉英俊（Hidetoshi Itakura）。唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。mainは本文のみの文書ミラー。

## 正本・exact-source検証

| 項目 | 確認結果 |
| --- | --- |
| 定理 | [PR #6393](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6393) MERGED |
| 最終source HEAD | `cfa566afc4986cc382e8fb233e83ffe7fa046118` |
| canonical squash | `59994f8cf41f3eddf572be118abb53e710185c13` |
| test-merge | `0a047aad9a09b6ff9664a13c3bd2cb735e094232` |
| source/test-merge/squash Git tree | `60bafc43ac3771e902743ac0cea52c8426625966`（同一） |
| [exact-source CI](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42190751075) | PR Lean Fast Check、completed/SUCCESS |
| Changed Lean job | `127801875141`、completed/SUCCESS |
| Lean依存閉包 | **11,353/11,353 SUCCESS** |
| 公理監査 | 新規7宣言は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx`なし |
| 変更Lean warning/error | **0/0** |
| 差分 | 新規Lean4葉1ファイル、既存Lean・workflow・root・pin変更なし |

固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。元の`Matrix.specialUnitaryGroup (Fin 2) ℂ`、Wilson作用、固定結合、真のHaar、source、kernel、Perron、signed transferは不変更。

## CLOSED — 真正SU(2)の有理中心の構成

任意の有理3パラメータ `t=(a,b,c)` に対し `s=a²+b²+c²`、`D=1+s>0` と置く。真正4実座標

`q(t)=((1-s)/D,2a/D,2b/D,2c/D)`

は全成分が有理数で、`∑ q_j(t)^2=1` を環恒等式と非零分母からLean4で証明した。従って `q(t)` は元ADR/ADSが用いる実単位3球面 `S³` の正真正銘の点である。

既証明のADS球面→元SU(2)逆写像 `Ψ` へ適用した `g(t)=Ψ(q(t))` は元の真正SU(2)行列であり、ADSの両側逆証明から元AGL `rationalCoordinates(g(t))` 証拠を構成。元Wilson plaquette energyは`1-q(t)_0`と幅0の有理値で証明された。代理測度・別のquaternion群は導入していない。

## CLOSED（条件付きdescent）— AGH・AGQ・AGPへ接続

有限パラメータ列`parameters:Fin n→(Fin 3→ℚ)`、正の半径`r`に対し、真正元SU(2)で

`∀g:G, ∃i:Fin n, g∈trueChordalBall (g(parameters i)) r`

という**明示的な有限被覆証拠が入力された場合**、元AGHの全リンク直積Borel格子を構成する。各元空間リンクについて元の有理中心証明を保持し、認証有理半径`R`は`(card Link)*r≤R`を満たす。

これにAGQの真のHaarセル質量総幅`≤eps`（`eps>0`、セル数が決まってから誤差配分）を結合し、`p4Q2PZ37AGR_originalGridDataOfRationalCover` が真正 `p4Q2PZ37AGP_gridData H` を構成する。

さらに`p4Q2PZ37AGR_originalTransferIntervalOfRationalCover` は元AGNの大域signed-transfer区間をAGPのセル別局所評価と`tighten-only`で交差させ、**同じ真正物理signed transfer**の証明済み区間を返す。入力された有限被覆の存在が「無条件に証明された」とは主張していない。

## Lean4全文修正理由

初回source `8aa244a469979b5e718f385ef495647f31bf85d0` のCI #42189336922は、数式の誤りではなく`EuclideanSpace.real_norm_sq_eq`適用後の`WithLp.toLp`の内部表現 `v.ofLp` と有理成分の実数castの型変換順序が一致せず失敗した。型変換を先に実数平方和として`exact_mod_cast`し、その後`simpa [v]`で`WithLp`を展開する修正を行った。修正source `917e2409bd47af02458003ef9bf15691d98f4a7c` はCI #42190081011 SUCCESS。初回のLean診断に含まれた`sorryAx`は、完成証明として採用せず、再検証で消失した。

その後、AGH・AGQ・AGPの条件付き物理的descentを追加した最終source `cfa566af...`を同じpinで再検証。新規7宣言の公理依存は標準3公理のみ。

## OPEN — 次段の局所障害を明示

**稠密性**：任意の元SU(2)点と半径に対して、有理ステレオ投影中心を任意に近接させられることは本AGRでは未証明。単一ステレオ投影チャートは反対極を除くので、もう一つのチャート、または反対極の有理点を分岐で扱い、`Rat.denseRange_cast`、有限Piの稠密性、連続性、ADS/ADT真の等距離を接続する必要がある。

**有限被覆**：稠密性とコンパクト性から任意半径の有限有理中心被覆を抽出し、上記の条件付き`hCover`を消去する証明が次段。本証明の`hCover`は消去されていない。

さらに真正Haarセルの具体的大体積有理数値表の計算、元signed-transferの非零符号認証、二閾値殻、H一様coercivity、Hamiltonian gap、連続体4D Yang–Mills質量ギャップはそれぞれ別の未解決問題。AGQのHaar質量包囲は古典的存在選択で、数値計算済みとの主張ではない。

ソース：[AGR Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/59994f8cf41f3eddf572be118abb53e710185c13/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalRationalStereographicCentersV5_PZ37AGR.lean)。
