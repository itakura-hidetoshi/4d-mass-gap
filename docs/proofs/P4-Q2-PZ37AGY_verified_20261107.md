# P4-Q2-PZ37AGY 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。Lean定理の唯一の正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。

## Exact-source証明・Git正本

| 項目 | 確定状態 |
| --- | --- |
| 定理PR | [#6412](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6412) **MERGED** |
| 最終検証source HEAD | `e0d8f129cb9f8a54dcc75588aa8840824ef5dc5f` |
| test-merge SHA | `6498ad142076c0849d63d97c8d1edc0a9a827d9c` |
| 定理squash SHA | `27a1db24f49c351b8c5025308d6b45cad3c19539` |
| source/test-merge/squash共通Git tree | `14987534a1dcc35c440380f5607e24e23468d8e8` |
| [exact-source CI #42300462050](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42300462050) | workflow completed/SUCCESS |
| Changed Lean job `128176581286` | completed/SUCCESS |
| Lean依存閉包 | **11,360 / 11,360 SUCCESS** |
| 新規宣言公理出力 | **9宣言：`propext`・`Classical.choice`・`Quot.sound` のみ** |
| sorryAx / 変更Lean warning・error | **なし / 0・0** |
| 独立completion receipt job `128179469373` | completed/SUCCESS |
| 差分 | 新規Lean1件・219追加行・削除0 |

固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。変更されたのは新規Lean葉のみ。既存Lean・元物理定義・公開root・pin・workflowは不変更。検証はChanged Lean依存閉包であり、別workflowのStrict LeanやGovernance実行を主張しない。

## CLOSED — genuine kernel最大幅・floor幅の独立定義

AGNの**実際の元物理global floor**の有理認証区間幅を

`DeltaF(H,m,n)=AGN_originalFloorInterval.upper-AGN_originalFloorInterval.lower`

と定義し、真のfloor値が区間内にある既証明から `0≤DeltaF` を得た。

AGUで選択済みの**同じ元AGH Borel空間格子**の各中心 `C_i` と、元右境界 `B` について、元AGMの真正clipped Wilson kernel認証区間幅 `DeltaK_i` を定義し、区間の包含から `0≤DeltaK_i` を証明した。元AGXで証明済みの格子添字非空性を継承し、

`DeltaKmax(H,d,B,m,n)=max_i DeltaK_i`

を `Finset.sup'` で定義。各 `DeltaK_i≤DeltaKmax` および `DeltaKmax≥0` を証明した。格子中心は古典選択される可能性があり、実数値表を計算したとは主張しない。

## CLOSED — 既証明の原Wilson中心化source上界

AGNの元centered continuous sourceについて `|f_H(C)|≤p_H/2` が既に成り立ち、各有理中心では元AGNの合理sourceは**正確にその実数値と等しい**。これを有理数へcastして

`|s_H(C_i)|≤AGN_countRational(H)/2`

とその上界の非負性をLean4で証明した。sourceや中心化係数に新たな仮定・近似を加えていない。

## CLOSED — AGX最大中心誤差の物理成分による上界

AGWの厳密式

`centerWidth_i=|s_H(C_i)|*(DeltaK_i+DeltaF/2)`

を符号付きのまま使用する。各幅の非負性と `DeltaK_i≤DeltaKmax` から

[
\boxed{
\eta_H^{\max}
\le \frac{p_H}{2}
\left(\Delta K_{\max}+\frac{\Delta F}{2}\right)
}
]

を証明。`Finset.sup'_le` の真正有限最大値を用い、セル数を乗じる粗い誤差評価へ戻らない。

AGXの元物理signed-transfer最終区間とAGVのtighten-only性を一切変更せず、任意H・正有理R,eps・元AGL有理座標の右境界B・m,nかつn>0について

[
\boxed{
\operatorname{width}(I_H)
\le
\frac{p_H}{2}
\left(\Delta K_{\max}+\frac{\Delta F}{2}\right)
+2L_H(m)R+2M_H(m,n)\varepsilon
}
]

をLean4で形式証明した。元Haar、元centered source、元kernel、元floor、元transferはいずれも同じ物理オブジェクト。

## Lean4全文修正の理由

初回のLean stepは `add_le_add_right hkMax _` が `fl/2+k≤fl/2+kMax` という型の項順で出力され、期待する `k+fl/2≤kMax+fl/2` に定義上一致しない1箇所の型エラー。新規Lean全文・依存シグネチャ・固定mathlib APIを照合し、正しい項順の `hAdd` を `linarith` で構成、係数の非負性を使う `mul_le_mul_of_nonneg_left` へ渡した。仮定・結論・物理定義は変更せず、最終exact-source CIで全宣言の公理依存を検証した。

## OPEN — kernel/floorの精度収束と真正非零符号

AGYは**実際の** `DeltaKmax` と `DeltaF` に分解した上界である。両者が任意に小さくなることはまだ証明していない。次段AGZ以降で、AGKの真正固定結合区間幅、AGJのTaylor指数残差、AGMの元clipped kernel、AGNのglobal floorの定量幅・全中心での一様精度を接続する。非計算的格子の具体的大体積Haar表、元signed-transfer非零符号、二閾値殻、H一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills mass gapはいずれも未解決。

[AGY Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/27a1db24f49c351b8c5025308d6b45cad3c19539/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalKernelFloorMaxWidthV5_PZ37AGY.lean)。
