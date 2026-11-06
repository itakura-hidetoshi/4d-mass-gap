# P4-Q2-PZ37AGW 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。唯一の定理正本は formal/real-hilbert-uniform-coercive-strong-limit、mainは文書ミラー。

## Exact-source検証

| 項目 | 結果 |
| --- | --- |
| 定理PR | [#6406](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6406) MERGED |
| 最終source HEAD | 47ffd257eebb0d44375ed5cda8798fee2d20fa88 |
| test-merge | 5811fa6e79aa028c6e7eda090cca1de26bc6c011 |
| 正本squash | 6a07147176ea85b51791ff8b38737e14db5ce28d |
| 共通source/test-merge/squash Git tree | e717d546cbbe8095c0da7b40a565d3f56b48fc37 |
| [exact-source CI #42274305910](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42274305910) | workflow completed/SUCCESS |
| Changed Lean job | 128086554113 completed/SUCCESS |
| Lean依存閉包 | **11,358／11,358 SUCCESS** |
| 新規公理出力 | **4宣言、propext・Classical.choice・Quot.sound のみ** |
| sorryAx／変更Lean warning/error | **なし／0/0** |
| completion receipt job | 128089072987 completed/SUCCESS |
| 差分 | 新規Lean1ファイル・150追加行・削除0 |

Lean v4.30.0-rc2／mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6。既存Lean、元SU(2)／Wilson作用／Haar／Perron／source／kernel／transfer、公開root、pins、workflowは変更なし。本結果はChanged Lean依存閉包であり、別workflowのStrict Lean／Governance検証を実施したと読み替えない。

## CLOSED — 任意の符号の元sourceによるmin/max幅恒等式

任意有理sとlo≤hiについて、次の**厳密な等式**をLeanで証明した。

`max(s*lo,s*hi) - min(s*lo,s*hi) = |s|*(hi-lo)`

s≥0とs≤0を場合分けする。負のsourceを正と置き換えず、元AGIとAGNのmin/maxに従う。

## CLOSED — 元AGN中心値区間の正確な誤差分解

元AGNの中心化source有理値s、元AGMの真正クリップ済kernel区間[klo,khi]、元AGNの真正global floor区間[flo,fhi]を同じH,A,B,m,nで使う。元の中心値区間は

`lo=min(s*(klo-(1+fhi)/2), s*(khi-(1+flo)/2))`

`hi=max(s*(klo-(1+fhi)/2), s*(khi-(1+flo)/2))`

である。これを**変更せず**、次の等式を証明した。

[
oxed{\mathrm{width}(I^{\rm center}_{H,A,B,m,n})
= |s_H(A)|\left[
(k_{\rm hi}-k_{\rm lo})+\frac{f_{\rm hi}-f_{\rm lo}}2
\right]}
]

元kernel区間・floor区間はいずれも真の元物理値の上下界を保持するため、各区間の順序が証明されている。追加で元AGN中心値区間幅の非負性もLeanで証明済み。4公理出力は標準公理のみ。

定理 `p4Q2PZ37AGW_originalCenterWidth_exact` は**本物の元AGN中心区間定義に対する等式**。任意に用意した合成表や代理measureに対する結果ではない。

## AGVとの接続と未解決の精度

AGVの `width(I_H) ≤ eta+2L_H(m)R+2M_H(m,n)eps` は、全セル中心値区間の幅≤etaを条件とする。AGWにより、この条件の中身は元sourceの有理値絶対値と元clipped kernel幅／元floor幅に還元できることが確定した。

**しかし、AGWだけでは各幅が任意に小さくなるとは言えない。** AGKの固定結合区間幅の収束は証明済みだが、AGJの指数Taylor、AGMの原kernel、AGNのfloorまで含む一様収束、および格子の全中心に対するetaの任意精度保証は次段以降の課題。実際の元signed-transfer非零符号・二閾値殻・H一様coercivity・Hamiltonian spectral gap・連続体4D Yang–Mills mass gap・具体的大体積計算はいずれも未解決である。

次の作業：元AGN/AGM/AGJ/AGKの評価区間幅を個別に上界化し、有限中心全体で一様化してAGVのeta条件を導く。仮定を新設して証明を弱めない。

[AGW Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/6a07147176ea85b51791ff8b38737e14db5ce28d/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCenterWidthFactorizationV5_PZ37AGW.lean)。
