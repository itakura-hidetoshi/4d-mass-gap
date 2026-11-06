# P4-Q2-PZ37AGV 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。唯一の定理正本は formal/real-hilbert-uniform-coercive-strong-limit、main は文書ミラー。

## Exact-source検証

| 検証項目 | 確認値 |
| --- | --- |
| 定理PR | [#6403](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6403) MERGED |
| 最終source HEAD | e0ea55e955ef1fd8ab36b65eaa9a7732e3e8b402 |
| test-merge SHA | 99742c4306d8c713be8d2f8ff6aa3e2f3cfdf600 |
| 正本squash | 13cdf5032b66a2170591037de91aab730a4e9a7b |
| source/test-merge/squash共通Git tree | 379ec0b8adc160388cbeabe234aad9ffe4c60474 |
| [exact-source CI #42271966524](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42271966524) | workflow completed/SUCCESS |
| Changed Lean job | 128078526978 completed/SUCCESS |
| Lean依存閉包 | **11,357 / 11,357 SUCCESS** |
| 新規定理公理出力 | **10宣言、標準公理 propext・Classical.choice・Quot.sound のみ** |
| sorryAx／変更Lean warning/error | **なし／0/0** |
| 独立completion receipt job | 128081411670 completed/SUCCESS、source HEAD一致 |
| 差分 | Lean新規1ファイル450追加行、削除0 |

Lean v4.30.0-rc2、mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6 固定。既存Lean、元物理model、公開root、workflowとpinは変更しない。本検証はChanged Lean依存閉包であり、別workflowのStrict LeanまたはGovernance実行を意味しない。

## CLOSED — 符号付きHaar質量のセル幅不等式

AGIの真のsigned min/max評価器を変更していない。各セルの真正Haar質量を p_i、独立した有理下限・上限を ml_i,mu_i とする。ml_i≤p_i≤mu_i、-M≤a_i,b_i≤M ならば

`max(b_i ml_i,b_i mu_i)-min(a_i ml_i,a_i mu_i) ≤ (b_i-a_i)p_i+2M(mu_i-ml_i)`

を形式証明した。有理質量下限を非負と仮定しない。

元の測度のセル真値は p_i≥0、Σp_i=1。b_i-a_i≤A、Σ(mu_i-ml_i)≤eps を用い、元AGI有限表について

`table.upper-table.lower≤A+2M eps`

を証明した。有理区間端点の和を1と置き換えていない。真正Haar質量正規化は既存AGN massIntervals.total_massを使用。

## CLOSED — 元AGPのセル評価とAGUの真正精度データへの接続

L_H(m)=6+13*AGK_upper(m)*(AGN_countRational(H)/2) を定義。元AGPの全合理中心に対するsource-adapted slopeにより cellBudget_i≤L_H(m)R を証明。元AGNの transferRadius(H,m,n)=M_H(m,n) は、既存AGOの元continuum integrand絶対値境界から非負性を得た。

元AGPではセル下端=max(-M_H,center.lower-cellBudget)、上端=min(M_H,center.upper+cellBudget) を使用する。したがって切り詰め後の両端は [-M_H,M_H] に残る。**各セルの元AGN中心値区間幅がeta以下という明示的条件**のもと、セル幅≤eta+2L_H(m)R。AGUで選択された同じ真正格子のHaar質量総幅≤eps、そして真のHaar質量の総和=1から、元AGP raw signed-transfer区間について

`raw.upper-raw.lower≤eta+2L_H(m)R+2M_H(m,n)eps`

を形式証明。真の元signed-transferの評価器・測度・source・kernelはいずれも保持。

## CLOSED — AGUの最終signed-transfer区間へのtighten-only降下

AGU fineOriginalTransferIntervalは、その同じ型付き選択データを元AGP評価器に渡し、AGN大域区間と交差する。交差区間の下端はrawより小さくならず、上端はrawより大きくならない。したがって同一の元transferを含む最終区間 I_H について

[
\boxed{\mathrm{width}(I_H)\le\eta+2L_H(m)R+2M_H(m,n)\varepsilon}
]

が形式証明済み。入力は任意有限H、正有理R,eps、元右境界Bにおける各リンクのAGL有理座標、m,nとn>0、eta≥0、全中心におけるAGN区間幅≤eta。これは無条件の精度収束定理ではない。

## Lean4エラーの構造

全文と依存シグネチャを照合し、二度の失敗に対して次を修正した。
1. 加法不等式 A+x と x+A の型の向きの差。正しい目標へ linarith で移行。
2. 関数引数内の by/constructor 箇条書きが構文解析に干渉したため、実数への上下界castを独立した証拠へ分離。
3. exact_mod_cast は関数適用やFinset.sum内側の有理castを単独では正規化できないため、式全体のcast証明を作り、push_castで和と差を標準形へ正規化。

最終sourceは10宣言とも標準公理のみ、sorryAxなし、変更ファイルwarning/error0/0。

## OPEN — 中心値幅の任意精度保証

etaはまだ条件である。AGKの固定結合精度の収束だけでは、AGMの指数Taylor、kernel、AGN floorと各中心値幅の全体収束は直ちに得られない。次段AGWでこれらの元の項を追い、中心値幅の条件を独立に導く。その後、選択可能なR,epsと組み合わせて最終区間幅の任意精度化を検討する。

具体的大体積Haar質量表の数値計算、真正非零transfer符号、二閾値殻、H一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは未解決。syntheticな数値を物理的符号認証として扱わない。

[AGVのLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/13cdf5032b66a2170591037de91aab730a4e9a7b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSignedHaarWidthV5_PZ37AGV.lean)。
