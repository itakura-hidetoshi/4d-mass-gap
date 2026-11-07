# P4-Q2-PZ37AHP — 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。GitHub `main` は文書ミラー。原則 append-only／tighten-only／overwrite-forbidden／same-root。

## 正本とexact-source実検証

| 項目 | 確認結果 |
| --- | --- |
| [AHP定理PR #6463](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6463) | **MERGED** |
| 継承元AHO正本HEAD | `dba01b40e42526186ca9fd126930616fc8903e4f` |
| 最終source HEAD | `2a49d6369043576cdacba5fb693329eac462dc2c` |
| test-merge SHA | `3eddd1240ee62a58c0174f4a8d45b1e7c765e382` |
| 定理squash／正本HEAD | `1f89ba949d3a7bafcd9d945ae57ddb73724b19bf` |
| source／test-merge／squash Git tree | `5341c78e848023b6b6c7e206f5468702fc0e8666`（完全一致） |
| [最終exact-source CI #42372491180](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42372491180) | **completed / SUCCESS** |
| Changed Lean job | `128403304486` — completed / SUCCESS |
| 独立completion receipt | `128404516597` — completed / SUCCESS |
| Lean依存閉包 | **11,377 / 11,377 SUCCESS** |
| 新規 #print axioms | **19定理**、`propext`／`Classical.choice`／`Quot.sound` のみ |
| `sorryAx` | 0 |
| 変更AHP Lean warning/error | **0 / 0** |
| 最終Leanログ | GitHub artifact `13574362849` (`lean-fast.log`) |
| ファイル変更 | 新規AHP Lean 1ファイルのみ。既存Lean／物理定義／root／workflow／pins／README／ROADMAP不変更 |

固定環境：Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。GitHub MCP経由で最終実ログを回収し、`Build completed successfully (11377 jobs).`、新規19定理の全公理監査、変更Lean warning/error 0/0、`sorryAx` 0を確認した。既存依存先に残存するlinter warningは今回の変更Lean warningに数えない。

## CLOSED — 元SU(2)完全Wilson核の一次項の厳密分離

元の固定空間法則 `muH`、元のGauss-law物理source `f0` および真正連続代表 `fCont=(W-pH)/2` を変更しない。元の両端空間halfweightと時間crossing作用を保持して

\[
S_H(A,B)=\tfrac12 W_H(A)+S_H^{\rm cross}(A,B)+\tfrac12 W_H(B),\quad
K_{H,\beta}(A,B)=\exp(-\beta S_H(A,B))
\]

と置く。元AGNによる厳密Haar平均 \(\int W_H\,d\mu_H=p_H\) から \(\int f_H\,d\mu_H=0\) を導出。元物理L²代表との既証明AFZ a.e.一致によって、全 \(\beta\) の元transferが真のHaar積分に一致することを再証明し、\(T_{H,0}(B)=0\) を得た。

元source二次モーメント \(V_H=\int f_H(A)^2\,d\mu_H(A)\)、真正crossing相関 \(X_H(B)=\int f_H(A)S_H^{\rm cross}(A,B)\,d\mu_H(A)\) を独立に保持して

\[
\boxed{\int f_H(A)S_H(A,B)\,d\mu_H(A)=V_H+X_H(B)}
\]

を形式証明。右空間halfweightは元source平均ゼロによって消え、左空間halfweightは \(V_H\) を係数1で与える。\(X_H(B)=0\) や符号に関する仮定は加えていない。

## CLOSED — 真正符号付きtransferの二次残差評価

固定mathlibの微分評価により全 \(x\ge0\) で \(0\le e^{-x}-1+x\le x^2/2\) を証明。元のglobal slab action budgetを \(C_H\) とし、元Haar source L¹質量を \(M_{\rm src,H}=\int|f_H|\,d\mu_H\) とする。真の完全Wilson核についてすべての \(\beta\ge0\)、元空間境界 \(B\) で、

\[
\boxed{
\left|T_{H,\beta}(B)+\beta(V_H+X_H(B))\right|
\le E_H(\beta),\qquad
E_H(\beta)=\frac{(\beta C_H)^2}{2}M_{\rm src,H}.
}
\]

ここでは新しい \(\beta C_H\le1\) 条件を要求せず、符号付きsourceを正値sourceで置き換えない。連続性／可積分性／線形化積分／signed Taylor Haar変動を別々のLean補題に分けて検証した。

## CLOSED — AHN正のsource二次モーメントから条件付きtransfer符号へ

AHNの真正元source下界

\[
F_H=\left(\frac{3p_H}{8}\right)^2\kappa(1/96)^{p_H}>0,\qquad
F_H\le V_H
\]

をそのまま使用して、

\[
T_{H,\beta}(B)\le-\beta(F_H+X_H(B))+E_H(\beta)
\]

を形式証明。その帰結である

\[
\boxed{
E_H(\beta)<\beta(F_H+X_H(B))
\implies T_{H,\beta}(B)<0
}
\]

も証明した。これは与えられた実際の\(B\)で条件が満たされた場合の負符号証明書であり、固定結合 \(\beta_0=\log(3/2)/64\) において実際に条件が成り立つことを主張しない。

## Lean4全文診断と修正履歴

初回CI `42362916579` は失敗。変更Lean全行・imports・依存ソース・固定mathlibの微分／積分APIを確認し、`id`関数の未簡約、局所notationのdot projection、関数値と関数加減算の不一致、巨大な`whnf` elaborationのタイムアウトを切り分けた。

途中 `42364819811`、`42365574719`、`42366231620` も診断に利用。独立積分補題による局所化と、元Boltzmann核の`exp(-beta*S)`への厳密な同一視により最終 `42366786649` でLean定理本体は成功したが、変更Leanに微分補題のlinter warningが5件残った。最後の `2a49d636…` は微分証明の `convert`／`simp`／`ring` の過剰なtactic組合せだけを簡約し、`42372491180`でwarning/errorを0/0にした。定理文／物理source／元Wilson核／真正Haar測度／公理依存は弱めていない。

## OPEN — 次段AHQへの引継ぎ

真正crossing相関 \(X_H(B)\) の符号・数値区間・変動を元のSU(2)一リンクHaar構造と境界の幾何により評価し、\(F_H+X_H(B)\) と残差 \(E_H(\beta_0)\) の実際の大小関係を証明できるか調べる。符号付き相関を正部分の積分と無条件同一視しない。定量transfer下界、実際に評価されたAGP true-Haar signed table、二符号殻、H一様coercivity、Hamiltonian spectral gap、4D continuum Yang–Mills質量ギャップは未証明である。

[正本AHP Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1f89ba949d3a7bafcd9d945ae57ddb73724b19bf/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFirstOrderHaarExpansionV5_PZ37AHP.lean)。

本記録は新規Markdownファイル1件のappend-only追補であり、文書専用PRでStrict Leanは再実行しない。
