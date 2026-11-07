# P4-Q2-PZ37AHI 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。元Wilson作用、ZW centered physical source、完全one-slab核、Haar測度、既存AGP/AGUの左積分格子、AHGの右境界メッシュ、固定Lean/mathlibを変更しない。

## 正本・Exact-source検証・統合

| 項目 | 検証値 |
| --- | --- |
| [AHI定理PR #6442](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6442) | **MERGED** |
| AHH継承HEAD | `da7fc40647103674d7c52d7a44571d5b0afb1aad` |
| 最終Lean source HEAD | `7cd77c114f4487696fb54959981db756b85d79e2` |
| PR test-merge HEAD | `279b8fb54f22330b0a5403769e2e8f286beb579a` |
| 定理squash HEAD | `cf0250b1fc72cc622620dfd1b9bf39468b4c4b99` |
| 共通Git tree（source/test-merge/squash） | `720ecd42d8eb2342fc7eb22c586ed0758eaa8654` |
| [Exact-source CI #42336830972](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42336830972) | **completed / SUCCESS** |
| Changed Lean job | `128295525459` completed / SUCCESS |
| Lean依存閉包 | **11,370 / 11,370 SUCCESS** |
| 新規公理監査 | **8定理**、`propext`・`Classical.choice`・`Quot.sound` のみ |
| sorryAx | **なし** |
| 変更Lean warning / error | **0 / 0** |
| 独立MCP completion receipt | `128297103672` completed / SUCCESS |
| 変更 | 新規Leanファイル1件のみ、既存Lean/物理定義変更なし |

GitHub MCPから実診断 `lean-fast-check-log` artifact `13559364106` を回収した。実ログ末尾の `Build completed successfully (11370 jobs).`、AHI新規8定理の `#print axioms`、変更ファイルwarning/errorゼロ、sorryAx不在を直接確認した。fixed Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。source・test-merge・squashのGit treeは完全一致した。別のStrict Lean/Governance workflowが実行されたとの主張はしない。

## CLOSED — 真正結合の合理的上界

元の正の固定結合は
\[
\beta_0=\log(3/2)/64.
\]
固定mathlib `Real.log_le_sub_one_of_pos` により \(\log(3/2)\leq 1/2\)、したがって
\[
0<\beta_0\leq 1/128
\]
を形式証明した。浮動小数点値を仮定していない。

## CLOSED — Haar依存値を消した右境界誤差

AFZの元ZW sourceの真のHaar \(L^1\) 質量 \(M_H\) に対する \(M_H\leq p_H\)、AHFの元正向きリンク数 \(=\) 元plaquette数 \(p_H\)、AEV/AGG/AHHの真正弦距離Lipschitz評価を合成し、全体係数を

\[
C_H=13\beta_0M_H\leq \frac{13}{128}p_H
\]

とした。右境界に指定するAHGの有理SU(2)メッシュは任意の \(N>0\) に対して誤差 \(4/N\) の被覆を持つ。よって任意の元右境界 \(B\) に対し、元AGL有理座標Type証拠を持つラベル配置 \(a\) が存在して

\[
\boxed{
|T_H(B)-T_H(B_{N,a})|\leq \frac{13p_H^2}{32N}
}
\]

を満たすとLean4で証明した。これは具体的な既知有理係数を持つ厳密評価であり、未知のHaar \(L^1\) 値を誤差条件に残さない。元のHaarセル質量を数値積分したわけではない。

## CLOSED — 真正AGP有理端点に応じた安定符号領域

元AGP signed-Haar表の厳密な下端が少なくとも \(q>0\) なら、その表が証明する真のtransferは \(T_H(B)\geq q\)。任意の \(N>0\) で

\[
\frac{13p_H^2}{32N}<q/2
\]

を満たせば、AHG右境界メッシュのある配置 \(a\) は

\[
\boxed{T_H(B_{N,a})>q/2}
\]

を満たす。負の元AGP上端が \(\leq -q\) なら同様に

\[
\boxed{T_H(B_{N,a})<-q/2}
\]

を証明した。両方向とも元AGPの真のHaar質量とsigned min/maxの端点による包含関係を使用し、符号を勝手に捨てない。

この基準は数値的な \(N\) の選択を可能にする**条件式**だが、現段階の \(q\) はAHHの存在証明によって選択されるもので、実際の数値を抽出したわけではない。

## CLOSED — 一つの符号と共通有理余裕幅の非有界次数存在

AHHによる無条件な元AGP厳密符号表の存在に上の誤差定理を適用し、任意の有限体積 \(H\) について

\[
\boxed{
\exists q\in\mathbb Q_{>0},\quad
\left[
\begin{aligned}
&\forall M\in\mathbb N,\ \exists N>M,\exists a:\ T_H(B_{N,a})>q\\
&\hspace{45pt}\lor\\
&\forall M\in\mathbb N,\ \exists N>M,\exists a:\ T_H(B_{N,a})<-q
\end{aligned}
\right]
}
\]

をLean4で形式証明した。**どちらか一つの符号枝で、同一の正の有理余裕幅を保ちながら任意に大きいメッシュ次数へ進める**という主張である。両符号が存在するとは言わない。

証明は元AHHの有理証明書から厳密余裕幅を半分にし、Archimedeanな整数次数選択と上の普遍的な誤差係数により行う。有限Hごとの存在であり、H一様下界ではない。

## Lean4初回CI失敗の理由と修正

初回HEAD `9b47c7fbb7eaa64d039cc3c2505c420d05914e4c` のCI `#42336405596` は依存モジュールではなく新規AHI内の3箇所で失敗した。診断：
- `div_lt_iff₀` の積は `N*s` であり、直接 `s*N` として受け取れない。定理の定義上の書式を合わせ、後段の `nlinarith` で交換を処理した。
- `p4Q2PZ37AHI_fixedCoupling_le_one128` は定理文にHが現れないため自動で不要なsection変数が除かれた。呼び出しの余分な `H` を削除した。
- 有理式 \(-Q/2\) と \(-(Q/2)\) をそのまま `simpa` で同一視できなかった。正確な有理キャスト後に `ring` で同値を示した。
- 未使用の `hq` 引数2箇所を削り、変更Lean警告をゼロにした。

修正は**定理文の仮定、Wilson source、Haar法則、kernel、結合定数を一切変更していない**。最終CIでは全8定理の公理依存が標準公理のみ、sorryAxなしとなった。

## OPEN — 実際に評価済みの有限符号証人

ここでCLOSEDになったのは、真の右境界近似誤差の明示的有理上界と、**未特定の一符号枝の**非有界格子次数安定性である。右境界の数値的ラベル配置、有理余裕幅 \(q\) の具体値、元Haar質量の数値区間、具体的に `true` を返したcheckerのログは依然存在しない。二符号殻、H一様coercivity、Hamiltonian gap、連続体4D Yang–Mills質量ギャップも未証明。

## NEXT — AHJ

元AGNのより鋭い点wise centered source bound \(|f_H|\leq p_H/2\) をHaar \(L^1\) へ移して係数 \(13/32\) をさらにtightenする可能性がある。また、真正Wilson kernelの低次Haarモーメントと相殺を利用し、固定H・右境界の実際の正負符号と正の有理数値余裕幅を評価する。巨大な全直積表の機械的全列挙は主経路としない。

[AHI Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/cf0250b1fc72cc622620dfd1b9bf39468b4c4b99/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalExplicitRationalRobustSignV5_PZ37AHI.lean)。正式記録は新規ファイル追加のみ。旧README/ROADMAPと全履歴は保持し、文書専用PRでStrict Leanを起動しない。
