# P4-Q2-PZ37AHB 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。元物理model、元Type値・証拠履歴、元Haar、root、pinは不変更。

## Exact-source CI・Git tree・公理監査

| 項目 | 検証済み状態 |
| --- | --- |
| 定理PR | [#6421](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6421) **MERGED** |
| 最終source HEAD | `3cf4648dc8d2998c7c2e5efe612f131d1fa3a0e1` |
| test-merge SHA | `043b33a8c6f0ab14508c6bd532656d542722a956` |
| 定理squash SHA | `ff5ba6bb7d6156fb9049558bcde08a6940c3972e` |
| source/test-merge/squash 共通Git tree | `89d9e7c8dd21726a7c44d1dd0e30bcfd4b2d1d71` |
| [exact-source CI #42313988679](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42313988679) | workflow completed / SUCCESS |
| Changed Lean job `128222058921` | completed / SUCCESS |
| Lean依存閉包 | **11,363 / 11,363 SUCCESS** |
| 新規定理公理監査 | **14宣言；`propext`・`Classical.choice`・`Quot.sound` のみ** |
| sorryAx / 変更Lean warning / error | **なし / 0 / 0** |
| 独立completion receipt `128223825386` | completed / SUCCESS |
| 差分 | **新規Lean 1件、502追加行、削除0行** |

`lean-fast-check-log` artifact をGitHub MCPで回収・展開し、`Build completed successfully (11363 jobs).`、全14宣言の `#print axioms`、新規ファイルwarning/error0/0を独立確認した。旧依存ファイルの非fatal linter warningは当該新規変更のwarningに算入しない。固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。文書専用CIにStrict Lean実行を要求しない。

## CLOSED — AGJ階乗残差の任意精度

元AGJの有理Taylor残差のAHA認証包絡

\[
E_n=\frac{n+1}{n!\,n},\qquad n>0
\]

について、固定mathlibの `Nat.self_le_factorial` と有理数除算の単調性から

\[
\boxed{0\le E_n\le\frac2n}
\]

を証明した。Archimedean性から任意の正有理精度 \(\varepsilon\) に対して `∃n>0, E_n<ε` をLean4で証明。AGKで既証明の `tail(m)=(5/768)(1/25)^m→0` と組み合わせ、任意の `C≥0` に対して同じ二次数を選び

\[
\boxed{\exists m,n>0,\quad C\,t_m+4E_n<\varepsilon}
\]

を導いた。未知の実指数値・数値表・精度選択oracleは不要。

## CLOSED — 真正作用量上界と全中心共通autoScale

元Wilson one-slab作用には既証明の物理上界があり、任意の真正境界配置 \(A,B\) について

\[
0\le S_H(A,B)\le V_H,\qquad
V_H=2\,\mathrm{CombinatorialVolume}(H).
\]

AGLの元有理作用量はこの**同じ実作用量の厳密値**であり、AGN global floorのactionは元組合せ体積に正確に等しい。したがってどちらも `0≤S≤V_H` の同一上界を満たす。

元AGKのfixed coupling区間を旧AGJの真正上端 `13/2048≤1` と交差したまま利用し、元AGM自動整数スケール

\[
k(S,m)=\Bigl\lceil\max(|-\beta_m^+S|,|-\beta_m^-S|)\Bigr\rceil+1
\]

について全中心・全右境界・全次数で

\[
\boxed{k(S,m)\le K_H:=\lceil V_H\rceil+1}
\]

を形式証明した。元AGJの真の指数区間下端base `b` は `u≤0` における元指数のverifiedInterval下端なので

\[
\boxed{0\le b(S,m,n)\le1}
\]

も証明した。新しい物理核・測度・区間値を導入していない。

## CLOSED — 元AHA powered出力幅の共通Lipschitz証明

固定mathlibの `abs_pow_sub_pow_le` を原式に適用。`0≤b≤1`、`0≤δ≤1`、`k≤K` なら

\[
\boxed{(b+\delta)^k-b^k\le K\,2^K\delta}
\]

が成り立つことを形式証明した。元AHAの実際のpowered Taylor区間幅 `B(S,m,n)` は同じbase `b` と、独立した結合・Taylor誤差

\[
\delta(S,m,n)=\frac{S\,t_m}{k(S,m)}+4E_n
\]

の厳密差である。`0≤S≤V_H` より `0≤δ≤V_Ht_m+4E_n`。右辺が1以下のとき

\[
\boxed{B(S,m,n)\le K_H\,2^{K_H}(V_Ht_m+4E_n)}
\]

を証明した。この定量係数は**Hに依存**する；H一様定数ではない。

## CLOSED — 同一有限体積の真正kernel/floor幅の任意精度

任意の固定 `H` と正有理数 `η` について、上の幾何・階乗精度を共通選択することにより、

\[
\boxed{
\exists m,n>0,\quad
\forall S\in[0,V_H]\cap\mathbb Q,\quad B(S,m,n)<\eta
}
\]

を証明した。さらに前段AGZ/AHAの本物のAGM clipped kernel最大幅とAGN floor区間幅への降下を使用し、**同じ選択 `m,n` を任意の元AGU精度付きBorel格子・元有理右境界に対して共通使用**できることを形式化した：

\[
\boxed{
\begin{aligned}
&\forall H,\eta>0,\quad\exists m,n>0,\quad
\forall d,B,\\
&\qquad\Delta K_{\max}(H,d,B,m,n)<\eta,\\
&\qquad\Delta F(H,m,n)<\eta.
\end{aligned}
}
\]

ここで元 `d` はAGUの真正Borel格子、`B` は元AGL有理座標証拠付き境界である。元Haar cellの形・幾何・分割選択は一切変更しない。有限中心数に比例する追加誤差は生じない。

## Lean4全文修正と最終warning除去

初回CIの失敗は主として定義上の等式と代数的な等式の混同、`Nat` 指数と `ℚ` の比較の混同、固定mathlibの `abs_pow_sub_pow_le` の明示引数不足、型推論を期待しすぎた `by simpa`、局所非負証明不足であり、元物理定理の反例ではない。新規Lean全文と依存するAGJ/AGK/AGM/AGN/AGZ/AHAの型、固定mathlib補題を照合して修正した。第2回CIのLean11,363件はSUCCESSだが `field_simp` 完了後の到達不能 `ring` に起因する新規warningが2件残った。最終修正で後続 `ring` だけを除去し、第3回exact-source CI #42313988679 でビルド、14宣言の公理依存、変更warning/error0/0、独立receiptを検証した。

## OPEN — AHC以降の課題

AHBで**固定Hのkernel/floor誤差の任意精度**は成立した。次のAHCではAGYの真正signed-transfer区間幅

\[
\mathrm{width}(I_H)\le
\frac{p_H}{2}(\Delta K_{\max}+\Delta F/2)+2L_H(m)R+2M_H(m,n)\varepsilon
\]

に対して、固定Hで`L_H`・`M_H` の定数上界を証明し、精度 `R,\varepsilon,m,n` を一括選択することで**符号付きtransfer区間幅の任意精度**を形式化する。これは実際のtransfer値が非零である証明ではない。大体積Haar表の計算、非零符号、two-threshold shell、H一様coercivity、Hamiltonian gap、連続体4D Yang–Mills mass gapはなお未証明。

[AHB Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/ff5ba6bb7d6156fb9049558bcde08a6940c3972e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedVolumeTaylorPrecisionV5_PZ37AHB.lean)。
