# P4-Q2-PZ37AHN — 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。運用は append-only／tighten-only／overwrite-forbidden／same-root。元のSU(2) Wilson作用、元ZW Gauss-law center source、真正Haar積測度、ADK正規化弦距離、AFZ L²型付き代表、すべての既存Lean定理・証拠履歴を変更しない。

## 正本・exact-source検証

| 項目 | 検証・統合結果 |
| --- | --- |
| [AHN定理PR #6457](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6457) | **MERGED** |
| 継承元AHM canonical HEAD | `febd7554b0e5e55c1e44376c2a44d5a6297f7670` |
| 最終exact-source HEAD | `943d223a3205b1970e2aa418dc5b94bbeb7a31ed` |
| PR test-merge SHA | `8248ba12df77b350c4afae9d58727001c27c5a0e` |
| 定理squash SHA | `ddd0900ac43900e84321f7c758d52d7c2958cee9` |
| source/test-merge/squash共通Git tree | `f154acf56a028d32b135db44ed4a7fd3431003de` |
| [Exact-source CI #42359873093](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42359873093) | **completed / SUCCESS** |
| Changed Lean job | `128365795415` completed / SUCCESS |
| 独立completion receipt | `128366776834` completed / SUCCESS |
| Lean依存閉包 | **11,375 / 11,375 SUCCESS** |
| 新規宣言公理監査 | **12定理**、標準公理 `propext`／`Classical.choice`／`Quot.sound` のみ |
| `sorryAx`／変更Lean warning／error | **なし／0／0** |
| ソース差分 | 新規Lean1ファイル・328追加行、既存Lean・物理定義の変更・削除0 |

GitHub MCPから最終 `lean-fast-check-log` artifact `13569253022` を回収し、実ログ `lean-fast.log` を解析した。末尾の `Build completed successfully (11375 jobs).`、全12個の `#print axioms` 結果が標準公理のみであること、`sorryAx` 0、変更AHNファイルのwarning/error 0/0を直接確認した。source・test-merge・squashのGit treeも一致。固定Leanは `v4.30.0-rc2`、mathlibは `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。今回、別のStrict Lean/Governance workflow実行は主張しない。

## CLOSED — 具体的に指定した元恒等配置とsourceの厳密な負領域

新しい source や非物理的な中心ではなく、**元の全空間リンクが実際のSU(2)恒等元**である構成 `I_H(e)=1` を用いる。既存AHH/AGNで既証明の

```text
f_H(I_H) = -p_H/2,
p_H = card(original positive spatial links) > 0
```

を継承した。元ADKの真正Wilson正規化弦距離 `d_J` と元ADLの全リンク空間ボックスを用い、**各一リンク半径を厳密な有理数1/96**に固定した：

```text
S_H = { C : original Cfg_H |
           forall e : original Link_H, d_J(1,C(e)) < 1/96 }.
```

この集合は元のSU(2)積位相でOPEN、Borel可測である。元AGGの真正中心化空間sourceの全リンクLipschitz係数12を同じ元配置に適用し、

```text
forall C in S_H,
  D_sp(I_H,C) <= p_H/96,
  f_H(C) <= -3*p_H/8 < 0,
  3*p_H/8 <= |f_H(C)|,
  (3*p_H/8)^2 <= f_H(C)^2
```

を形式証明した。元Haar平均からの偏差が負であることの**空間領域全体での定量的な証明書**であって、`T_H(I_H)<0` やtransferの符号を主張するものではない。

## CLOSED — 元のHaar球積の真正質量下界

元ADLの空間積Haar量の厳密な直積恒等式と、元ADZの**すべての中心・正半径**に対する真のSU(2) Haar球質量下界を利用した。半径に依存する既証明の正の定数は

```text
kappa(r) = (Measure.toSphereBallBound 4 r : NNReal) / 4 > 0,
r=1/96.
```

このため同じ空間Haar法則 `muH` に関して

\[
\boxed{
\mu_H(S_H)\ge \kappa(1/96)^{p_H}>0
}
\]

を証明した。指数は**元の一空間境界のリンク数p_H**で、境界ペアHaarの2p_Hではない。上界の提供者は固定mathlibに基づく真のSU(2)球であり、独立に選んだ仮想的な質量や新しい確率法則ではない。ただし `kappa(1/96)` の具体的な十進有理値や数値区間は今回計算していない。

## CLOSED — 元Gauss-law物理sourceの真正Haar L¹・二次モーメント

元AFZの**型付き物理L²代表とのHaar-a.e.一致**を使い、

```text
Msrc_H = integral_C |f_H(C)| dmuH(C)
       = integral_C |(f0_H : Lp R 2 muH)(C)| dmuH(C)
```

を同一視できることを形式証明した。元AGGの符号領域での `3*p_H/8` 下界、元の積Haar量のボックス質量下界、可測性・可積分性・集合積分の単調性を合成し、

\[
\boxed{
\frac{3p_H}{8}\,\kappa(1/96)^{p_H}
\le M_{\rm src,H}
\le\frac{p_H}{2}
}
\]

を得た。右辺は統合済みAHJの既証明tight upper boundである。

さらに、同じ元中心化sourceの真正Haar二次モーメントを

\[
V_H^{\rm source}=\int_{\mathrm{Cfg}_H}f_H(C)^2\,d\mu_H(C)
\]

と置いた。元AFZのL²代表に対する同じ二乗積分との**型付き同一性**も証明し、元恒等ボックス上の振幅・Haar質量から

\[
\boxed{
\left(\frac{3p_H}{8}\right)^2
\kappa(1/96)^{p_H}\le V_H^{\rm source}
}
\]

を形式証明した。両モーメントは各有限Hで厳密に正である。これは元sourceの参照Haar二次モーメントであり、元Wilson核のtransfer相関やそのスペクトル下界ではない。

## CIのLean4記法エラーの構造と解消

初回HEAD `fd02587f3cb93b5e96246251112e6f2a4ab3181f` のCI [#42359496810](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42359496810) は、変更AHNファイルの2箇所で

```text
Unknown identifier «fCont».continuous.integrable_of_hasCompactSupport
Unknown identifier «fCont».continuous.pow
```

を報告した。固定Lean4の局所notation `fCont` の後続dot projectionを単純に参照できない文法・ elaboration 問題である。**連続代表の正本定義 `p4Q2PZ37AFZ_originalCenteredContinuous H` を括弧付きで明示**して `.continuous` と `.continuous.pow` を使うよう修正した。数学的定理文・仮定・元物理source・Haar測度・核を変更していない。初回の未完了証明で現れた下流sorryAxは最終HEADのCIで全件消失している。

## OPEN — 真のtransfer符号の数値証明

AHNで確定したのは**具体的な恒等配置を中心にしたsource側の明示的振幅・Haarモーメント下界**である。AHKの `∫ f_H T_H dmuH>0` は実際の完全Wilson核で厳密に正だが、これにsource二次モーメントの下界を乗じて**正の数値transfer下界を主張することはできない**。元Wilson核の量的な正値固有値や特定source方向の量的なpairing下界が別途必要である。LJのstrict positive-definitenessはH一様coercivityとは異なる。

元transferの具体的正負符号枝、AHG境界ラベル、真正AGU/AGP Haarセル質量の数値区間、実際にtrueと評価されたBoolean checker、二符号殻、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills mass gapは引き続き未証明／未評価。

## NEXT — AHO

元の完全Wilson核のsmall-\(\beta_0\)展開と、元ZW源のHaar平均0・正の二次モーメントの関係を追い、**具体的な境界のtransfer符号**を真のHaarモーメントから評価するための、実際に成立する符号付き相関と残差の厳密評価を探索する。無根拠に正の数値固有値を仮定せず、必要なobstructionを明示する。

[AHN Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/ddd0900ac43900e84321f7c758d52d7c2958cee9/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalIdentitySourceHaarMomentV5_PZ37AHN.lean)。今回の正式記録は新規Markdown1件。過去Lean/README/ROADMAPは不変更で、docs-onlyのためStrict Leanを起動しない。
