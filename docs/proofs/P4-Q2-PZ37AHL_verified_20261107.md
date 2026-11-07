# P4-Q2-PZ37AHL — 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。Lean定理の唯一のcanonical branchは `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。運用は append-only／tighten-only／overwrite-forbidden／same-root。元ZW centered Gauss-law source、元の完全SU(2) Wilson kernel、元の空間積Haar測度、既存AHK/ADZ/ADL/AGG/AHJの証拠履歴を変更しない。

## 正本・形式検証

| 項目 | 検証・統合状態 |
| --- | --- |
| [AHL定理PR #6451](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6451) | **MERGED** |
| 継承元AHK canonical HEAD | `56938de16266aed9a56e4d0a40d432db19cf088e` |
| 最終exact-source HEAD | `417c493a85d65d6662f397d70897cebbeecb18f0` |
| PR test-merge HEAD | `2fac75de709fb7e2909b6f67caaa75c5101a0420` |
| 定理squash SHA | `ac891e38544720e988070726b1cea97a3bc6b2f5` |
| source/test-merge/squash共通Git tree | `4b1b6c642167802fc7d4b582b44490297c9d5772` |
| [Exact-source CI #42355519888](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42355519888) | **completed / SUCCESS** |
| Changed Lean job | `128352646677` completed / SUCCESS |
| 独立completion receipt | `128353979662` completed / SUCCESS |
| Lean依存閉包 | **11,373 / 11,373 SUCCESS** |
| 公理監査 | 新規8定理すべて `propext`、`Classical.choice`、`Quot.sound` のみ |
| `sorryAx` | **なし** |
| 変更AHL Lean warning/error | **0/0** |
| ソース変更 | 新規Leanファイル1件・327行追加、旧Lean・物理定義の変更／削除0 |

GitHub MCPから `lean-fast-check-log` artifact `13567611602` を回収して実ログ `lean-fast.log` を読解した。末尾の `Build completed successfully (11373 jobs).`、新規8定理の標準公理のみの `#print axioms`、`sorryAx` 0、新規AHL warning/error 0を確認した。ログ中には多数の既存Leanファイルに由来する非fatal警告が残っているが、変更AHLファイルは無警告。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` は不変更。別のStrict Lean/Governance workflow実行を主張しない。

## CLOSED — 元sourceと元transferの積の真の一リンク正則性

元centered連続代表 `f_H(B)=(W_H(B)-p_H)/2` と、元の完全Wilson kernelから作られた元signed-transfer `T_H(B)` の積を観測する。元AHKの絶対積差恒等式、元AGGのsourceスロープ12、AHJの真のHaar L¹ boundとtransferスロープ、AHJの絶対振幅上界から

```text
D_sp(B,C) = sum_{e in original Link_H} d_SU2(B_e,C_e),

|f_H(B)*T_H(B)-f_H(C)*T_H(C)|
  <= L_H * D_sp(B,C),

L_H = 6*p_H + (13/512)*p_H^2 >= 0
```

をLean4で証明した。元の弦距離・物理source・元transferを別の代理量へ置き換えていない。係数は真のplaquette数 `p_H` の多項式で、未知のHaar積分数値を含まない。

## CLOSED — 任意正半径の真正空間積Haar球質量に明示下界

実際の空間スライス全リンク集合で

```text
Ball_sp(B,R) = {C : original Cfg_H | D_sp(B,C) < R}
```

を定義した。任意の `R>0` に対して、すべてのリンクに中心Bの真のSU(2)弦距離球 `r=R/(card(Link_H)+1)` を置いた元ADL直積ボックスは `Ball_sp(B,R)` に包含される。

元ADLの**同じ**normalized spatial product Haar量の直積恒等式に、元ADZのすべての中心・正半径に通用する無条件のSU(2) Haar球質量下界を各リンクで適用し、

```text
kappa(R/(card(Link_H)+1))^card(Link_H)
  <= Measure.real muH (Ball_sp(B,R))
```

を得た。ここで `kappa(r)=Measure.toSphereBallBound 4 r / 4` は元ADQにある厳密なmathlib球体積下界であり、すべての正半径で正。元AHFで証明済みの `card(Link_H)=p_H` を用いて数学的に次の式が成り立つ。

\[
\boxed{
\mu_H(\mathrm{Ball}_{sp}(B,R))
\ge
\kappa\!\left(\frac{R}{p_H+1}\right)^{p_H}>0 .
}
\]

**指数は元の一空間境界の全リンク数p_Hである。** 元二境界pair-Haarを借用した2p_H指数や、仮想的なHaar質量上界は用いていない。正数係数はHとRに依存し、体積一様ではない。

## CLOSED — 正相関点から、真正Haar正質量の同符号領域へ

元AHKの無条件正値相関定理により、各有限体積Hについて

```text
exists B : original Cfg_H, 0 < f_H(B)*T_H(B).
```

上記L_Hと半振幅から `R=(f_H(B)*T_H(B)/2)/(L_H+1)>0` を構成する。この真の空間ℓ¹弦距離球では、全Cに対して

```text
f_H(C)*T_H(C) > f_H(B)*T_H(B)/2 > 0
```

を形式証明した。さらに実数の有理稠密性から `0<q<f_H(B)*T_H(B)/2` を選び、真正Haar量への集合包含によって

\[
\boxed{
\exists q\in\mathbb Q_{>0},\exists B,\exists R>0,\qquad
\mu_H\{C:f_H(C)T_H(C)>q\}
\ge
\kappa\!\left(\frac{R}{p_H+1}\right)^{p_H}>0.
}
\]

を証明した。これは、元の空間Haar下の「作用平均からの偏差とsigned-transferの向きが一致する」境界が**単なる一点でなく正質量の領域を形成する**厳密な証明である。

さらに、

```text
muH({C: (0<f_H(C) and 0<T_H(C))
       or (f_H(C)<0 and T_H(C)<0)}) > 0
```

を直接の系として形式証明した。正・負の二種類を区別し、**その和集合**が正質量であることを証明したのであり、個別の正枝・負枝の両方が正質量とは主張していない。

## 証明の境界・未解決事項

今回CLOSEDとなったのは、元Wilson作用と元transferの符号整合領域の**正の空間Haar質量**と、元SU(2)球の真正幾何による明示的なH依存下界。数値的な境界B・半径R・有理余裕幅q・Haar積分の具体値を抽出していない。右境界メッシュのラベルはこの新規質量定理には不要であり、AHE/AGP左Haar格子とも同一視していない。

両符号殻、H一様な質量下界、volume-uniform coercivity、Hamiltonian gap、連続体4D Yang–Mills mass gapはいずれも未証明のまま。

## NEXT — AHM

次はこの正質量領域のBorel・可測性を元transferの連続性から明示的に整理し、さらに元Wilson作用・核のHaarモーメントから、評価可能な具体的正負符号証明書へ進める。証人の存在を計算済みの数値証明書と混同しない。

[AHK継承・AHL Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/ac891e38544720e988070726b1cea97a3bc6b2f5/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAlignedPositiveSpatialHaarMassV5_PZ37AHL.lean)。本文は新規正式証明記録として追加。旧README/ROADMAP・既存proofsは保全。文書専用変更でStrict Leanは起動しない。
