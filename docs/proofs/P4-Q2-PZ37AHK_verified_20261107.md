# P4-Q2-PZ37AHK — 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元ZW centered Gauss-law physical source、元の完全SU(2) Wilson one-slab kernel、真正空間積Haar測度、既存AGP／AGU／AGL／AHG証拠履歴をそのまま保持。

## exact-source検証と統合

| 項目 | 確定結果 |
| --- | --- |
| [定理PR #6448](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6448) | **MERGED** |
| AHJ継承canonical | `71bd1f8a1a19b2f71f3a7baed86799b01de9951e` |
| 最終source HEAD | `1f9950777dfd92d25b34372b2b89b17a5bb243c3` |
| test-merge HEAD | `de9f531f7f22eb3143bfc5a24a412bddf9cd44f7` |
| 定理squash SHA | `617b4ce51b1006cd4f1309ab33080e1fe6f3c435` |
| 共通source/test-merge/squash Git tree | `c56a37df9e7bf9c9d6d10413c374d01c2240017c` |
| [Exact-source CI #42348778199](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42348778199) | **completed / SUCCESS** |
| Changed Lean job | `128332221976` completed / SUCCESS |
| 独立completion receipt | `128333239471` completed / SUCCESS |
| Lean依存閉包 | **11,372 / 11,372 SUCCESS** |
| 公理監査 | 新規9定理すべて `propext`・`Classical.choice`・`Quot.sound` のみ |
| `sorryAx` / 変更Lean warning / error | **なし / 0 / 0** |
| 定理変更 | 新規Lean1ファイル、340追加行、既存Leanの変更・削除0 |

GitHub MCPから最終 `lean-fast-check-log` artifact `13564791901` をダウンロードし、内部の `lean-fast.log` を実際に読解した。`Build completed successfully (11372 jobs).`、AHK9定理すべての `#print axioms`、`sorryAx` 0、新規AHKファイルのwarning/error 0を独立確認した。旧側の非fatal warningとは区別する。ピン留め：Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。別のStrict Lean/Governance workflowの実行を主張しない。

## CLOSED — 元の完全one-slab Wilson核のHaar二次形式と元signed-transferの等式

元sourceの連続代表を `f_H : C(Cfg_H,Real)`、本来のGauss-law physical L²源を `f0_H`、元transferを `T_H(B)=decomposableOneSliceTransferIntegral H 2 beta0 f0_H B` とする。AFZの**型付きL²代表一致**を通じて実際のHaar-a.e.値を連続代表へ移し、元Wilson kernelの対称性とLJの厳密な積分一致を使った。これにより、同じ元Haar測度に関する

```text
integral_A integral_B K_H(A,B) * (f_H(A)*f_H(B)) dmuH(B) dmuH(A)
  = integral_B f_H(B)*T_H(B) dmuH(B) > 0
```

をLean4で証明した。LJ/AHHの正の**完全**Wilson核（二つの空間half-Boltzmann重みを含む）を用いている。任意のL²同値類代表の点値を実際のf値と混同しない。

## CLOSED — 物理的な元Wilson作用とsigned-transferが同符号の境界

正のHaar積分と、非正関数のHaar積分が非正であるという基本事実から

```text
forall H, exists B : original Cfg_H,
  0 < f_H(B) * T_H(B)
```

を証明した。AGNの厳密中心化により `f_H(B)=(W_H(B)-p_H)/2` である。したがって証人は元Wilson作用がHaar平均 `p_H` より大きくかつtransferが正、または元Wilson作用が平均より小さくかつtransferが負の、いずれかである。

**「ある境界で同符号」を証明したのであり、全境界で同符号、正負両符号の個別存在、恒等右境界でのtransfer符号は証明していない。**

## CLOSED — sourceとtransferを同じAHG有理境界で同時に近似する

AHJの真のsource/transfer半幅上界とAHG/AGGの元SU(2)弦距離被覆から、同じ有理中心ラベル配置 `a : Link_H → AHG_meshIndex N` を選ぶ。

```text
D_sp(B,B_(N,a)) <= 4*p_H/N,
|f_H(B)-f_H(B_(N,a))| <= 48*p_H/N,
|T_H(B)-T_H(B_(N,a))| <= 13*p_H^2/(64*N),
|f_H(B)|, |T_H(B_(N,a))| <= p_H/2.
```

厳密な恒等式

```text
f_B*T_B - f_C*T_C = f_B*(T_B-T_C) + T_C*(f_B-f_C)
```

を使い、**同一の**右境界メッシュ証人に関する

```text
|f_H(B)*T_H(B)-f_H(B_(N,a))*T_H(B_(N,a))|
    <= (24*p_H^2+(13/128)*p_H^3)/N
```

を形式証明した。左右別の有理メッシュの証人をcompatibilityなしに貼り合わせていない。係数は元の厳密な有限plaquette数だけで表される**有理係数**であり、未知のHaar質量値を含まない。実際のHaar質量の数値計算はしていない。

## CLOSED — 元Wilson作用の厳密な有理評価と元AGP符号表の一致

上記の正の相関・明示的な有限格子誤差を組み合わせると、ある `N>96`、真正有理右境界 `B_(N,a)` で

```text
f_H(B_(N,a))*T_H(B_(N,a)) > 0
```

となる。元AGL/AGNからその元Wilson作用中心化値は**厳密な有理数**
`q_H(a)=AGN_centeredActionRational(H,B_(N,a))` である。AHEの真正AGU/AGP符号証明書完全性と接続して、

```text
exists N>96, exists a,
  (q_H(a)>0 AND original true-Haar positive AGP certificate exists)
  OR
  (q_H(a)<0 AND original true-Haar negative AGP certificate exists).
```

を形式証明した。これは物理的な元作用の有理符号と、**同じ**元signed-transferに対する認証可能な符号枝が一致することの無条件存在定理である。

AHG右境界メッシュとAGU左Haar積分格子を別のデータとして保持する。旧original24の全次数拒否定理AHFと矛盾しない。

## CLOSED — 正の有理「作用×transfer」余裕幅が全十分大次数で成立

先ほどの相関積が正の境界を固定し、実数間の有理数稠密性で `q in Rat, q>0` を選ぶ。AHJの単調な分母評価である `N0>96` 以降のすべてのNについて

```text
exists q : Rat, 0<q, exists N0>96,
  forall N>=N0, exists a,
    q < f_H(B_(N,a))*T_H(B_(N,a))
```

を形式証明した。これは「一つの符号枝の方向」を固定する主張ではなく、「同じ正の有理相関余裕幅の証人が、すべての十分大きな有限格子次数に存在する」という主張である。ラベル配置はNごとに変わってよい。

## 初回Lean警告と修正の構造

初回source `c2204a1733fdbc5220ea5ba775676f265a13cc9a` のCI `#42348412475` は 11,372/11,372 SUCCESS、新規9定理すべて標準公理・sorryAxなしだった。ただしAHKファイル142行の `push_neg` 非推奨警告が1件あった。元の `∃B,0<f(B)T(B)` の否定を、非推奨タクティクではなく `by_contra` と `lt_of_not_ge` を使った明示的背理法へ変更した。定理文・前提・元物理量・関係証拠に変更はない。修正版HEADのCIで変更ファイルwarning/errorは0/0になった。

## OPEN / NEXT — AHL

本定理は元Wilson作用と元transferの符号整合性を持つ**有理境界の存在**と、真正Haar表による有限符号検査への型付き接続を閉じた。具体的なラベル配置・符号枝・AGPの実際の質量区間・有理marginの数値評価は、依然として行っていない。

次は相関の正値域が真正空間Haar測度で正質量を持つこと、および元Wilson核の低次Haarモーメントや恒等境界での物理的符号を解析する。両符号殻、H一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは未証明のまま保持する。

[AHK Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/617b4ce51b1006cd4f1309ab33080e1fe6f3c435/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalActionAlignedHaarCorrelationV5_PZ37AHK.lean)。本記録は新規Markdownファイルのみ追加。既存README/ROADMAPと全過去証明履歴は変更せず、docs-only PRでStrict Leanは起動しない。
