# P4-Q2-PZ37AHV — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の形式定理正本：`formal/real-hilbert-uniform-coercive-strong-limit`。GitHub `main` は正式文書ミラー。運用原則：append-only／tighten-only／overwrite-forbidden／same-root。既存Lean・真正SU(2)完全一スラブWilson核・左右空間halfweight・元ZW Gauss-law signed source・積Haar・型付き証拠履歴・固定toolchain・workflowを変更しない。

## 1. authoritative exact-source検証台帳

| 項目 | 検証済み結果 |
| --- | --- |
| [AHV定理PR #6481](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6481) | **MERGED** |
| AHU統合済み継承元HEAD | `474ae8cf5a76532d630c451ce804d2486f261112` |
| 初回source HEAD | `8d27d3dd662ebc0cda49bf2857c495ab711dc834` |
| 第2回source HEAD | `b44117071df30cd4f9569f37742eadca06e9de11` |
| 最終source HEAD | `fac2fe9759a84bb1fa1d0915ed072ac02397cc18` |
| 最終test-merge HEAD | `fbe07f50fa51f2d6998e3904680704415230b8db` |
| squash定理正本HEAD | `71ffefb193b0267089176942089780f2276adee0` |
| source／test-merge／squash共通Git tree | `9994b6f037fc2d07a06a13df2506946b4aebf21c`（完全一致） |
| [最終CI #42428149350](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42428149350) | **completed / SUCCESS** |
| Changed Lean job | `128570858240` — SUCCESS |
| 独立completion receipt | `128572267673` — SUCCESS |
| Strict Lean依存閉包 | **11,383 / 11,383 SUCCESS** |
| AHV新規宣言 `#print axioms` | **7件**、標準公理 `propext`／`Classical.choice`／`Quot.sound` のみ |
| `sorryAx` | なし |
| 変更AHV warning／error | **0 / 0** |
| 成功実ログartifact | `13597005011`、`lean-fast.log` 回収・監査 |
| 変更対象 | 新規AHV Leanファイル1件・251行、既存Lean／root／pins／workflow不変更 |

固定環境：Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。成功ログ末尾は `Build completed successfully (11383 jobs).`。AHV全7宣言で標準公理のみ、変更警告・エラー0/0を独立確認した。既存依存ファイルの歴史的warningは変更AHVの監査と分離した。

## 2. CLOSED — 元三次sourceの点wise上界と真正Haar可積分性

既存AGNの真正元source連続代表

\[
f_H(A)=\frac{W_H(A)-p_H}{2},
\qquad |f_H(A)|\leq\frac{p_H}{2}
\]

を変更せずに使用した。非負性 \((f_H(A))^2\ge0\) により

\[
-\frac{p_H}{2}f_H(A)^2
\le f_H(A)^3
\le\frac{p_H}{2}f_H(A)^2
\]

をLean4で形式証明した。元の空間SU(2)積Haarはコンパクト確率測度で、連続な元sourceの三乗は積分可能であることも独立したLean4宣言で証明した。

## 3. CLOSED — 元三次source Haarモーメントの無条件厳密区間

元AHSで定義した**真正元source**の三次HaarモーメントとAHNで証明済みの二次sourceモーメントを

\[
M_{3,H}:=\int_{\mathrm{Cfg}_H}f_H(A)^3\,d\mu_H(A),
\qquad V_H:=\int_{\mathrm{Cfg}_H}f_H(A)^2\,d\mu_H(A)>0
\]

として保持し、元Haar上で積分単調性を使用して

\[
\boxed{
-\frac{p_H}{2}V_H\le M_{3,H}\le\frac{p_H}{2}V_H
}
\qquad
\boxed{|M_{3,H}|\le\frac{p_H}{2}V_H}
\]

を形式証明した。三次モーメントの数値・符号・ゼロ値を仮定していない。これは保守的な無条件区間であり、中心twistの存在を必要としない。

## 4. CLOSED — 完全一スラブ二次sourceモーメントの二側区間

AHUで既証明の元完全一スラブWilson作用・元混合Haarの等式は

\[
M_{2,H}(B)=M_{3,H}+(3p_H+W_H(B))V_H.
\]

第3節の元Haar三次モーメント区間を代入して

\[
\boxed{
\left(\frac{5p_H}{2}+W_H(B)\right)V_H
\le M_{2,H}(B)\le
\left(\frac{7p_H}{2}+W_H(B)\right)V_H
}
\]

をLean4で証明した。さらに元AHNの \(p_H>0,\ V_H>0\) と元のWilson空間作用の \(W_H(B)\ge0\) を使い

\[
\boxed{M_{2,H}(B)>0}
\]

を全有限H・全真正右境界Bで形式証明した。

**この正値性はsourceで重み付けした二次ACTIONモーメントについての数学的命題であり、固定 \(\beta_0\) のtransfer符号、自己共役Hamiltonianのスペクトルギャップ、連続体質量ギャップとは異なる。**

## 5. CLOSED — Haar保存source反転があれば三次モーメントゼロ、という正確な条件付き帰結

空間構成上の変換 \(T:\mathrm{Cfg}_H\to\mathrm{Cfg}_H\) が実際に

\[
T_*\mu_H=\mu_H,
\qquad f_H(T(A))=-f_H(A)\quad(\forall A)
\]

を満たすことを**前提として明示した定理**を追加し、元のsource三次モーメントの符号反転と積分不変性から

\[
\boxed{M_{3,H}=0}
\]

をLean4で証明した。これは「条件付き帰結」の完成であり、実際にそのような \(T\) を構成したという主張ではない。実装には既存の `MeasureTheory.integral_map` を用い、元Haarを別の測度に置き換えていない。

## 6. Lean4全文診断・初回／第2回CIの修正

### 初回

初回 [CI #42427419011](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42427419011)、実ログartifact `13595469008` はAHV Lean3箇所でエラー。元AGN/AHN/AHUと変更AHV全文、imports、固定mathlibの加法順序と連続関数APIを照合した。

- 106行：`Continuous.pow` から `.integrable_of_hasCompactSupport` への改行・メソッド適用をLean4が関数適用として誤解釈。
- 167・172行：`add_le_add_right` が `c+a\le c+b` 型を返す一方、目標は `a+c\le b+c`。既存AHTで学習した左右加法の構造に従い `add_le_add_left` へ修正。
- これらの未解決ゴールが下流に伝播して一時的に `sorryAx` と表示されたが、新しい公理・仮定は採用していない。

### 第2回

第2回 [CI #42427763269](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42427763269)、実ログartifact `13595679818` で加法順序の2件は解消。連続性の証拠から可積分性を導く1件だけ残ったため、既存AHSと同じスタイルで `have hf : Continuous ...` として証拠を明示的に束縛し、`(hf.pow 3).integrable_of_hasCompactSupport` と適用した。

### 最終

最終source `fac2fe9759a84bb1fa1d0915ed072ac02397cc18` のCI #42428149350は11,383/11,383 SUCCESS。元の証明義務は保持し、7宣言すべて標準公理のみ、`sorryAx`なし、変更warning/error 0/0。独立completion receiptの成功後にsquashマージし、source/test-merge/squash Git tree完全一致をGitHub MCPで確認した。

## 7. OPEN — 次段AHWの真正偶数トーラス中心twist

ここから三次モーメントを厳密にゼロとするには、単なる「対称性がありそう」という理由では足りない。既存の偶数周期幾何 `PeriodicHypercubicEvenCoordinateParity` を元のリンク上で使用する。

空間方向 \(j\) のリンク \((x,j)\) に、法2の1-cochain

\[
\tau_j(x)=\sum_{i<j}\mathrm{parity}(x_i)\in\mathbb Z/2\mathbb Z
\]

を割り当てる候補がある。周期長 \(2(H+1)\) が偶数なのでparityは真正周期トーラス上で一価である。各空間プラケット \(i<j\) について、既存のparity_shift定理から形式的には

\[
\delta\tau(x;i,j)=1\pmod 2
\]

を得る。真正SU(2)中心 \(z=-I\) を用いたリンクごとの左乗変換 \(T(A)_{(x,j)}=z^{\tau_j(x)}A_{(x,j)}\) が真正Haarを保存し、全プラケット文字を反転するなら、AHVの第5節の定理へ接続できる。

**ただし本PRはこの具体的twist・全プラケットの符号変換・積Haar保存をLean4で証明していない。** 次段で元のプラケットholonomyの四辺・逆辺とSU(2)非可換積を含めて、実際の型上で証明することが必要。代替Gibbs posteriorや新公理による置換は禁止。

元固定結合 \(\beta_0=\log(3/2)/64\) の真正transfer符号・正負二殻、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは引き続き**未証明**。

[AHV真正Lean4定理全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/71ffefb193b0267089176942089780f2276adee0/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCubicHaarMomentEnclosureV5_PZ37AHV.lean)

本記録はdocs-only新規Markdownとしてのみ追記する。Strict Leanを再実行せず、既存ファイル・roots・pins・workflowを変更しない。
