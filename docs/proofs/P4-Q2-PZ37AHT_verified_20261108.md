# P4-Q2-PZ37AHT — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の形式定理正本：`formal/real-hilbert-uniform-coercive-strong-limit`。GitHub `main` は正式文書ミラー。運用原則：append-only／tighten-only／overwrite-forbidden／same-root。既存Lean、元完全SU(2)一スラブWilson核、両端halfweight、元ZW Gauss-law signed source、積Haar、型付き証明履歴、固定toolchain、workflowは変更していない。

## 1．Authoritative exact-source形式証明台帳

| 項目 | 検証済み結果 |
| --- | --- |
| [AHT定理 PR #6475](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6475) | **MERGED** |
| 継承元AHS canonical HEAD | `cb63559fd8f52bc80eaa76e84f55579d29b227a5` |
| 最終AHT source SHA | `0d7da9703d540e79a8b508e1a7edac9dd78b15cc` |
| exact test-merge SHA | `8b5508865d7b179cd0308aee43c493b6e54b11a7` |
| squash定理正本HEAD | `9542c427443597999ac438076884ef756b258d0c` |
| source／test-merge／squash共通Git tree | `68d336f430595d59b652432641463f589fb3b88a`（完全一致） |
| [最終CI #42422301858](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42422301858) | **completed / SUCCESS** |
| Changed Lean job | `128553135776` — completed / SUCCESS |
| 独立completion receipt | `128554317731` — completed / SUCCESS |
| Lean依存閉包 | **11,381 / 11,381 SUCCESS** |
| 新規AHT定理・`#print axioms` | **10件**。標準公理`propext`／`Classical.choice`／`Quot.sound` のみ |
| `sorryAx` | なし |
| 変更AHT Lean warning／error | **0 / 0** |
| 実ログartifact | `13593888824`、`lean-fast.log` 回収・解析済み |
| 変更対象 | 新規AHT Leanファイル1件のみ。既存Lean／物理定義／公開root／workflow／pins不変更 |

固定環境：Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。実ログの末尾`Build completed successfully (11381 jobs).`と、AHT新規10宣言の公理監査、変更警告・エラー0/0を確認した。既存依存ファイルの歴史的warningは今回の変更warningに混入しない。

## 2．CLOSED — 元source二乗の真正ゲージ不変性

真正空間Wilson作用 \(W_H(A)\) は既存ゲージ作用に対し不変（既証明）。元AGNの真正連続ZW sourceは

\[
f_H(A)=\frac{W_H(A)-p_H}{2}
\]

なので、元の有限空間スライスの任意の頂点ゲージ変換 \(\gamma\) に対し

\[
f_H(\gamma\cdot A)^2=f_H(A)^2
\]

をLean4で形式証明した。元source二乗は連続であり、元の空間積Haarについて可積分である。ここではGauss-law物理sourceの元Haar-a.e.代表との型付き接続を保った。

## 3．CLOSED — 真正crossing混合Haarの右境界独立性

AHSで残った元の二次mixed Haar項を

\[
Y_H(B)=
\int_{\mathrm{Cfg}_H} f_H(A)^2
  S_H^{\mathrm{cross}}(A,B)\,d\mu_H(A)
\]

と定義済み。既存PTの「任意の連続・空間ゲージ不変な重み \(\phi\) に対する真正SU(2)元crossing Haarの右境界不変性」へ \(\phi=f_H^2\) を代入した。真正恒等境界 \(I_H\) について

\[
\boxed{Y_H(B)=Y_H(I_H)}
\]

を、さらに任意の元右境界 \(B,C\) について

\[
\boxed{Y_H(B)=Y_H(C)}
\]

をLean4で形式証明した。**この定数の実数値は未計算**であり、独立Gibbs posteriorへ置き換えた主張ではない。

## 4．CLOSED — 完全one-slab二次sourceモーメントの厳密アフィン性

AHS既証明の真正完全Wilson作用の二次source加重Haarモーメント

\[
M_{2,H}(B)
  :=\int f_H(A)S_H(A,B)^2\,d\mu_H(A)
  =M_{3,H}+(p_H+W_H(B))V_H+2Y_H(B)
\]

を保持する。ここで

\[
V_H=\int f_H(A)^2\,d\mu_H(A)>0,\qquad
M_{3,H}=\int f_H(A)^3\,d\mu_H(A).
\]

AHTで証明した定数性により、**真正元Haarでの**アフィン切片

\[
I_{2,H}:=M_{3,H}+p_HV_H+2Y_H(I_H)
\]

を定義し、

\[
\boxed{M_{2,H}(B)=I_{2,H}+W_H(B)V_H}
\]

を形式証明した。したがって任意の元右境界 \(B,C\) で

\[
\boxed{
M_{2,H}(B)-M_{2,H}(C)
=(W_H(B)-W_H(C))V_H
}
\]

が成立し、同じ元Wilson作用値なら二次モーメントも一致する。

AHNの**真正source分散正値** \(V_H>0\) から、

\[
\boxed{
W_H(B)<W_H(C)\Longrightarrow
M_{2,H}(B)<M_{2,H}(C)
}
\]

を形式証明した。これとは別に、元空間ゲージ変換に対する \(M_{2,H}\) の不変性も証明した。

## 5．CLOSED — 元crossing混合相関の無条件区間

AHQの元crossing Wilsonエネルギー範囲

\[
0\le S_H^{\mathrm{cross}}(A,B)\le2p_H
\]

と \(f_H(A)^2\ge0\) を真正積Haarの積分へ適用し、全有限H・全元右境界Bについて

\[
\boxed{0\le Y_H(B)\le2p_HV_H}
\]

をLean4で形式証明した。これは**定量区間**であって、\(Y_H(B)=p_HV_H\) や特定の数値は仮定していない。

## 6．Lean4全文診断とCI失敗修正

初回HEAD `4fcc4fac96aba33f401265095d3d83180872a102`、[CI #42421893932](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42421893932) はLean1箇所失敗。新規Lean全文249行・imports・既存PT／AHS／AHN／AGNの真正型と実ログ（artifact `13594122488`）を照合した。問題は純粋なLeanの不等式APIであった：

`add_lt_add_left hScaled intercept` は `W(B)*V + intercept < W(C)*V + intercept` という**右側に定数を加えた形**を返すが、目標は `intercept + W(B)*V < intercept + W(C)*V`。そこで `add_lt_add_right hScaled intercept` へ修正した。数学的な命題、元source、元作用、証明仮定を変更せず、その他の9定理も変更しなかった。

修正HEAD `0d7da9703d540e79a8b508e1a7edac9dd78b15cc` のCI `42422301858` ではLean全11,381件SUCCESS、全10定理標準公理のみ、`sorryAx`なし、変更AHT warning/error 0/0、独立completion receipt SUCCESSを確認した。

## 7．OPEN — 次段AHUへの残りの障害

AHTは \(Y_H(B)\) の**右境界独立性と上下界**を証明したが、実際の値 \(Y_H(I_H)\) は計算していない。\(M_{3,H}\) の真正SU(2) Haar三次モーメントも未評価。

次段AHUでは、元のリンクごとのHaar条件付き積分・既証明SU(2) character orthogonality・プラケットリンク支持により、\(Y_H(I_H)\) と \(M_{3,H}\) の具体値または符号付き有理区間を検討する。また、これを元完全Boltzmann transferの三次Taylor残差評価に厳密接続できるかを研究する。

元固定結合 \(\beta_0=\log(3/2)/64\) におけるtransfer符号、二符号殻、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは引き続き**未証明**。

[真正AHT Lean定理全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/9542c427443597999ac438076884ef756b258d0c/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalGaugeWardAffineSecondMomentV5_PZ37AHT.lean)

正式記録はdocs-only新規Markdown1件のappend-only追補であり、Strict Leanを起動しない。
