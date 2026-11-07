# P4-Q2-PZ37AHS — 正式証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。
唯一の形式定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main`は文書専用ミラー。
append-only／tighten-only／overwrite-forbidden／same-root。元のSU(2)物理完全one-slab Wilson核、両端の元空間halfweight、ZW Gauss-law signed source、元積Haar測度、既存の型付き証拠履歴は変更していない。

## 正本・検証台帳

| 項目 | 厳密な確認結果 |
| --- | --- |
| [AHS定理PR #6472](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6472) | **MERGED** |
| 継承元AHR定理／記録HEAD | `6bda56c7540c451923edbb5b49ae504cb339bf73` |
| 最終AHS source HEAD | `d887070204f120fc70459f93888e8f2e519385b1` |
| 正確なtest-merge commit | `9108714be509b0a9a1c07eb4e6bdf6e394422ee6` |
| AHS squash／定理正本HEAD | `bafda8d16148b94882a4a053fa3ff1224c729f4e` |
| source／test-merge／squash Git tree | `56ce44c02c616ecf0c4f4be6c0fb4c01a8dd0299` **三者完全一致** |
| [最終exact-source CI #42420827991](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42420827991) | **completed / SUCCESS** |
| Changed Lean job | `128548718476` completed / SUCCESS |
| 独立MCP completion receipt | `128549983369` completed / SUCCESS |
| Strict Lean依存閉包 | **11,380 / 11,380 SUCCESS** |
| 新規AHS定理／`#print axioms` | **4件**、`propext`／`Classical.choice`／`Quot.sound` のみ |
| `sorryAx` | なし |
| 変更AHS Lean warning/error | **0 / 0** |
| Leanログ実物 | GitHub Actions artifact `13593646656`、`lean-fast.log` |
| 変更対象 | 新規AHS Leanモジュール1ファイルのみ。既存Lean／root／pins／workflow／物理定義は不変更 |

固定Lean：`v4.30.0-rc2`。固定mathlib：`5450b53e5ddc75d46418fabb605edbf36bd0beb6`。
GitHub MCPを使って最終artifactの`lean-fast.log`を回収・解析し、`Build completed successfully (11380 jobs).`、変更ファイルのerror/warning 0/0、全4件の公理依存が標準公理のみであることを確認した。変更対象外の歴史的warningを今回の変更warningへ混入させていない。

## 1. CLOSED — 元crossing作用の二乗との真正Haar直交性

AHRの真正元物理連続source \(f_H=(W_H-p_H)/2=-\Phi_H/2\) と、既存PW2の真正centered first Wilson profile \(h_H=\Phi_H/2\) が**同じ元carrier上で**互いに負であることを、Lean4で型付きに照合した。

既存PW3が証明した、元完全crossing作用の二乗と真正centered profileとのHaar直交性
\[
\int_{\mathrm{Cfg}_H}h_H(A)
\bigl(S_H^{\mathrm{cross}}(A,B)\bigr)^2\,d\mu_H(A)=0
\]
を、型の同一視と積分の線形性だけで元ZW Gauss-law sourceへ移し、任意の有限体積Hと真正元境界Bで
\[
\boxed{
\int_{\mathrm{Cfg}_H}f_H(A)
\bigl(S_H^{\mathrm{cross}}(A,B)\bigr)^2\,d\mu_H(A)=0.
}
\]
を形式証明した。元Wilson Gibbs posteriorがリンク独立だとは仮定していない。

## 2. CLOSED — 任意二次crossing多項式の厳密な消滅

AHPの元source Haar平均ゼロ、AHRの真正一リンクcrossing相関ゼロ、上のPW3由来の二次消滅の三つを合わせ、任意の実係数 \(a,b,c\) と元境界Bについて
\[
\boxed{
\int f_H(A)\left[
a+bS_H^{\mathrm{cross}}(A,B)+
c\bigl(S_H^{\mathrm{cross}}(A,B)\bigr)^2\right]\,d\mu_H(A)=0
}
\]
をLean4で検証。あくまで元crossing作用の**次数2以下**のHaar選択則であり、一般次数、固定結合のBoltzmann核全体の消滅、正負符号を主張しない。

## 3. CLOSED — 真正完全one-slab作用の二次係数の型付き分解

元の両端空間halfweightを保持した完全one-slab作用は
\[
S_H(A,B)=f_H(A)+\frac{p_H+W_H(B)}2+
S_H^{\mathrm{cross}}(A,B)
\]
である。純粋なcrossing二次項、crossing一次項、source定数項は、**上の既証明Haar選択則でゼロ**となる。新規の真正Haarモーメント

\[
\begin{aligned}
V_H&=\int f_H(A)^2\,d\mu_H(A)>0,\\
M_{3,H}&=\int f_H(A)^3\,d\mu_H(A),\\
Y_H(B)&=\int f_H(A)^2S_H^{\mathrm{cross}}(A,B)\,d\mu_H(A)
\end{aligned}
\]
を別々のType値・積分として保持し、完全作用の二次sourceモーメントを
\[
\boxed{
\int f_H(A)S_H(A,B)^2\,d\mu_H(A)
=M_{3,H}+(p_H+W_H(B))V_H+2Y_H(B)
}
\]
と厳密に形式証明した。

ここで \(Y_H(B)\) の符号、定数性、値は**仮定も評価もしていない**。source三次モーメント \(M_{3,H}\) も実際の値未評価。これは二次Taylor係数を計算するための真正積分恒等式であって、二次Taylor残差の定量的な三次上界を追加証明したとは主張しない。

## 4. Lean4全文診断と構造的修正

初回source `c20ac151aafee8a91214d5c4926e20b41dd3cfc2` の [CI #42420336815](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42420336815) は失敗。GitHub実ログを回収して、新規Lean全文272行、全imports、固定mathlibの`integral_add`の型と旧AHP証明での使用方法を調べた。

- 87行付近：`rw`がすでに目標を完全に閉じていたのに後続の`ring`を適用し、`No goals to be solved`を発生。
- 148行付近：`integral_add`の関数加算`Pi.add`と、明示的なラムダ式の加算がLean elaboration上では直接同一視されず、`rw`が対象を発見できなかった。
- 255行付近：完全作用の二次モーメント分解でも同じ関数加算／ラムダ表示の不一致が繰り返された。

修正commit `d887070204f120fc70459f93888e8f2e519385b1` では、不要な`ring`を削除し、`Pi.add_apply`を使う**型付き外側・内側積分分割補題**で証明した。数理命題・元source・元Kernel・測度・仮定は変えていない。最終CI #42420827991 が全体SUCCESS、4件標準公理のみ、`sorryAx`なし、変更warning/error 0/0を確認した。

## 5. OPEN — AHT以降の厳密評価

最も直接的な次段は、既存PTの「ゲージ不変な重みでの一crossing Haar積分は右境界Bに依存しない」というWard定理を、実際の \(f_H^2\) に適用して \(Y_H(B)\) の境界定数性を証明できるか検証すること。その後、固定結合 \(\beta_0=\log(3/2)/64\) に必要な元核の三次Taylor残差、source三次モーメント、局所支持Haar相殺を定量評価する。

\(\beta_0\)での真正符号決定、評価済みAGP符号表、二符号殻、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは未証明。AHRのH依存小結合負符号定理は保持している。

[AHS真正Leanソース](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/bafda8d16148b94882a4a053fa3ff1224c729f4e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCrossingQuadraticHaarSecondMomentV5_PZ37AHS.lean)

本記録はdocs-only新規Markdown1ファイルのappend-only追補。文書専用PRでStrict Leanを再実行しない。
