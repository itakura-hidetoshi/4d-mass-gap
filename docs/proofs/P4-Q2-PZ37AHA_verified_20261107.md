# P4-Q2-PZ37AHA 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。`main` は文書ミラーであり、異なる履歴を保持する。

## Exact-source Lean4証明とGit正本

| 項目 | 検証済み値 |
| --- | --- |
| 定理PR | [#6418](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6418) **MERGED** |
| 最終exact-source HEAD | `6e1dab060ce19b9eda7542da3b33c160a2ff00a0` |
| test-merge SHA | `c97354def35e4f355f47063454fa02d1cbd6aebb` |
| 定理squash SHA | `00836486dd2795cd73e0b285583d600b088a5bbe` |
| source / test-merge / squash共通Git tree | `61663613839f72b5251105bdbf6355e82544ca91` |
| [Exact-source CI #42310738307](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42310738307) | workflow completed/SUCCESS |
| Changed Lean job `128211240389` | completed/SUCCESS |
| Changed Lean依存閉包 | **11,362 / 11,362 SUCCESS** |
| 新規定理公理出力 | **12件すべて標準公理 `propext`・`Classical.choice`・`Quot.sound` のみ** |
| sorryAx / 変更Lean warning / error | **なし / 0 / 0** |
| 独立completion receipt job `128213488072` | completed/SUCCESS |
| 定理差分 | 新規Lean1件のみ、既存Lean削除・改変なし |

GitHub MCPから `lean-fast-check-log` を回収し、`Build completed successfully (11362 jobs).`・新規12件の `#print axioms`・新規ファイルのwarning/error0/0を独立照合した。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。既存の物理モデル、元Haar、source、kernel、floor、transfer、集約root、pins、workflowは変更していない。別workflowのStrict LeanやGovernance実行は主張しない。

## CLOSED — 真正AGJ Taylor残差の階乗有理上界

元AGJの実際の有限有理Taylor残差について、`n>0`、`|q|≤1` なら

\[
0\le \mathrm{TaylorError}(q,n)
\le E_n:=\frac{n+1}{n!\,n}
\]

を形式証明。`E_n` は有理数で計算可能な値であり、外部の実数指数値を近似入力として受け取らない。

## CLOSED — 非正指数上のexp-Lipschitz・符号付きclip・整数乗

元固定結合 `β₀` と元の非負one-slab actionの指数引数は非正。したがって実指数の単調性と `exp(z)≥1+z` から

\[
x\le y\le0\implies e^y-e^x\le y-x
\]

をLean4で証明。AGJの実際の `max 0` クリッピングを保ち、スケール後の2つのTaylor底の差を指数入力幅と各Taylor残差で上から制御した。元AGJが`max 0`を取った後で `k` 乗することを変更せず、非負の整数乗の単調性から実際のAGJ指数出力幅を抑えた。

元AGK・AGMの真正指数端点を

\[
q^-=-\beta^{\mathrm{upper}}_m S,\quad
q^+=-\beta^{\mathrm{lower}}_m S,\quad
k=\mathrm{AGM\_autoScale}(q^-,q^+),\quad
u=q^-/k
\]

とし、`b=max(0,P_n(u)-TaylorError(u,n))` を元AGJの下端のまま定義した。AGZで証明済みの結合誤差 `t_m=(5/768)(1/25)^m` と組み合わせ、

\[
\boxed{
\mathrm{AGJ\_expUpper}(q^+,k,n)-
\mathrm{AGJ\_expLower}(q^-,k,n)
\le
\left(b+\frac{S\,t_m}{k}+4E_n\right)^k-b^k
}
\]

をLean4形式証明。これは真の元kernel・floorに対する**指数出力**の有理区間幅上界であり、入力幅だけの命題ではない。

## CLOSED — 元AGM kernel / 元AGN floor / AGU同一格子への降下

AGLの元one-slab actionの**厳密有理値** `S_i` をそのまま使用し、AGNの元global floorには既存の組合せ作用量 `S_floor` を使用。AGMの核値とBoltzmann指数表示の既証明等式を用い、依存型 `verifiedInterval` のtransportを簡約した。元AGM kernelおよび元AGN floorの実際のraw AGJ/AGK Taylor区間幅が、それぞれ上述の有限有理式 `B(S_i,m,n)`、`B(S_floor,m,n)` 以下であることを形式証明した。

AGZの**同一**非空真正AGUグリッドの全中心について、`B(S_i,m,n)` の有限最大値 `Bmax` を作成。セル数に比例する余分な誤差を導入せず、元物理signed-transfer区間について

\[
\boxed{
\mathrm{width}(I_H)\le
\frac{p_H}{2}
\left(B_{\max}+\frac{B(S_{\rm floor},m,n)}2\right)
+2L_H(m)R+2M_H(m,n)\varepsilon
}
\]

をLean4で証明した。元AGUの同じ非計算的選択格子、Haar細胞質量、元signed min/max、tighten-onlyな区間交差を維持している。

## Lean4 CI失敗の構造的理由と修正履歴

初期CIは `pow_le_pow_left₀` の非負性証拠を小さい底 `b` に渡したため、期待する `c^k≤(b+d)^k` に一致しなかった。正しい底 `c` の非負性へ修正。有理加法 `(b+u)+v` と `b+(u+v)` は自動的な定義上の等式でないため、`ring` で明示的な同一性を証明した。

さらに元AGK/AGMの `rw` で型付き認証区間をtransportする際、任意の型等式が端点を保存するという過剰一般化はLean4の依存消去で成立しなかった。これは真正kernelとBoltzmann値の**既証明等式**を使って簡約するのが正しい。最終修正では不必要な一般化を削除し、この物理的に同じ値の等式で区間を正規化した。最終CIはすべてのLeanエラーを解消し、公理依存も検証した。

## OPEN — 次段AHB以降

幾何誤差 `t_m→0` はAGKで形式証明済み。AHAの `E_n` は明示的な階乗有理量だが、この新しい**powered output budget** `B(S,m,n)` 自体が全中心で任意精度に収束することはAHAでは証明していない。次は原作用量の共通上界、実際の自動整数scale `k` の統一上界、`b` の上界、階乗tailの収束を接続して、固定Hでの真正kernel/floorの任意精度を形式化する。非計算的格子の大体積Haar数値表、真のtransfer非零符号、two-threshold shell、H一様coercivity、Hamiltonian gap、連続体4D Yang–Mills mass gapはなおOPEN。

[定理Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/00836486dd2795cd73e0b285583d600b088a5bbe/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTaylorOutputWidthV5_PZ37AHA.lean)。
