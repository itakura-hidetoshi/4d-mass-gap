# P4-Q2-PZ37AJU — 真正元Wilson二時点冪の定量補正とAJA閾値

2026-11-11 JST。**Lean4形式認証済み／定理PR MERGED／統合後push再認証済み。**

## 正本・証明履歴

- Repository: `itakura-hidetoshi/4d-mass-gap`。
- Canonical branch: `formal/real-hilbert-uniform-coercive-strong-limit`。mainは文書ミラー。
- 定理PR [#6637](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6637) MERGED、変更は新規Lean1ファイルのみ（389行、既存Lean変更・削除0）。
- exact-source HEAD: `edf8d3ba1ed574687c6a32fba8a19d81447ac15c`、[CI #42957344244](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42957344244) completed/SUCCESS。
- source/merge共通Git tree: `ee4ef1452fcaab89047a19580f59c05701705e0e`。AJU Lean blob: `32db516f2b130693bda7e2c63917eb81ae9bd3d6`。
- 正式formal squash HEAD `033420df2039e5bed9e9509bb55e6343266b0683`。
- [統合後push CI #42958127760](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42958127760) completed/SUCCESS。
- source/pushの両方でLean依存閉包 `11,435/11,435` SUCCESS、12/12宣言の実公理出力は標準 `propext`、`Classical.choice`、`Quot.sound` のみ、`sorryAx`なし、変更AJU warning/error 0/0。
- 独立completion receiptはsource `event=pull_request exact_sha=edf8d3ba... source_result=success run=42957344244`、push `event=push exact_sha=033420df... source_result=success run=42958127760` で完了。
- 初回CI #42955873741 FAILURE: 正射影Pythagorasの`change`方向、`rw`後不要タクティク、加法不等式の左右、ゼロの二乗の型。
- 2回目CI #42956597764 FAILURE: 既に正しい直交射影形への不要な`rw`、加法結合の方向、出力正準ノルムの型付き等式の不一致。
- これらは新規AJU Leanファイルの証明手順のみ修正。既存定理文、元物理仮定、固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、workflow、rootは不変更。

## 認証された数学

全top固定空間への真正直交射影を `Q`、その直交補の元正規化Wilson転送制限を `R`、`q=‖R‖<1` とする。元の中心化ZW物理L²源 `f₀` の元分散 `V_H=‖f₀‖²` と、AJTで認証された真正一時点欠損下界

```
d_H(β) = β v_H / exp(β p_H) > 0,
v_H = (3p_H/8)^2 * (1/384)^(4n_H)
```

を再利用し、一般実Hilbert補題から固定有限H・β>0で次を証明した。

```
||S² f₀||² + (1-q⁴)*(d_H(β)/(1+q))² ≤ V_H
||S² f₀||² < V_H
```

この**無条件**二時点上界は真のsource分散に対する厳密改善。AJA厳密予算 `B_H(β)=m_H(β)² μ_H^{real}({B : u_H,β(B)<−m_H(β)})` とは別の量である。

AJUは下の**条件付き閾値**を原定義のまま明示し、

```
V_H − (1−q⁴)*(d_H(β)/(1+q))² < B_H(β)
```

が別途認証された場合に限り、**具体的整数n=2** が元AJA予算の厳密小証人になること、全top源射影の予算未満、元正規化Wilson転送後の全top直交成分非零を証明した。構成した「条件付き証人n=2」を「無条件証人が既に存在する」と言い換えてはならない。

## OPENと次段への継承

元AJA厳密予算に対して閾値不等式が成立する数値・体積・結合の具体証拠はまだ**NO_DATA**。また、`q`の有用な数値上界、追加top残余の十分小さい明示値、top一次元性、転送後励起の無条件非零、体積一様coercivity、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapはいずれも未証明。

次はAJTの真正L²欠損下界とAJRから、`q<1`だけを利用した**qを消去した全top源射影上界**をLean4で導く。その上で元AJA予算と直接比較可能か検証する。既存の曖昧さを消すためにsource、Haar、transfer、元AJA予算を変更してはならない。

append-only / tighten-only / overwrite-forbidden / same-root。
