# P4-Q2-PZ37AJT — 真正Wilson L²一時点欠損ノルムの明示下界

2026-11-11 JST。**Lean4形式認証済み／定理PR MERGED／統合後push再認証済み。**

## 正本と検証経路

- Repository: `itakura-hidetoshi/4d-mass-gap`。
- Canonical branch: `formal/real-hilbert-uniform-coercive-strong-limit`。mainは文書ミラー。
- 変更範囲: 新規Lean leaf 1件（272行追加、既存Lean変更／削除なし）。定義2・定理7・公理監査9件。
- 定理PR [#6636](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6636)、squash MERGED。
- 最終exact-source HEAD `db521df94a095ad1e3c76267163d2ba5e10037dc`、[CI #42925478976](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42925478976)、completed/SUCCESS、11,434/11,434。
- sourceとmergeの共通Git tree: `b54ec7d2d51d20c7722fe383699068a5df47ac5a`。
- AJT Lean Git blob: `e3803fcfb82af46c3025d2fed90999968da1edc6`。
- formal squash HEAD: `b45bf3a17004a765c73dc66c2bea171a7fcb7e2a`。
- [統合後push CI #42926260138](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42926260138) completed/SUCCESS、11,434/11,434、別job completion receipt `event=push exact_sha=b45bf3a17004a765c73dc66c2bea171a7fcb7e2a source_result=success`。
- 新規9/9宣言の公理は `propext`・`Classical.choice`・`Quot.sound` のみ、新規 `sorryAx` なし、変更AJTファイル warning/error 0/0。
- 固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。定理と元の物理対象・仮定・root・workflow不変更。

## 形式証明済みの主張

元の有限体積 `H`、正結合 `β>0`、元の中心化ZW物理L²源 `f₀`、実際の正規化SU(2) Wilson転送 `S`、元plaquette数 `p_H`、元リンク数 `n_H` に対し、AJTは元の右halfweight `w=e^(βW_H/2)` を真正Haar-L²元として構成する。

元の連続源代表・真正正規化転送のa.e.代表を用いて、AJSが認証した重み付き差積分 `D_w` と、同じ物理空間の真の内積 `⟨w,f₀−Sf₀⟩` が一致すると形式証明した。実際の右halfweightに `‖w‖₂≤exp(βp_H)` を示し、Cauchy–Schwarzを適用する。AIKの真正有理Haar箱分散下界

```
v_H = (3*p_H/8)^2*(1/384)^(4*n_H) > 0,   v_H ≤ V_H
```

を使い、次を固定H,βの真正物理Hilbert L²ノルムについて認証した。

```
beta*V_H / exp(beta*p_H) <= ||f₀-Sf₀||
beta*v_H / exp(beta*p_H) <= ||f₀-Sf₀||
```

不等式は元の符号付きZW源・両halfweight・元Haar・元物理転送を保持し、外部の擬似源や別の観測測度を用いない。

## 失敗・修正と未解決範囲

初期候補でLean4連続写像表記、固定mathlibの`ENNReal.toNNReal_one`・`Real.one_rpow`、`Lp.coeFn_sub`後の`Pi.sub_apply`、内積順序・除算の左右の elaboration failures を確認。最終sourceではこれらを変更ファイル内のみ修正。型検査成功後の一件のlinter warningは`<;>`から`;`へ置換して解消し、最終sourceを再認証した。失敗CIを成功と扱わず履歴保持。

この成果は**真正L²一時点欠損の正の下界**であり、元AJA予算との厳密比較、有限冪証人、追加top残余の十分小さい具体値、top一次元性、転送後無条件励起sector非零、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills mass gapは依然OPEN。

append-only / tighten-only / overwrite-forbidden / same-root。
