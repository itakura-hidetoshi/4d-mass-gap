# P4-Q2-PZ37AJV — 元Wilson全top射影のq-free明示分散補正

2026-11-11 JST。**形式定理source認証済み・canonical formalへMERGED**。この記録が成立する範囲は元の有限体積H、結合β>0の真正SU(2) Wilson模型に限る。

## 正本・検証履歴

- Repository: `itakura-hidetoshi/4d-mass-gap`。
- 唯一の定理正本: `formal/real-hilbert-uniform-coercive-strong-limit`。mainは文書ミラー。
- 新規Lean1ファイル、273行追加、既存Lean変更・削除なし、9宣言と9件の`#print axioms`。
- 定理 [PR #6640](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6640)、Squash MERGED。
- 認証exact-source HEAD `d295c85ffa10d4c097ecab20e9d6312ca705f852`。
- [Exact-source CI #42972219152](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42972219152) completed/SUCCESS、11,436/11,436 Lean依存閉包、9/9宣言の公理監査はいずれも`propext`、`Classical.choice`、`Quot.sound`のみ。新規sorryAxなし、変更AJV warning/error 0/0、独立completion receipt `event=pull_request exact_sha=d295c85ffa10d4c097ecab20e9d6312ca705f852 source_result=success run=42972219152`、SUCCESS。
- 正式formal squash HEAD `716693195bc51c8f45776b089c16e516bd8529b3`。
- 認証source・mergeの共通Git tree `783c21db4fb2e869315eae8551c6e452dcfc50af`。
- 認証source・merge同一Lean blob `8dd7dca631b5bf14dc1280792291cfde43049a18`。
- 統合後push [CI #42973075691](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42973075691) は開始を確認。**pushの独立完了・公理実ログは、後続確認まで未認証**。定理sourceそのものの形式認証と区別する。
- Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、元のSU(2)物理定義、Haar、source、元AJA予算、root・workflow不変更。

## 証明された内容

元の中心化ZW物理Hilbert L²源を `f₀`、真正正規化SU(2) Wilson転送を `S`、全top固定部分空間の正準射影を `Q`、その直交補制限を `R` とする。既存の正・コンパクト転送定理により `q=‖R‖<1`。ただし、AJVの結論には数値的な `q` を一切残さない。

既存AJTで確定した真正一時点物理L²欠損下界

```
d_H(β) := β * v_H / exp(β*p_H) > 0,
v_H := (3*p_H/8)^2 * (1/384)^(4*n_H)
```

とAJRの`‖f₀−Sf₀‖≤(1+q)‖Q^⊥f₀‖`に `1+q<2`を併用する。元物理Hilbert空間の直交Pythagorasから、真の全top源射影に対し

```
||Q f₀||² + (d_H(β)/2)² ≤ V_H,
||Q f₀||² ≤ V_H - (d_H(β)/2)² < V_H
```

をLean4形式証明した。`V_H=‖f₀‖²`は元の真正Haar分散。選択top固有単位方向 `Ω` と、同じ元Type値の真正追加top成分 `r=Qf₀-⟨f₀,Ω⟩Ω` に対して、

```
||r||² ≤ V_H - ⟨f₀,Ω⟩² - (d_H(β)/2)²
```

も認証した。未知のtop一次元性は仮定しない。

さらに、真のAJA予算`B_H,β=m_H(β)² μ_H^{real}({B:u_H,β(B)<-m_H(β)})`に対して、

```
V_H - (d_H(β)/2)² < B_H,β
```

が**独立に立証された場合に限り**、既認証AJIの全top有限冪同値から、`∃ n≥1,‖Sⁿf₀‖²<B_H,β`、および転送後の元全top直交成分非零を得る。これは特定`n=2`の無条件証人ではない。AJUの`n=2`は別の`q`依存厳密条件を持つ。

## 未解決のobstruction

真正AJA予算との上の厳密比較は**NO_DATA／未認証**である。従って無条件AJA有限冪数値証人、転送後の無条件励起sector非零性は依然OPEN。加えてtop一次元性、追加top残余のAJA予算内への十分小さい実数評価、体積一様coercivity、Hamiltonian spectral gap、連続体4次元Yang–Mills質量ギャップも未証明。

append-only / tighten-only / overwrite-forbidden / same-root。


## AJV統合後pushの独立追認（同日追記）

[CI #42973075691](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42973075691) は `completed/SUCCESS`、formal exact merge HEAD `716693195bc51c8f45776b089c16e516bd8529b3` で **11,436/11,436** Lean依存閉包 SUCCESS。新規AJV9/9宣言の実公理は`propext`、`Classical.choice`、`Quot.sound`のみ、`sorryAx`なし、変更AJV warning/error 0/0。独立completion receipt `event=push exact_sha=716693195bc51c8f45776b089c16e516bd8529b3 source_result=success run=42973075691 attempt=1` と一致。上記の「push未認証」は記録作成時点の履歴として保存し、本追記で正式認証が完了した。
