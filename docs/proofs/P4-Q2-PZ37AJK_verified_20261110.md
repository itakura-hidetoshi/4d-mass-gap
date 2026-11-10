# P4-Q2-PZ37AJK — 真正Wilson有限冪による二種類の追加top残余の独立評価

2026年11月10日 JST。唯一のLean4定理正本は \`itakura-hidetoshi/4d-mass-gap\` の \`formal/real-hilbert-uniform-coercive-strong-limit\` である。このMarkdownは認証済み証明と実行時検査の来歴記録であり、それ自身を機械証明と同一視しない。

[定理PR #6605](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6605) **MERGED**。[統合済みLean leaf](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/dea4a9117fe257ce4f490ae5606a451cb7473a83/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFinitePowerIndependentTopResidualsV5_PZ37AJK.lean)。

## 1. 対象と形式的に使用した条件

元の有限H∈ℕ・β>0ごとの完全SU(2) Wilson one-slab、Gauss-law実Hilbert物理空間、積Haar、元符号付き中心化ZW源f₀、元の対称・正・コンパクト正規化transfer S、全top固定空間F=ker(S−I)、正準射影Q、直交補制限作用素R、選択単位topベクトルΩ、Haar定数単位ベクトルcを変更しない。

使用する上流結果はAJIの真正全top有限冪収束上界、およびAJJの真正Haar定数defectによる全top直交距離上界。一般Hilbert補題の第2定理では既存の固定H,βで成り立つq=‖R‖<1を正の分母条件に用いる。Ωが全topを張ること、cがtop固有ベクトルであること、H一様のq<1、追加top残余の消滅はどれも仮定しない。

## 2. 認証対象の二種類の上界

選択方向への内積をα_c=⟨c,Ω⟩、α_f=⟨f₀,Ω⟩とし、**異なる2つの残余**を

\`\`\`text
rᶜ := Qc − α_c Ω
rᶠ := Qf₀ − α_f Ω
\`\`\`

と置く。各固定H,βと任意の正整数n≥1について、AJKは次の別個の物理評価を形式証明した。

\`\`\`text
‖rᶜ‖ ≤ ‖Sⁿc − α_c Ω‖ +
         ‖R‖ⁿ · (‖c−Sc‖ / (1−‖R‖))

‖rᶠ‖ ≤ ‖Sⁿf₀ − α_f Ω‖ +
         ‖R‖ⁿ · ‖Qᗮf₀‖
\`\`\`

両式は同じ元Wilson演算子の**元の物理ノルム**による評価であり、代替物理作用素や擬似的なsourceは一切導入しない。定数側はAJJの(I−S)c defectを使い、ZW源側はAJIの元の直交source尾を別に保持する。

一般実Hilbertの補題は
\`‖Qx−⟨x,ω⟩ω‖ ≤ ‖Sⁿx−⟨x,ω⟩ω‖ + ‖R‖ⁿ‖Qᗮx‖\`
と、この全top尾をdefectで抑える補題である。一般補題にはωが全topに属するという不要な仮定さえ追加していない。

**これらの上界は未知の有限冪normを含む条件付きの構造評価であり、値が十分小さいことを主張しない。** nの具体的証人、元AJAの正Haar-L²証明書C_AJAを下回る厳密不等式、元励起sectorの無条件非零性、Hamiltonian gapは一切導出していない。

## 3. Lean4ソース・新規宣言と実公理監査

変更は1つの新規Lean leaf \`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFinitePowerIndependentTopResidualsV5_PZ37AJK.lean\`（+190行・削除0）。元既存ファイル、元Wilson source/kernel・Haar law、workflow、公開root、固定Lean/mathlibは変更していない。

新規4宣言（それぞれ末尾に実行時\`#print axioms\`を設置）：

| 宣言suffix | 証明内容 |
| --- | --- |
| \`realHilbert_extraTop_norm_le_finitePower_ajk\` | 一般実Hilbertでの任意選択方向に関する有限冪上界 |
| \`realHilbert_extraTop_norm_le_finitePower_defect_ajk\` | AJJの(I−S)c defectを用いた有限冪上界 |
| \`p4Q2PZ37AJK_originalHaarConstantExtraTop_norm_le_power_defect\` | 真正Haar定数側残余の元物理評価 |
| \`p4Q2PZ37AJK_originalSourceExtraTop_norm_le_power\` | 真正ZW源側残余の元物理評価 |

4／4宣言の実公理出力は \`propext\`、\`Classical.choice\`、\`Quot.sound\` の標準3公理のみ。新規\`sorryAx\`なし。

## 4. 初回CI失敗と全文修正の来歴

初回source \`4e1c51787205114ffa56903a519bc8dc95835c1a\` の [CI #42731583927](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42731583927) は completed／FAILURE。変更Lean leaf全文190行・AJI上流定理署名・AJJ既存defect評価・失敗ログを照合した。

- 68行：\`add_le_add_left hpower _\`は加える項を**右側**に配置する定理型となり、目的の「固定prefix + 左辺・右辺」の順序と不一致。
- 101行：\`add_le_add_left htail _\`も同様の辺順不一致。
- Leanエラーによる不完全証明の\`#print axioms\`には\`sorryAx\`が出た。初回結果を証明済みと誤認しない。

定理文、追加仮定、物理定義を変更せず、両箇所だけを\`add_le_add_right\`に修正。**失敗した型の左・右の配置**を根拠とする修正であり、仮定の緩和や証明の削除ではない。

修正source \`e822c2118f15d3a4a8b912a6d60826829f4332b9\` で再検証。

## 5. Exact-source、定理マージと実測確認

| 監査項目 | 観測結果 |
| --- | --- |
| Exact-source CI | [#42740594286](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42740594286) completed／SUCCESS |
| Lean依存閉包 | **11,425／11,425 SUCCESS** |
| 実公理出力 | **4／4、標準3公理のみ** |
| 新規sorryAx | なし |
| 変更Lean warning／error | **0／0** |
| 独立completion receipt | completed／SUCCESS、source HEADとrunに紐付く |
| 認証source HEAD | \`e822c2118f15d3a4a8b912a6d60826829f4332b9\` |
| 定理PR | [#6605](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6605) MERGED |
| formal定理merge commit | \`dea4a9117fe257ce4f490ae5606a451cb7473a83\` |
| source vs formal merge Git diff | **0変更ファイル**、統合側は1コミット先 |
| formal統合後push CI | 独立の完了・実ログ認証は未確認。SUCCESSを推定しない |

固定環境：\`leanprover/lean4:v4.30.0-rc2\`、mathlib \`5450b53e5ddc75d46418fabb605edbf36bd0beb6\`。completion receiptは機械定理の追加証明ではない。

## 6. AJL以降の障害と最小の次段

実際の \`‖(I−S)c‖\`、\`‖Sⁿc−α_cΩ‖\`、\`‖Sⁿf₀−α_fΩ‖\`、\`‖Qᗮf₀‖\` の真正物理値に、AJA証明書と比較できる非自明な上界は未構成。任意にnを増やしただけで追加top成分が消えるとも、小さくなるとも主張できない。AJIの全top極限は一般に非零の追加top残余を残す。

AJLでは元演算子における有限冪と全topの直交分解を厳密に保持しつつ、追加top残余に十分な定量情報が得られるかを検討する。もし得られなければ障害をそのまま記録する。

top一次元性、厳密AJA予算、無条件の励起sector非零性、体積一様coercivity、Hamiltonian spectral gap、4D連続体Yang–Mills mass gapは**OPEN**。append-only／tighten-only／overwrite-forbidden／same-root。
