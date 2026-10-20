#import "template.typ": *
#import "notation.typ": *

#let Gentzen(L) = $bold(sans("G"))_#L$
#let G3(L) = $bold(sans("G3"))_#L$

#show: slides-theme.with(
  config-info(
    title: [Embeddings of Propositional Logics into the Provability Logics ],
    subtitle: [証明可能性論理へ埋め込める命題論理について],
    author: [野口 真柊],
    date: [2026/10/23 @ MLG61],
    url: "https://sno2wman.github.io/MLG61/main.pdf",
    institution: [
      神戸大学システム情報学研究科 M2
    ],
  ),
)

#title-slide()

= はじめに

== 要旨

Solovayの証明可能性論理 $LogicS$ とJaparidzeの証明可能性論理 $LogicD$ に適当に修正したGödel変換によって埋め込める命題論理をシークエント計算によって与えた，という話をします．

#grid(
  columns: (1fr, auto),
  column-gutter: 12pt,
  inset: (x: 32pt),
  [
    - プレプリント: #link("https://arxiv.org/abs/2608.04620")
  ],
  [
    #qr-code("https://sno2wman.github.io/slides-for-MLG61/main.pdf", width: 180pt)
  ],
)
#pagebreak()

= 前提知識

== 地図

上は命題論理，下は様相論理．実線は論理の包含関係，点線は様相同伴を表す．

#figure(gap: 1em, caption: none)[
  #let nodes = (
    "VF": (label: $Logic("VF")$, pos: (0, 0)),
    "WF": (label: $Logic("WF")$, pos: (1, 0)),
    "F": (label: $Logic("F")$, pos: (2, 0)),
    "BPL": (label: $LogicBPL$, pos: (3, 0)),
    "FPL": (label: $LogicFPL$, pos: (3.5, -0.5)),
    "DPL": (label: text(fill: theme-colors.accent, LogicDPL), pos: (4.5, -0.5)),
    "SPL": (label: text(fill: theme-colors.accent, LogicSPL), pos: (5.5, -0.5)),
    "Int": (label: $Logic("Int")$, pos: (4, 0)),
    "KC": (label: $Logic("KC")$, pos: (5, 0)),
    "LC": (label: $Logic("LC")$, pos: (6, 0)),
    "Cl": (label: $Logic("Cl")$, pos: (7, 0)),
    "N": (label: $Logic("N")$, pos: (0, 2)),
    "EN": (label: $Logic("EN")$, pos: (1, 2)),
    "K": (label: $Logic("K")$, pos: (2, 2)),
    "K4": (label: $Logic("K4")$, pos: (3, 2)),
    "GL": (label: $LogicGL$, pos: (3.5, 2.5)),
    "D": (label: $LogicD$, pos: (4.5, 2.5)),
    "S": (label: $LogicS$, pos: (5.5, 2.5)),
    "S4": (label: $Logic("S4")$, pos: (4, 2)),
    "S4.2": (label: $Logic("S4.2")$, pos: (5, 2)),
    "S4.3": (label: $Logic("S4.3")$, pos: (6, 2)),
    "S5": (label: $Logic("S5")$, pos: (7, 2)),
  )
  #let edges = (
    ("VF", "WF"),
    ("WF", "F"),
    ("F", "BPL"),
    ("BPL", "Int"),
    ("Int", "KC"),
    ("KC", "LC"),
    ("LC", "Cl"),
    ("N", "EN"),
    ("EN", "K"),
    ("K", "K4"),
    ("K4", "S4"),
    ("S4", "S4.2"),
    ("S4.2", "S4.3"),
    ("S4.3", "S5"),
    ("K4", "GL"),
    ("BPL", "FPL"),
    ("FPL", "DPL"),
    ("DPL", "SPL"),
    ("GL", "D"),
    ("D", "S"),
  )
  #let MC = (
    ("VF", "N"),
    ("WF", "EN"),
    ("F", "K"),
    ("BPL", "K4"),
    ("Int", "S4"),
    ("KC", "S4.2"),
    ("LC", "S4.3"),
    ("Cl", "S5"),
    ("FPL", "GL"),
    ("DPL", "D"),
    ("SPL", "S"),
  )
  #diagram(
    spacing: 3.5em,
    edges.map(e => edge(
      nodes.at(e.at(0)).pos,
      nodes.at(e.at(1)).pos,
      stroke: theme-colors.secondary,
      "<-",
    )),
    MC.map(e => edge(
      nodes.at(e.at(0)).pos,
      nodes.at(e.at(1)).pos,
      stroke: theme-colors.foreground,
      bend: -20deg,
      "<-->",
    )),
    nodes.values().map(n => node(n.pos, text(n.label))),
  )
]

#let Fml = $serif("Fml")$

== Gödel-McKinsey-Tarskiの定理

直観主義命題論理 $Logic("Int")$ と様相論理 $Logic("S4")$ の間には深い関係がある．

#fact[@Göd33,@MT48][
  $
    Logic("Int") proves A <==> Logic("S4") proves A^goedelTr
  $
]


#definition[
  Gödel変換 $(dot.c)^goedelTr : Fml_upright("P") -> Fml_upright("M")$．

  - $p^goedelTr mapsto box p$，ただし $p$ は命題変数．
  - $bot^goedelTr mapsto bot$．
  - $(A -> B)^goedelTr mapsto box (A^goedelTr -> B^goedelTr)$
  - $(A and B)^goedelTr mapsto A^goedelTr and B^goedelTr$
  - $(A or B)^goedelTr mapsto A^goedelTr or B^goedelTr$
]

== $Logic("S4")$ の拡張について

#definition[
  命題論理 $L$ と様相論理 $M$ について $L proves A <==> M proves A^goedelTr$ なら*（変換 $goedelTr$ によって）$M$ は $L$ の様相同伴である*と言う．
]

$Logic("S4")$ の拡張論理に関する様相同伴はよく知られている．

#fact[cf. @CZ97][
  - $Logic("S4.2") & : Logic("S4") + dia box p -> box dia p$ は弱排中律・Jankovの論理 $Logic("KC") : Logic("Int") + not p or not not p$ の様相同伴．
  - $Logic("S4.3") & : Logic("S4") + box (box p -> q) or box (box q -> p)$ はGödel-Dummettの論理 $Logic("LC") : Logic("Int") + (p -> q) or (q -> p)$ の様相同伴．
  - $Logic("S5") & : Logic("S4") + p -> box dia p$ は古典論理 $Logic("Cl") : Logic("Int") + p or not p$ の様相同伴．
]

== Visserの $LogicBPL$ と $LogicFPL$

@Vis81 は主に証明可能性論理的な動機から $LogicBPL$ (*Basic* Propositional Logic) #footnote[_Basic_の由来はSmoryńskiが $LogicK4$ をbasic modal logicと呼んでいたことから由来するらしい．]と $LogicFPL$ (*Formal* ...) を導入した．

#definition[
  Visser--Gödel変換 $(dot.c)^visserTr : Fml_upright("P") -> Fml_upright("M")$ は命題変数の設定を $ p^visserTr mapsto p and box p $ で定義する．
]

#proposition[@Vis81][
  以下が成立する #footnote[これらはGödel変換 $(dot.c)^goedelTr$ でも成立する．]．
  $
    LogicBPL proves A & <==> LogicK4 proves A^visserTr \
    LogicFPL proves A & <==> LogicGL proves A^visserTr
  $
]

#pagebreak()

つまり $LogicK4$ ($LogicGL$) は変換 $visserTr$ によって $LogicBPL$ ($LogicFPL$) の様相同伴．

@Vis81 はKripke意味論によってこの事実を証明した．

#proposition[
  $LogicBPL$ は推移的かつ付値が遺伝的であるようなKripkeモデル（=直観主義命題論理のKripkeモデルから反射律を抜いたモデル）に対して完全．
]

*証明論的な方法によって埋め込むことも出来る．*

== $LogicBPL$ から $LogicK4$ への構文論的な埋め込み

@YS17 では $Logic("BPL")$ の G3-style (i.e. 多重集合ベース) のシークエント計算 $G3(LogicBPL)$ を与えて，それを $Logic("K4")$ のシークエント計算 $G3(LogicK4)$ の証明図へ忠実に変換する具体的な手続きを示した．

#theorem[@YS17][
  $G3(LogicBPL) proves Gamma => Delta$ iff $G3(LogicK4) proves Gamma^visserTr => Delta^visserTr$．
]

#pagebreak()

$G3(LogicBPL)$ の含意 $->$ に関する規則だけ見てみよう．
通常の $->$ の規則は入っておらず，代わりに次が入っている．

#definition[
  自然数 $k >= 0, n < 2^k$ を取り，$n$ の $k$-bitでの2進数表記 $n = sum^(k - 1)_(i = 0) 2^i c_i$ とする．
  このとき $chevron.l n chevron.r^k_i = c_i$ と定める．
  また，$k$-bitの表記だと思ったうえで $n$ の1の補数を $macron(n)$ で表す．

  例: $k = 3, n = 5 = 101_((2))$ のとき $chevron.l 5 chevron.r^3_1 = 0$．
]

#definition[$G3(LogicBPL)$ の $->$ 導入規則][
  $0 <= k$ と論理式 $C_0 -> D_0, ..., C_n -> D_n$ は任意として，前提が $2^k$ 個の $->$ 規則を導入する．

  $
    #prooftree(rule(
      name: $(->)_k$,
      $\[ Delta_i, Sigma, \{ C_j -> D_j \}_(j < n), A => B, Gamma_i \]_(i < 2^k)$,
      $Sigma, \{C_j -> D_j\}_(j < n) => A -> B, Pi$,
    ))
  $
  ここで $0 <= k$ であり，$i < 2^k$ に対して，$Delta_i := { D_j : chevron.l i chevron.r^k_i = 1 }$，$Gamma_i := { C_j : chevron.l macron(i) chevron.r^k_i = 1 }$ とする．
]

イメージとしては $C_0 -> D_0, ..., C_n -> D_n$ の前件と後件の組み合わせを片っ端から試すイメージ．

#pagebreak()

#example[$G3(LogicBPL)$ の $->$ 導入規則の例][

  $k = 0$:
  $
    #prooftree(rule(name: $(->)_0$, $Sigma, A -> B, A => B$, $Sigma => A -> B, Pi$))
  $

  $k = 1$:
  $
    #prooftree(rule(
      name: $(->)_1$,
      $Sigma,C_0 -> D_0, A -> B, A => B, C_0$,
      $D_0, C_0 -> D_0, Sigma, A -> B, A => B$,
      $Sigma, C_0 -> D_0 => A -> B, Pi$,
    ))
  $

  $k = 2$:
  $
    #prooftree(rule(
      name: $(->)_2$,
      $Sigma, \{C_j -> D_j\}_(j < 2), A -> B, A => B, C_0, C_1$,
      $D_0, D_1, \{C_j -> D_j\}_(j < 2), Sigma, A -> B, A => B$,
      $D_0, Sigma, \{C_j -> D_j\}_(j < 2), A -> B, A => B, C_1$,
      $D_1, Sigma, \{C_j -> D_j\}_(j < 2), A -> B, A => B, C_0$,
      $Sigma, \{C_j -> D_j\}_(j < 2) => A -> B, Pi$,
    ))
  $
]

== 論理 $LogicS, LogicD$ とその証明体系

$LogicGL$ の拡張として証明可能性論理で重要な論理として $LogicS, LogicD$ がある．

1. Solovayの証明可能性論理: $LogicS := LogicGL + box A -> A$．
  - $TA$ の証明可能性論理．
2. Japaridze(Dzhaparidze)の証明可能性論理: $LogicD := LogicGL + not box bot + box (box A or box B) -> box A or box B$．
  - $PA + #text[$Sigma_1$-反映原理 ($box_PA sigma -> sigma: sigma in Sigma_1$)]$ の証明可能性論理．

厳密に包含関係 $LogicGL subset.neq LogicD subset.neq LogicS$ が成り立つ．

#pagebreak()

#let seq(l) = $attach(tr: #l, =>)$
#let seq1 = seq("1")
#let seq2 = seq("2")
#let seq3 = seq("3")
#let level = $scr(l)$
#let LvRuleAx(l) = Rule($"Ax"_#l$)
#let LvRuleBotL(l) = Rule($bot L_(#l)$)
#let Inverse(R) = $#R^(-1)$
#let LvRuleWL(l1, l2) = Rule($W L^(#l1)_(#l2)$)
#let LvRuleWR(l1, l2) = Rule($W R^(#l1)_(#l2)$)
#let LvRuleCL(l1, l2) = Rule($C L^(#l1)_(#l2)$)
#let LvRuleCR(l1, l2) = Rule($C R^(#l1)_(#l2)$)
#let LvRuleAndL(l1, l2) = Rule($and L^(#l1)_(#l2)$)
#let LvRuleAndLI(l1, l2) = Inverse(LvRuleAndL(l1, l2))
#let LvRuleAndR(l1, l2) = Rule($and R^(#l1)_(#l2)$)
#let LvRuleAndRI(l1, l2) = Inverse(LvRuleAndR(l1, l2))
#let LvRuleOrL(l1, l2) = Rule($or L^(#l1)_(#l2)$)
#let LvRuleOrLI(l1, l2) = Inverse(LvRuleOrL(l1, l2))
#let LvRuleOrR(l1, l2) = Rule($or R^(#l1)_(#l2)$)
#let LvRuleOrRI(l1, l2) = Inverse(LvRuleOrR(l1, l2))
#let LvRuleCut(l1, l2) = Rule($"Cut"^(#l1)_(#l2)$)
#let LvRuleImpL(l1, l2) = Rule($->L^(#l1)_(#l2)$)
#let LvRuleImpLI(l1, l2) = Inverse(LvRuleImpL(l1, l2))
#let LvRuleImpR(l1, l2) = Rule($->R^(#l1)_(#l2)$)
#let LvRuleImpRI(l1, l2) = Inverse(LvRuleImpR(l1, l2))
#let LvRuleBoxL(l1, l2) = Rule($box L^(#l1)_(#l2)$)
#let LvRuleBoxLI(l1, l2) = Inverse(LvRuleBoxL(l1, l2))
#let LvRuleBoxGL(l1, l2) = Rule($box #LogicGL^(#l1)_(#l2)$)
#let LvRuleBoxGLI(l1, l2) = Inverse(LvRuleBoxGL(l1, l2))
#let LvRuleLift(l1, l2) = Rule($"LU"^(#l1)_(#l2)$)

#let GentzenS = Gentzen(LogicS)
#let GentzenD = Gentzen(LogicD)


$LogicS$ のシークエント計算は @Kus20 で導入された．

主なアイデア：*シークエントにレベルの概念を導入する．*

#definition[
  $Gamma, Delta$ を集合とし，$level = 1,2$ とする．$Gamma seq(level) Delta$ をシークエントの基本単位とする．
]

$seq1$ で $LogicGL$ の計算をやって，必要なら $seq1$ から $seq2$ に持ち上げて，$seq2$ で $Logic("KT")$ の計算をやるイメージ．
*$seq2$ から $seq1$ には戻れない．*

#pagebreak()

ここでは @KK23 の定義をちょっと修正して導入する．

#definition[
  #LogicS のシークエント計算 #GentzenS を以下の規則で定義する．$LvRuleAndL(level, level), LvRuleAndR(level, level), LvRuleOrL(level, level), LvRuleOrR(level, level)$ は省略．

  #grid(
    columns: 2,
    row-gutter: 16pt,
    align: top,
    [
      $ #prooftree(rule(name: LvRuleAx(level), $p seq(level) p$)) $
    ],
    [$ #prooftree(rule(name: LvRuleBotL(level), $bot seq(level)$)) $],

    [$ #prooftree(rule(name: LvRuleWL(level, level), $Gamma seq(level) Delta$, $A, Gamma seq(level) Delta$)) $],
    [$ #prooftree(rule(name: LvRuleWR(level, level), $Gamma seq(level) Delta$, $Gamma seq(level) Delta, A$)) $],

    [
      $
        #prooftree(rule(
          name: LvRuleImpL(level, level),
          $A -> B, Gamma seq(level) Delta$,
          $Gamma seq(level) Delta, A$,
          $B, Gamma seq(level) Delta$,
        ))
      $
    ],
    [
      $
        #prooftree(rule(name: LvRuleImpR(level, level), $A, Gamma seq(level) Delta, B$, $Gamma seq(level) Delta, A -> B$))
      $
    ],

    [
      $
        #prooftree(rule(name: LvRuleBoxGL(1, 1), $box Gamma, Gamma, box A seq1 A$, $box Gamma seq1 box A$))
      $
    ],
    [
      $
        #prooftree(rule(name: LvRuleBoxL(2, 2), $A, Gamma seq2 Delta$, $box A, Gamma seq2 Delta$))
      $
    ],
    grid.cell(colspan: 2)[
      $
        #prooftree(rule(name: LvRuleLift(1, 2), $Gamma seq1 Delta$, $Gamma seq2 Delta$))
      $
    ],
  )
]


#pagebreak()

#theorem[$GentzenS$ の証明能力][
  1. $GentzenS proves Gamma seq1 Delta$ iff $LogicGL proves and.big Gamma -> or.big Delta$．
  2. $GentzenS proves Gamma seq2 Delta$ iff $LogicS proves and.big Gamma -> or.big Delta$．
]

#theorem[$GentzenS$ のカット除去定理][
  #GentzenS ではカット除去定理が成立する．正確には，カット規則 $LvRuleCut(level, level)$ を以下のように定義したとき，$#GentzenS + LvRuleCut(level, level) proves Gamma => Delta$ ならば $#GentzenS proves Gamma => Delta$ である．
  $
    #prooftree(rule(name: LvRuleCut(level, level), $Gamma_1, Gamma_2 seq(level) Delta_1, Delta_2$, $Gamma_1 seq(level) Delta_1, A$, $A, Gamma_2 seq(level) Delta_2$))
  $
]

#pagebreak()

$LogicD$ のシークエント計算は @KKIM25 で導入された．
基本のアイデアは $LogicS$ と同じで，シークエントに*3個* #footnote[実際には2つのレベルの体系もあるが，それはカット除去が成立しないなどあまり良い性質を持たず，今回の内容では使わないので割愛．]のレベルを入れる．

#definition[
  $LogicD$ のシークエント計算 #GentzenD は，#GentzenS の $LvRuleBoxGL(1, 1)$ と $LvRuleBoxL(2, 2)$ 規則以外を $level = 1, 2, 3$ に適当に拡張するしたうえで，更に $LvRuleLift(2, 3)$ を追加して得られる．
  $
    #prooftree(rule(name: LvRuleLift(2, 3), $box Gamma seq2 box Delta$, $box Gamma seq3 box Delta$))
  $
]

#pagebreak()

#theorem[$GentzenD$ の証明能力][
  1. $GentzenD proves Gamma seq1 Delta$ iff $LogicGL proves and.big Gamma -> or.big Delta$．
  2. $GentzenD proves Gamma seq2 Delta$ iff $LogicS proves and.big Gamma -> or.big Delta$．
  3. $GentzenD proves Gamma seq3 Delta$ iff $LogicD proves and.big Gamma -> or.big Delta$．
]

#theorem[$GentzenD$ のカット除去定理][
  $#GentzenD + LvRuleCut(level, level) proves Gamma => Delta$ ならば $#GentzenS proves Gamma => Delta$ である．
]

== 今回の研究のモチベーション

#text(size: 1.125em)[
  モチベーション：様相論理のシークエント計算を $GentzenS$ や $GentzenD$ を上手く @YS17 の手法と同じように埋め込める*命題論理*のシークエント計算が作れるのでは？
]

元々は @Pet23 が $LogicS$ のシークエント計算を命題論理に埋め込む研究を行っていたが，しかしその証明を精査するとやや不備があったので，証明を修正した．

= 結果

== $LogicSPL$

#let GentzenSPL = $Gentzen(LogicSPL)$
#let GentzenDPL = $Gentzen(LogicDPL)$

Solovayの命題論理 $LogicSPL$ のシークエント計算 $GentzenSPL$ にもレベル付けされた $seq(level)$ を導入する．

#definition[$GentzenSPL$][
  $Gamma seq(level) Delta$ は *集合*ベースのシークエントとする: $level = 1, 2$．
  $LvRuleAndL(level, level), LvRuleAndR(level, level), LvRuleOrL(level, level), LvRuleOrR(level, level)$ などは省略．

  #struct[
    $0 <= k$ と論理式 $C_0 -> D_0, ..., C_n -> D_n$ は任意として，前提が $2^k$ 個の $->$ 規則を導入する．
    $
      #prooftree(rule(
        name: $LvRuleImpR(1, 1)$,
        $\[ Delta_i, Sigma, \{ C_j -> D_j \}_(j < n), A seq1 B, Gamma_i \]_(i < 2^k)$,
        $Sigma, \{C_j -> D_j\}_(j < n) seq1 A -> B$,
      ))
    $
    ここで $0 <= k$ であり，$i < 2^k$ に対して，$Delta_i := { D_j : chevron.l i chevron.r^k_i = 1 }$，$Gamma_i := { C_j : chevron.l macron(i) chevron.r^k_i = 1 }$ とする．
  ]
  #grid(
    columns: 2,
    row-gutter: 16pt,
    align: top,
    [
      $
        #prooftree(rule(
          name: $LvRuleImpL(2, 2)$,
          $Gamma seq2 Delta, A$,
          $B, Gamma seq2 Delta$,
          $A -> B, Gamma seq2 Delta$,
        ))
      $
    ],
    [
      $
        #prooftree(rule(name: LvRuleLift(1, 2), $Gamma seq1 Delta$, $Gamma seq2 Delta$))
      $
    ],
  )
]

#pagebreak()

#theorem[@Pet23 @Nog26][
  $GentzenSPL proves Gamma seq(level) Delta$ iff $GentzenS proves Gamma^visserTr seq(level) Delta^visserTr$
]

$LogicSPL := { A in Fml_upright("P") : GentzenSPL proves seq2 A}$ と定めれば，実際 $LogicS$ が $visserTr$-変換によって様相同伴になる命題論理を見つけたと言える．

#corollary[@Nog26][
  $GentzenSPL$ はカット除去が成立する．そうでなければ $GentzenS$ もカット除去出来ないことになる．
]

== $LogicSPL$ についてのいくつかの注意

@Pet23 の証明は誤っていると考えられる．

致命的な問題点は $LogicS$ のシークエント計算を*多重集合*ベースで考えている点である．
この体系では，縮約や逆転などは高さを保って行えないはずだが，しかし彼の先行研究では明らかにhpで行ってしまっており，帰納法が成立していない箇所がある．

この問題が起こらないように自分の体系では*集合*ベースで考えて修正している．

#remark[
  多重集合ベースのシークエント計算で @Kus20 ではカット除去を具体的な手続きとして与えていたが，集合ベースの #GentzenS では意味論的に与えられている（頑張れば出来るかもしれないが）．

  $LogicSPL$ から $LogicS$ への埋め込みではカット除去に依拠しているので，それ故にこの埋め込みは構成的ではなくなっている．
]

#pagebreak()

この発表では特に注意していないが，非古典の命題論理へ埋め込む関係上，命題論理側の論理結合子は $and, or, ->$ をプリミティヴに持つ．

埋め込みを忠実に行うためには，様相論理側の言語も $and, or, ->$ を入れ，かつシークエント計算にもそれらの規則を入れなければならない．

つまり，*論理結合子の選択が非常にセンシティヴな問題になっている．*

== $LogicDPL$


Japaridzeの命題論理 $LogicDPL$ のシークエント計算 $GentzenDPL$ も同様のアイデアを取る．

とても大雑把に言って，様相論理 $box A$ は命題論理では $B -> A$ だと思える観察から，以下の規則を足せば良い．

#definition[$GentzenDPL$][
  #GentzenSPL を $level = 1, 2, 3$ に適当に拡張して，以下 $LvRuleLift(2, 3)$ を足したシークエント計算を $GentzenDPL$ と定める．
  $
    #prooftree(rule(
      name: $LvRuleLift(2, 3)$,
      $\{A_j -> B_j\}_(j < n), Gamma seq2 \{C_j -> D_j\}_(j < m)$,
      $\{A_j -> B_j\}_(j < n), Gamma seq3 \{C_j -> D_j\}_(j < m)$,
    ))
  $
]

#pagebreak()

証明は #GentzenS の場合とほとんど同じようにやればよい．

#theorem[@Nog26][
  $GentzenDPL proves Gamma seq(level) Delta$ iff $GentzenD proves Gamma^visserTr seq(level) Delta^visserTr$
]

$LogicDPL := { A in Fml_upright("P") : GentzenDPL proves seq3 A}$ と定めれば，実際 $LogicD$ が $visserTr$-変換によって様相同伴になる．

#corollary[@Nog26][
  $GentzenDPL$ はカット除去が成立する．
]

= 結論といくつかの問題

== まとめ

*まとめ*: Solovayの証明可能性論理 $LogicS$ とJaparidzeの証明可能性論理 $LogicD$ に適当に修正したGödel変換によって埋め込める命題論理 $LogicSPL, LogicDPL$ をシークエント計算によって与えた．

以下では今考えている（考えるべき?）問題を提示する．

== 意味論

$LogicSPL, LogicDPL$ 自体の性質はほぼ何もわからない．*特に意味論が無い．*

- $LogicFPL$ はVisserの原論文 (@Vis81) で証明可能性論理として調べられている．
- @Pet23 は $LogicSPL$ に対し，Visserのtail model @Vis84 の対応物を導入し，埋め込み経由で完全性を示している．
- $LogicD$ の意味論は @Bek89 @Bek90 @KKIM25 で与えられており，埋め込み経由で $LogicDPL$ の意味論を議論することは可能．

#problem[
  *埋め込みを経由せずに* $LogicSPL, LogicDPL$ の意味論を直接定義し，完全性を示すことは出来るか？
]

シークエント計算による定義だけでは，今回の $LogicSPL, LogicDPL$ が埋め込みを成立させるだけのad-hocな体系である可能性が排除できない（特に論理結合子の選択が本質的とは思えない）．
せめて意味論的な裏付けが欲しい．

== Hilbert流の体系

$LogicBPL$ と $LogicFPL$ のHilbert流の体系は @SO97 @IKK01 などで研究されている．

#problem[
  $LogicSPL, LogicDPL$ のHilbert流の体系はどのようなものか．
]

- 複数レベルのシークエントを持つシークエント計算で定義しているため，Hilbert流の体系の定義は容易ではない．

*予想*: 単一レベルの含意 $->$ のみの言語ではHilbert流の体系は存在しない．
もしそうなら，複数レベルの含意 $attach(tr: 1, ->), attach(tr: 2, ->), attach(tr: 3, ->)$ を備えた言語の論理とは何か？それらの含意は何を意味するのか？

== 構成的なカット除去

$LogicSPL, LogicDPL$ の埋め込み可能性とカット許容性は，$LogicS, LogicD$ のシークエント計算のカット許容性に依存している．
後者は意味論的な議論で示されているため，今回の結果は純粋に構成的ではない．

#problem[
  $GentzenSPL, GentzenDPL$ に対する，構成的なカット除去アルゴリズムは？
]

== 参考文献

#show bibliography: set text(size: 0.75em)
#bibliography(title: none, "references.yml", style: "elsevier-harvard")
