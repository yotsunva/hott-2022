```
Definition UU := Type.
Notation paths := identity.
Definition isprop (A : UU) := forall x y : A , paths x y.
Definition quiz {A : UU} (is : isprop A) (a b : A) (p : paths a b) : paths p (is a b).
```
に続く quiz の証明について考えます。
これは基本的な主張で、HoTT book であれば Lemma 3.3.4 にこれと同様の主張が載っています。
一般に n-type という概念が定義されて、n-type ならば (n+1)-type であることが言えます
（isprop の定義と (-1)-type であることの定義が異なる可能性があるので、
この証明が quiz の証明と直接関わっているとは限りませんが）。
contractible であることは (-2)-type であることと同値で、
proposition であることは (-1)-type であることと同値で、
set であることは 0-type であることと同値です。

HoTT book では用意した道具を使って示していますが、
ここでは直接示すことにします。
おそらく path induction を二回使うことになると思います（p に関する帰納法と、isprop から出る path に関する帰納法）。

#### p に関する帰納法を先に使う方針
p に関する帰納法を使うと、  
(is : isprop A) (a b : A) (p : a = b) から p = (is a b) の項を作る問題が  
(is : isprop A) (a : A) から refl = (is a a) の項を作る問題に帰着されます。  
is a a が refl である場合に帰着させたいですが、帰納法を使うためには is a a のままだと一般性が足りません
（(based) path induction を使う場合、少なくとも片方の端点を自由に動かせるようにする必要があります）。
そこで、  
(is : isprop A) (a c : A) (q : a = c) (x : q = is a c) から refl = (is a a) の項を作る問題を解くことにします。  
これが解ければ、c := a , q := is a a , x := refl とすることで前の問題が解けます。  
q に関する帰納法を使うと、  
(is : isprop A) (a : A) (e : refl = is a a) から refl = (is a a) の項を作る問題に帰着されます。
これは e を使えば解けます。

Coq では例えば以下のように書くことができます（都合上、上の説明における a と c が部分的に逆になっています）。
```
Proof.
  destruct p.
  remember a as c.
  remember (is c a) as q eqn:e.
  destruct q , e.
  reflexivity.
Defined.
```
#### isprop から出る path に関する帰納法を先に使う方針
(is : isprop A) (a b : A) (p : a = b) から p = (is a b) の項を作る問題を解くために、  
(is : isprop A) (a b c : A) (p : a = b) (q : a = c) (e : q = is a c) から p = (is a b) の項を作る問題を解くことにします。  
後者を解けば、c := a , q := is a a , e := refl とすることで前者を解くことができます。
q に関する帰納法を使うと
(is : isprop A) (a b : A) (p : a = b) (e : refl = is a a) から p = (is a b) の項を作る問題に帰着されます。  
さらに p に関する帰納法を使うと、  
(is : isprop A) (a b : A) (e : refl = is a a) から refl = (is a a) の項を作る問題に帰着されます。  
これは x を使えば解けます。

Coq では例えば以下のように書くことができます。
（Coq では、destruct すると path induction のために必要な一般化を多少やってくれます。
例えば q : a = a を destruct する部分では、q : a = c に一般化してから帰納法を使ってくれています）：
```
Proof.
  remember (is a a) as q eqn:e.
  destruct q , p , e.
  reflexivity.
Defined.
```
