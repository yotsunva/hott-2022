途中で失敗したので無視してください。

エラーと変更点は以下の通りです：
- `Implicit Arguments pair [ B E ].` で `Syntax error: illegal begin of vernac.` というエラーが出る問題。
  - `Arguments pair {_ _}.` に変更。Coq の仕様が変わったんだと思います。
- `eqweqmap` の定義で `Once notations are expanded, the resulting constructor
identity_refl (in type identity) is expected to be applied
to 1 argument while it is actually applied to no arguments.` というエラーが出る問題。
  - 冒頭に `Set Asymmetric Patterns.` を追加（代わりに `idpath` を `idpath _` と書き換えても解決できる）。
- `weqindelim` の定義で `Found type "UU" where "?B" was expected.` というエラーが出る問題。
  - 冒頭に `Set Universe Polymorphism.` を追加。この変更は後のエラーにも効いてくると思います。
  おそらく universe のレベルのチェックを無効化して実行することを想定して書かれたコードですが、
  そのチェックを無効化すると矛盾を導ける (Girard's paradox) ので、ここでは無効化せずに対処しようと思います。
- `isweqpitftototalspace` の証明で `Unused introduction patterns: a a'
[unused-intro-pattern,tactics]` という警告が出る問題。
  - 証明の後半の `destruct a as [ a a' ].` を削除。前半の証明からコピペするときに消し忘れたのだと思います。
- `isaxiomunivalence` の型について `The term "isweqeqweqmap" has type "Type"
while it is expected to have type "UU"
(universe inconsistency: Cannot enforce
max(Set, JsCoq.2769, JsCoq.2770+1) <= Set).` のようなエラーが出る問題。
  - `isofhlevel` の定義において、引数 `( A : UU )` の型を `( A : Type )` のように変更。
  UU と書くと universe のレベルの調整がうまくいきませんが、Type と書くとなぜかうまくいきます
  （あちこちで UU と書くとそれらのレベルが統一されたりするんですかね…）。
  これも universe のレベルのチェックに関する問題です。
  面倒なので、`UU` を全て `Type` に書き換えました
  （レベルのチェックを無効化する方が手っ取り早かったかもしれませんが）。
- `UU` を全て `Type` に書き換えると `triangle` の証明でエラーが出る問題。
  - `weqind` の定義において、`A B` の型を `(A B : Type)` のように明示。
      明示しないと `(A B : Set)` だと思われるようです。
- `UU` を全て `Type` に書き換えると `eqweqmaptriangle` の証明でエラーが出る問題。
  - ?
- `isofhlevelSnhn` の証明で `In environment
A, B : total (fun x : UU => isofhlevel 0 x)
Unable to unify ...` のようなエラーが出る問題。
  - ?
