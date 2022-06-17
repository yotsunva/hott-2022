### path induction について
`a : A` に対して loop space `a = a` が可縮であることは、path induction では示せません（HoTT において、`base : S1` に関して `base = base` は整数がなす型 `Z` と同値です）。

一方で、(based) path space fibration の全空間 `Σ(x : A). a = x` が可縮であることは示せます。例えば HoTT において、`base = base` の項として `refl` と `loop` は等しくないですが、`Σ(x : S1). base = x` の項として `(base , refl)` と `(base , loop)` は等しいです（fiber は Z と同値で可縮ではないが、全空間は螺旋状で可縮）。

(based) path induction は
「関数 `((x , p) : Σ(x : A). a = x) → C (x , p)` を定めたければ、`(a , refl)` の行き先を定めれば良い」
のように解釈することもできます。

重要なのは、「goal となる `C (x , p)` が各 `(x , p)` に対して定まっている必要がある」という点です。ループ `l : a = a` に対して、
`C (a , refl) ≡ (refl = refl)`
`C (a , l) ≡ (refl = l)`
となるように `C` を「`Σ(x : A). a = x` 全域で」定義できれば path induction を使って `refl = l` が示せますが、そのような `C` は一般には作れません。
