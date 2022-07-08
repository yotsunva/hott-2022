文献で示されている `iscontrunit` と `isofhlevelntoSn` を使うと `Lemma ttpathpath (p q : paths tt tt) : paths p q.` が示せます。

```
Set Asymmetric Patterns.

Notation UU := Type.

Inductive total { B : UU } ( E : B -> UU ) : UU := pair ( x : B ) ( y : E x ).
Arguments pair {_ _}.

Notation paths := identity.
Notation idpath := identity_refl.

Definition pathsinv { A : UU } { a b : A } ( f : paths a b ) : paths b a.
Proof.
  destruct f. apply idpath. 
Defined.

Definition pathscomp { A : UU } { a b c : A } ( f : paths a b ) ( g : paths b c ) : paths a c.
Proof.
  destruct f. assumption.
Defined.

Definition iscontr ( A : UU ) := total ( fun center : A => forall b : A, paths center b ).

Definition isofhlevel (n : nat) : UU -> UU.
Proof.
  induction n.
  exact (fun A => iscontr A).
  exact (fun A => forall a b : A, IHn (paths a b)).
Defined.
(* 文献の定義と実質的に同じ *)

Lemma iscontrtoisaprop { A : UU } ( is : iscontr A ) : isofhlevel 1 A.
Proof.
  destruct is.
  simpl.
  intros.
  refine (pair (pathscomp (pathsinv (y a)) (y b)) _).
  intros.
  destruct b0 , (y a).
  exact (idpath _).
Defined.
(* 文献では univalence を使って示されているが、公理なしで示せる *)

Lemma isofhlevelntoSn ( n : nat ) : forall A : UU, isofhlevel n A -> isofhlevel ( S n ) A . 
Proof.
  induction n.
  simpl.
  intro.
  exact iscontrtoisaprop.
  simpl.
  intros A f a b.
  exact (IHn _ (f a b)).
Defined.

Lemma iscontrunit : iscontr unit.
Proof.
  split with tt. intro b. destruct b. apply idpath.
Defined.

Lemma ttpathpath (p q : paths tt tt) : paths p q.
Proof.
  destruct ((isofhlevelntoSn _ _ (isofhlevelntoSn 0 _ iscontrunit)) _ _ p q).
  exact x.
Defined.
```
