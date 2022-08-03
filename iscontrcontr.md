準備
```
Set Asymmetric Patterns.

Notation UU := Type.

Inductive total { B : UU } ( E : B -> UU ) : UU := pair ( x : B ) ( y : E x ).
Arguments pair {_ _}.

Definition pr1 { B : UU } { E : B -> UU } : total E -> B := fun z => match z with pair x y => x end. 
Definition pr2 { B : UU } { E : B -> UU } ( s : total E ) : E ( pr1 s ) := match s with pair x y => y end. 

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

Lemma isofhlevelntoSn ( n : nat ) : forall A : UU, isofhlevel n A -> isofhlevel ( S n ) A . 
Proof.
  induction n.
  exact (fun A => iscontrtoisaprop).
  intros A f a b.
  exact (IHn _ (f a b)).
Defined.
```
証明
```
Axiom depfunextfun : forall {B : UU} {E : B -> UU} (f g : forall x : B, E x) , (forall x : B, paths (f x) (g x)) -> paths f g.

Lemma iscontrcontr {A : UU} (is : iscontr A) : iscontr (iscontr A).
Proof.
  assert (isofhlevel 2 A).
  apply isofhlevelntoSn , isofhlevelntoSn.
  exact is.
  refine (pair is _).
  intro.
  destruct is , b.
  destruct (y x0).
  assert (paths y y0).
  apply depfunextfun.
  intro.
  exact (pr1 (X _ _ _ _)).
  destruct H.
  reflexivity.
Defined.
```
