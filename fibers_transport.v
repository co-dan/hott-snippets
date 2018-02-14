Require Import HoTT.
Require Import HoTT.Basics.PathGroupoids.

Theorem fibers_equiv : forall (X : Type) (E : X -> Type) (x y : X)
                              (f : x = y), E(x) <~> E(y).
Proof.
  intros.
  split with (equiv_fun:=(transport E f)).
  simple refine (BuildIsEquiv _ _ _ (transport E (f^)) _ _ _).  
  intro. induction f. simpl. reflexivity.
  intro. induction f. simpl. reflexivity.
  intro. simpl. induction f. simpl. reflexivity.
Qed.

Theorem equiv_fibers : forall (X : Type) (E1 E2 : X -> Type),
    ((sig E1) <~> (sig E2)) -> forall x, E1(x) <~> E2(x).
Proof.
  intros X E1 E2 h. intro x.
  
