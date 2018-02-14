Require Import HoTT.
Require Import UnivalenceAxiom.

Definition UIP := 
  forall (A : Type) (x y:A) (p q : x = y),
    p = q.
Definition UIP_refl := 
  forall (A : Type) (x : A) (p : x = x),
    p = idpath.
Definition K :=
  forall A (x : A) (P : x = x -> Type),
    P (idpath x) -> forall (h : x = x), P h.

(* Groupoid model shows that K/UIP are not derivable in ITT *)

Theorem UIPisUIPrefl : UIP <-> UIP_refl.
Proof.
  split.
    intro U. unfold UIP_refl.
    unfold UIP in U.
    intros A x p.
    apply (U A x x p idpath).
 
    intro Ur. intros A x y p q.
    induction q. apply Ur.
Qed.

Theorem UIP2K : UIP -> K.
Proof.
  intro U.
  intros A x P H h.
  rewrite <- (U A x x idpath h). exact H.
Qed.

Theorem K2UIP : K -> UIP.
Proof.
  intro k. intros A x y p q.
  destruct p. 
  (* Set Printing Implicit. <-- to see why case analysis on q does not work *)
  (* destruct q. *)
  apply (k A x (fun m => idpath = m) idpath).
Qed.

Definition coerce : forall A B, (A = B) -> A -> B :=
  fun A B p a => match p with
                   | idpath => a
                 end.

Lemma coerce_refl : forall A x, coerce A A idpath x = x.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma coerce_id : K -> forall (e : Bool = Bool), coerce Bool Bool e true = true.
Proof.
  intros K e.
  apply (K Type Bool (fun p => coerce Bool Bool p true = true) (coerce_refl Bool true) e).
Qed.
