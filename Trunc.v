From HoTT Require Export HoTT HIT.Truncations.
Require Import HitTactics.

(* Encode-decode for set truncations *)
Instance Trunc_recursion A n : HitRecursion (Trunc n A) := {
  indTy := _; recTy := _; 
  H_inductor := @Trunc_ind n A; H_recursor := @Trunc_rec n A }.

Section coding.
Context `{Univalence}.
Variable A : Type.
Notation "'||' X '||₀'" := (Trunc 0 X).
Definition code : ||A||₀ -> ||A||₀ -> hProp.
Proof.
hinduction. intro a.
hinduction. intro b.
unshelve eapply BuildhProp.
- exact (Trunc -1 (a = b)).
- apply _.
Defined.

Definition r : forall (x : ||A||₀), code x x.
Proof.
hinduction. intro a.
exact (tr idpath).
Defined.

Definition encode : forall (x y : ||A||₀), x = y -> code x y
  := fun x y p => transport (fun z => code x z) p (r x).

Definition decode : forall (x y : ||A||₀), code x y -> x = y.
Proof.
hinduction. intro a.
hinduction. intro b.
hinduction.
exact (ap tr).
Defined.

Lemma decode_encode (u v : ||A||₀) : forall (p : u = v),
  decode u v (encode u v p) = p.
Proof.
induction p.
simpl.
hinduction u. reflexivity.
Defined.

Lemma encode_decode : forall (u v : ||A||₀) (c : code u v),
    encode u v (decode u v c) = c.
Proof.
hinduction. intro a.
hinduction. intro b. intro c. apply path_ishprop. 
Defined.

Lemma hset_tr_prop_id_1 (a b : A) :
  (@tr 0 _ a) = (@tr 0 _ b) -> Trunc -1 (a = b).
Proof.
  intro p. apply (encode _ _ p).
Defined.

Lemma hset_tr_prop_id_2 (a b : A) :
  Trunc (-1) (a = b) -> (@tr 0 _ a) = tr b.
Proof.
  intro p. apply (decode (tr a) (tr b) p).
Defined.

Lemma hset_tr_prop_id (a b : A) :
  (@tr 0 _ a) = (@tr 0 _ b) <~> Trunc -1 (a = b).
Proof.
  esplit with (hset_tr_prop_id_1 a b).
  apply isequiv_biinv. unfold BiInv. split.
  - esplit with (hset_tr_prop_id_2 a b).
    intro x. apply decode_encode.
  - esplit with (hset_tr_prop_id_2 a b).
    intro x. unfold hset_tr_prop_id_1. unfold hset_tr_prop_id_2.
    apply (encode_decode (tr a) (tr b) x).
Defined.

End coding.

