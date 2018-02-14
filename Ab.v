Require Import HoTT.
(*  Suppose we have a function f : C -> D -> E
  and paths c = c' in C, d = d' in D.
  Then there should be a path between f c d and f c' d'.

  In fact, we can construct such path in two ways.
 *)

Definition ap2 {C D E : Type} (f : C -> D -> E)
           {c c' : C} {d d' : D} (p : c = c') (q : d = d')
           : f c d = f c' d'
  := (ap (fun c => f c d) p) @ (ap (f c') q).

(* equivalent definition *)
Definition ap2' {C D E : Type} (f : C -> D -> E)
           {c c' : C} {d d' : D} (p : c = c') (q : d = d')
           : f c d = f c' d'
  := (ap (f c) q)  @ (ap (fun c => f c d') p).

(* We can show that they are equivalent! *)

Lemma ap2_is_ap2' {A : Type} {m : A} (k l : m = m) : forall (p q : k = l),
  ap2 (fun x y => x @ y) p q =
  ap2' (fun x y => x @ y) p q.
Proof.
  intros. induction p. unfold ap2. simpl.
  rewrite concat_1p.
  unfold ap2'. simpl.
  rewrite concat_p1.
  reflexivity.
Qed.

(* For a specific case of c = c' = idpath and
   d = d' = idpath (and, hence, 
   p : idpath = idpath, q : idpath = idpath)
   it turns out that

   [ap2 (fun x y => x @ y) p q = p @ q]
*)

Lemma ap_id1 {A : Type} {m : A} (k l : m = m) (p : k = l) 
  : ap (fun x => x @ 1) p 
    = (concat_p1 k) @ (p @ (concat_p1 l)^).
Proof.
  induction p. simpl.
  rewrite concat_1p. symmetry. apply concat_pV.
Qed.

Lemma ap_id1'' {A : Type} {m : A} (k l : m = m) (p : k = l) 
  : ap (fun x => x @ 1) p 
  = ((concat_p1 k) @ p) @ (concat_p1 l)^.
Proof.
  induction p. simpl.
  rewrite concat_pp_p.
  rewrite concat_1p. symmetry. apply concat_pV.
Qed.

Lemma ap_id2 {A : Type} {m : A} (k l : m = m) (p : k = l) 
  : ap (fun x => 1 @ x) p 
    = (concat_1p k) @ p @ (concat_1p l)^.
Proof.
  induction p. simpl.
  rewrite concat_p1. symmetry. apply concat_pV.
Qed.


Lemma t1 {A : Type} {m : A} : forall (p q : (idpath m) = (idpath m)),
  ap2 (fun x y => x @ y) p q = p @ q.
Proof.
  intros. unfold ap2. rewrite ap_id1.
  rewrite ap_id2. simpl.
  repeat (rewrite concat_p1).
  repeat (rewrite concat_1p).
  reflexivity.
Qed.

Lemma t2 {A : Type} {m : A} : forall (p q : (idpath m) = (idpath m)),
  ap2' (fun x y => x @ y) p q = q @ p.
Proof.
  intros. unfold ap2'. rewrite ap_id2.
  rewrite ap_id1. simpl.
  repeat (rewrite concat_p1).
  repeat (rewrite concat_1p).
  reflexivity.
Qed.

Theorem EckmannHilton {A : Type} :
  forall (m : A) (p q : (idpath m) = (idpath m)), p @ q = q @ p.
Proof.
  intros. rewrite <- t1. rewrite <- t2.
  apply (ap2_is_ap2' _ _ p q). 
Qed.
