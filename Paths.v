Require Import HoTT.

Definition unit_path : forall (x y :Unit), x = y
 := fun x y => match x, y with tt,tt => 1 end.
(* Proof. *)
(*   intros x y. *)
(*   destruct x. destruct y. exact idpath. *)
(* Qed. *)
Lemma unit_hprop : forall (x y: Unit) (p : x=y), 
                     (unit_path x y) = p.
Proof. 
  intros x y. induction p. destruct x. simpl.
  reflexivity.
Qed.

Theorem t281 : forall (x y : Unit) (p q : x = y), p = q. 
Proof.
  induction p. intro q. transitivity (unit_path x x).
  symmetry. apply unit_hprop. apply unit_hprop.
Qed.

Definition path_empt : forall (p q: Type), 
  p = Empty -> q = Empty -> p = q :=
fun (p q : Type) (H1 : p = Empty) (H2 : q = Empty) =>
let t := Empty in
match H1 in (_ = y) return (q = y -> p = q) with
| 1 => fun H3 : q = p => H3^
end H2.

(* Below we want to characterise the path space of the cartesian
product, in terms of the paths spaces of its constituents *)

(* The theorem is 

  [(x = y) <~> ((fst x = fst y) * (snd x = snd y))]

We can easily define a function 
f : x = y -> ((fst x = fst y) * (snd x = snd y))
 *)

Definition f {A B : Type} {x y : A * B} :
             x = y -> (fst x = fst y) * (snd x = snd y)
  := fun p => (ap fst p, ap snd p).

(* Then we use [ap2] (defn below) to write out an inverse of [f] *)

Definition ap2 {C D E : Type} (f : C -> D -> E)
           {c c' : C} {d d' : D} (p : c = c') (q : d = d')
           : f c d = f c' d'
  := (ap (fun c => f c d) p) @ (ap (f c') q).

(* equivalent definition *)
Definition ap2' {C D E : Type} (f : C -> D -> E)
           {c c' : C} {d d' : D} (p : c = c') (q : d = d')
           : f c d = f c' d'
  := (ap (f c) q)  @ (ap (fun c => f c d') p).

Definition g {A B : Type} {x y : A * B} :
             (fst x = fst y) * (snd x = snd y) -> x = y
  := fun p => ap2 (fun a b => (a,b)) (fst p) (snd p).

(* Finally, we can prove the characterization *)
Theorem id_space_prod :  forall {A B : Type} (x y : A * B), 
  (x = y) <~> ((fst x = fst y) * (snd x = snd y)).
Proof.
  intros A B x y.
  split with (equiv_fun := f).
  Check BuildIsEquiv.
  refine (BuildIsEquiv _ _ f g _ _ _).
  (* f . g = id *)
  unfold Sect. intro q.
  destruct q as [q1 q2].
  (* we cannot do induction on q1 or q2 at this point, as we don't
   have free endpoints. however, we use the induction on the product
   type to assume that [x] and [y] are pairs themselves. this way we
   can get rid of the dependency in the endpoints *)
  destruct x as [x1 x2]; destruct y as [y1 y2]; simpl in *.
  induction q1; induction q2.
  unfold g. unfold f. simpl. reflexivity.
  (* g . f = id *)
  unfold Sect; intro p.
  unfold f. unfold g. simpl. unfold ap2.
  induction p. simpl. reflexivity.
  (* adjointness *)
  intro p. simpl. induction p. simpl. reflexivity.
Qed.


(** Eckmann-Hilton *)

Lemma t1 {A : Type} {m n : A} : forall (p q : (idpath m) = (idpath m)),
  ap2 (fun x y => x @ y) p q = p @ q.
Proof.
  intros p q.
  unfold ap2.

  (* Here we need to prove that 
     
     - [ap (fun x => x @ 1) p = p]
     - [ap (fun x => 1 @ x) p = p]
  
     Once again, we cannot do this directly, as [p] doesn't have 
     free endpoints *)
  Check (ap idmap p = p).
  Check (ap (fun x => x @ 1) p).
  Check p.
  Check ((fun y => 1 @ y) = idmap).
  Abort.


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

Lemma t3 {A : Type} {m : A} (k l : m = m) : forall (p q : k = l),
  ap2 (fun x y => x @ y) p q =
  ap2' (fun x y => x @ y) p q.
Proof.
  intros. induction p. unfold ap2. simpl.
  rewrite concat_1p.
  unfold ap2'. simpl.
  rewrite concat_p1.
  reflexivity.
Qed.

Theorem EckmannHilton {A : Type} :
  forall (m : A) (p q : (idpath m) = (idpath m)), p @ q = q @ p.
Proof.
  intros. rewrite <- t1. rewrite <- t2.
  rewrite t3. reflexivity.
Qed.

Definition whR {A : Type} {a b c : A} 
  {p q : a = b} (al : p = q) (r : b = c) : p @ r = q @ r
  := match r with
       | 1 => ap (fun x => x @ 1) al
     end.
Definition whL {A : Type} {a b c : A} 
  {r s : b = c} (p : a = b) (be : r = s)  : p @ r = p @ s.
induction p; apply (ap (fun x => 1 @ x) be). Qed.
  (* := match p with *)
  (*      | 1 => ap (fun x => 1 @ x) be *)
  (*    end. *)
