Require Import HoTT.

Definition Dec A := A + (~A).
Definition DecEq A := forall (x y : A), Dec (x = y).
Definition UIP_refl (A : Type) := forall (x : A) (p : x = x),
                           p = idpath.

Theorem transport_path_concat : forall A (a x y: A)
  (p : x = y) (k : a = x),
  transport (fun z => paths a z) p k = k @ p.
Proof.
  intros. induction p.
  simpl. symmetry. apply concat_p1.
Qed.

(** Basically, if [q : (a,b) = (c,d)], then [fstp q : a = c] and 
[sndp q : b = d] *)

Definition fstp {A} {x y : A * A}
  (p : x = y) : (fst x) = (fst y) := ap fst p.
Definition sndp {A} {x y : A * A}
  (p : x = y) : (snd x) = (snd y) := ap snd p.

Theorem transport_prod_path_concat : forall {A} {x y : A * A}
  (q : x = y) (k : fst x = snd x),
  transport (fun z => (fst z = snd z))
            q
            k
  = ((fstp q)^ @ k @ (sndp q)).
Proof.
  intros. induction q. simpl. 
  rewrite concat_1p. rewrite concat_p1. reflexivity.
Qed.

Theorem transport_decpath_concat : forall {A} {x y : A * A}
  (q : x = y) (k : fst x = snd x),
  transport (fun z => (fst z = snd z) + (fst z <> snd z))
            q
            (inl k)
  = inl ((fstp q)^ @ k @ (sndp q)).
Proof.
  intros. rewrite <- transport_prod_path_concat.
  rewrite transport_sum. reflexivity.
Qed.

Theorem transport_decpath_concat' : forall {A} {a b c d : A}
  (q1 : a = c) (q2 : b = d) (k : a = b),
  transport (fun z => (fst z = snd z) + (fst z <> snd z))
            (path_prod (a,b) (c,d) q1 q2)
            (inl k)
  = inl (q1^ @ k @ q2).
Proof.
  intros.  
  rewrite transport_decpath_concat with (q:=path_prod (a, b) (c, d) q1 q2).
  unfold fstp,sndp. 
  rewrite ap_fst_path_prod.
  rewrite ap_snd_path_prod.
  reflexivity.
Qed.

Definition uncurry {A B C} (f: forall (a:A) (b:B), C a b)
  (x : A * B) : C (fst x) (snd x) := match x with
                                       | (a, b) => f a b
                                     end.
Definition concat_p1V {A : Type} {x y : A} (p : x = y) :
  p @ 1^ = p 
  :=
  match p with idpath => 1 end.
Definition concat_1Vp {A : Type} {x y : A} (p : x = y) :
  1^ @ p = p 
  :=
  match p with idpath => 1 end.

Theorem Hedberg : forall A, DecEq A 
  -> UIP_refl A.
Proof.
  intros A H.
  intros x p.
  (** define [z x] = [dec x x] *)
  assert (z := uncurry H); simpl in z.
  (** We need that [(1,p) # (z (x,x)) = z (x,x)] *)
  assert (transport (fun z => (fst z = snd z) + (fst z <> snd z)) (path_prod' 1 p) (z (x,x)) = z (x,x)) as H1.
    {
      apply (apD z (path_prod' 1 p)).
    }
  (** Clearly, [z (x,x)] can only be [inl q] for some [q] *)
  destruct (z (x,x)) as [q | nq]; [| destruct (nq p)].
  (** [p = 1] is the same as [1^ @ p @ q = q] *)
  apply (cancelL q). rewrite concat_p1.
  apply (cancelL 1^). 
    (* we cannot do [rewrite concat_1Vp at 2] *)
    symmetry; rewrite concat_1Vp; symmetry.
  rewrite concat_p_pp.
  (** [1^ @ q @ p = q] iff [inl (1^ @ q @ p) = inl q] *)
  apply (@path_sum_inl _ (x<>x)).
  (** finally, we know that [inl ((1^ @ q) @ p)] is how transport works on a decpath space *)
  rewrite <- (transport_decpath_concat' 1 p q).  
  rewrite H1. reflexivity.
Qed.
