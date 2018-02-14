Require Import HoTT HitTactics.
Require Import Circ.
(* This is a non-truncated definition of a free monoid *)
(* In this file we will prove that this construction does not give rise to a h-set. *)
Section monoid.
Variable A : Type.

Private Inductive M : Type :=
| el : A -> M
| e  : M
| op : M -> M -> M.

Infix "+" := op. (* left assoc *)
Notation "0" := e.
Coercion el : A >-> M.

Axiom assoc : forall (a b c : M), 
 (a + b) + c = a + (b + c).
Axiom ident_l : forall (a : M),
  0 + a = a.
Axiom ident_r : forall (a : M),
  a + 0 = a.

Fixpoint M_ind
  (Y : M -> Type)
  (AY : forall a : A, Y (el a))
  (eY : Y 0)
  (opY : forall x y : M, Y x -> Y y -> Y (x + y))
  (opY_assoc : forall x y z : M, forall (xY : Y x) (yY : Y y) (zY : Y z),
      assoc x y z # opY _ _ (opY _ _ xY yY) zY = opY _ _ xY (opY _ _ yY zY))
  (opY_ident_l : forall (x : M) (xY : Y x), 
      ident_l x # opY _ _ eY xY = xY)
  (opY_ident_r : forall (x : M) (xY : Y x), 
      ident_r x # opY _ _ xY eY = xY)
  (x : M)
  {struct x}
  : Y x :=
  (match x return _ -> _ -> _ -> Y x with
    | el a => fun _ _ _ => AY a
    | e    => fun _ _ _ => eY
    | e1 + e2 => fun _ _ _ => 
       opY e1 e2 (M_ind Y AY eY opY opY_assoc opY_ident_l opY_ident_r e1) 
                 (M_ind Y AY eY opY opY_assoc opY_ident_l opY_ident_r e2)
  end) opY_assoc opY_ident_l opY_ident_r.

Axiom M_ind_beta_assoc : forall
  (Y : M -> Type)
  (AY : forall a : A, Y (el a))
  (eY : Y 0)
  (opY : forall x y : M, Y x -> Y y -> Y (x + y))
  (opY_assoc : forall x y z : M, forall (xY : Y x) (yY : Y y) (zY : Y z),
      assoc x y z # opY _ _ (opY _ _ xY yY) zY = opY _ _ xY (opY _ _ yY zY))
  (opY_ident_l : forall (x : M) (xY : Y x), 
      ident_l x # opY _ _ eY xY = xY)
  (opY_ident_r : forall (x : M) (xY : Y x), 
      ident_r x # opY _ _ xY eY = xY)
  (x y z : M),
  apD (M_ind Y AY eY opY opY_assoc opY_ident_l opY_ident_r) (assoc x y z)
  = opY_assoc x y z (M_ind Y AY eY opY opY_assoc opY_ident_l opY_ident_r x)
                    (M_ind Y AY eY opY opY_assoc opY_ident_l opY_ident_r y)
                    (M_ind Y AY eY opY opY_assoc opY_ident_l opY_ident_r z).

Axiom M_ind_beta_ident_l : forall
  (Y : M -> Type)
  (AY : forall a : A, Y (el a))
  (eY : Y 0)
  (opY : forall x y : M, Y x -> Y y -> Y (x + y))
  (opY_assoc : forall x y z : M, forall (xY : Y x) (yY : Y y) (zY : Y z),
      assoc x y z # opY _ _ (opY _ _ xY yY) zY = opY _ _ xY (opY _ _ yY zY))
  (opY_ident_l : forall (x : M) (xY : Y x), 
      ident_l x # opY _ _ eY xY = xY)
  (opY_ident_r : forall (x : M) (xY : Y x), 
      ident_r x # opY _ _ xY eY = xY)
  (x : M),
  apD (M_ind Y AY eY opY opY_assoc opY_ident_l opY_ident_r) (ident_l x)
  = opY_ident_l x (M_ind Y AY eY opY opY_assoc opY_ident_l opY_ident_r x).

Axiom M_ind_beta_ident_r : forall
  (Y : M -> Type)
  (AY : forall a : A, Y (el a))
  (eY : Y 0)
  (opY : forall x y : M, Y x -> Y y -> Y (x + y))
  (opY_assoc : forall x y z : M, forall (xY : Y x) (yY : Y y) (zY : Y z),
      assoc x y z # opY _ _ (opY _ _ xY yY) zY = opY _ _ xY (opY _ _ yY zY))
  (opY_ident_l : forall (x : M) (xY : Y x), 
      ident_l x # opY _ _ eY xY = xY)
  (opY_ident_r : forall (x : M) (xY : Y x), 
      ident_r x # opY _ _ xY eY = xY)
  (x : M),
  apD (M_ind Y AY eY opY opY_assoc opY_ident_l opY_ident_r) (ident_r x)
  = opY_ident_r x (M_ind Y AY eY opY opY_assoc opY_ident_l opY_ident_r x).

Definition M_rec
  (Y : Type)
  (AY : A -> Y)
  (eY : Y)
  (opY : Y -> Y -> Y)
  (opY_assoc : forall x y z : Y, 
      opY (opY x y) z = opY x (opY y z))
  (opY_ident_l : forall (x : Y), 
      opY eY x = x)
  (opY_ident_r : forall (x : Y), 
      opY x eY = x)
  (x : M) : Y.
Proof.
simple refine (M_ind (fun _ => Y) 
                AY
                eY
                (fun _ _ => opY) _ _ _ x); simpl.
- intros ??? a b c.
  etransitivity. apply transport_const. apply opY_assoc.
- intros ? a.
  etransitivity. apply transport_const. apply opY_ident_l.
- intros ? a.
  etransitivity. apply transport_const. apply opY_ident_r.
Defined.


Definition M_rec_beta_assoc : forall
  (Y : Type)
  (AY : A -> Y)
  (eY : Y)
  (opY : Y -> Y -> Y)
  (opY_assoc : forall x y z : Y, 
      opY (opY x y) z = opY x (opY y z))
  (opY_ident_l : forall (x : Y), 
      opY eY x = x)
  (opY_ident_r : forall (x : Y), 
      opY x eY = x)
  (x y z : M),
  ap (M_rec Y AY eY opY opY_assoc opY_ident_l opY_ident_r) (assoc x y z)
  = opY_assoc (M_rec Y AY eY opY opY_assoc opY_ident_l opY_ident_r x)
              (M_rec Y AY eY opY opY_assoc opY_ident_l opY_ident_r y)
              (M_rec Y AY eY opY opY_assoc opY_ident_l opY_ident_r z).
Proof.
  intros.
  eapply (cancelL (transport_const _ _)).
  etransitivity. symmetry.
   apply apD_const.
  unfold M_rec. simpl. 
  change (fun x0 : M =>
   M_ind (fun _ : M => Y) AY eY (fun _ _ : M => opY)
     (fun (x1 y0 z0 : M) (a b c : Y) =>
      transport_const (assoc x1 y0 z0) (opY (opY a b) c) @ opY_assoc a b c)
     (fun (x1 : M) (a : Y) =>
      transport_const (ident_l x1) (opY eY a) @ opY_ident_l a)
     (fun (x1 : M) (a : Y) =>
      transport_const (ident_r x1) (opY a eY) @ opY_ident_r a) x0)
  with (M_ind (fun _ : M => Y) AY eY (fun _ _ : M => opY)
     (fun (x1 y0 z0 : M) (a b c : Y) =>
      transport_const (assoc x1 y0 z0) (opY (opY a b) c) @ opY_assoc a b c)
     (fun (x1 : M) (a : Y) =>
      transport_const (ident_l x1) (opY eY a) @ opY_ident_l a)
     (fun (x1 : M) (a : Y) =>
      transport_const (ident_r x1) (opY a eY) @ opY_ident_r a)).
  rewrite M_ind_beta_assoc. reflexivity.
Qed.

Definition M_rec_beta_ident_l : forall
  (Y : Type)
  (AY : A -> Y)
  (eY : Y)
  (opY : Y -> Y -> Y)
  (opY_assoc : forall x y z : Y, 
      opY (opY x y) z = opY x (opY y z))
  (opY_ident_l : forall (x : Y), 
      opY eY x = x)
  (opY_ident_r : forall (x : Y), 
      opY x eY = x)
  (x : M),
  ap (M_rec Y AY eY opY opY_assoc opY_ident_l opY_ident_r) (ident_l x)
  = opY_ident_l (M_rec Y AY eY opY opY_assoc opY_ident_l opY_ident_r x).
Proof.
  intros.
  eapply (cancelL (transport_const _ _)).
  etransitivity. symmetry.
   apply apD_const.
  unfold M_rec. simpl. 
  rewrite M_ind_beta_ident_l. reflexivity.
Qed.

Definition M_rec_beta_ident_r : forall
  (Y : Type)
  (AY : A -> Y)
  (eY : Y)
  (opY : Y -> Y -> Y)
  (opY_assoc : forall x y z : Y, 
      opY (opY x y) z = opY x (opY y z))
  (opY_ident_l : forall (x : Y), 
      opY eY x = x)
  (opY_ident_r : forall (x : Y), 
      opY x eY = x)
  (x : M),
  ap (M_rec Y AY eY opY opY_assoc opY_ident_l opY_ident_r) (ident_r x)
  = opY_ident_r (M_rec Y AY eY opY opY_assoc opY_ident_l opY_ident_r x).
Proof.
  intros.
  eapply (cancelL (transport_const _ _)).
  etransitivity. symmetry.
   apply apD_const.
  unfold M_rec. simpl. 
  rewrite M_ind_beta_ident_r. reflexivity.
Qed.

End monoid.

Arguments op {_} x y.
Arguments el {_} a.
Arguments e {_}.
Infix "⊡" := op (at level 80).

Instance M_recursion A : HitRecursion (M A) := {
  indTy := _; recTy := _; 
  H_inductor := (M_ind A); H_recursor := (M_rec A) }.

(* (M A) is not an h-set by recursion into S1 *)
Section monoid_sphere.
Context `{UAxiom : Univalence}.
Variable A : Type.

Definition f (x : S1) : x = x.
Proof.
hinduction x.
- exact loop.
- etransitivity. 
  eapply (@transport_paths_FlFr S1 S1 idmap idmap).
  hott_simpl.
Defined.

Definition S1op (x y : S1) : S1.
Proof.
hrecursion y.
- exact x. (* x + base = x *)
- apply f. 
Defined.

Lemma S1op_nr (x : S1) : S1op x base = x.
Proof. reflexivity. Defined.

Lemma S1op_nl (x : S1) : S1op base x = x.
Proof.
hrecursion x.
- exact loop.
- etransitivity.
  apply (@transport_paths_FlFr _ _ (fun x => S1op base x) idmap _ _ loop loop).
  hott_simpl.
  apply moveR_pM. apply moveR_pM. hott_simpl.
  etransitivity. apply (ap_V (S1op base) loop).
  f_ap. apply S1_rec_beta_loop.
Defined.

Lemma S1op_assoc (x y z : S1) : S1op x (S1op y z) = S1op (S1op x y) z.
Proof.
hrecursion z.
- reflexivity.
- etransitivity.
  apply (@transport_paths_FlFr _ _ (fun z => S1op x (S1op y z)) (S1op (S1op x y)) _ _ loop idpath). 
  hott_simpl.
  apply moveR_Mp. hott_simpl.
  rewrite S1_rec_beta_loop.
  rewrite ap_compose.
  rewrite S1_rec_beta_loop.
  hrecursion y.
  + symmetry. apply S1_rec_beta_loop.
  + apply is1type_S1.
Defined.

Definition M_to_S : M A -> S1.
Proof.
hrecursion.
- intro a. apply base.
- exact base.
- exact S1op.
- intros. symmetry. apply S1op_assoc.
- apply S1op_nl.
- apply S1op_nr.
Defined.

Lemma M_S_ap : (ident_l A e) = (ident_r A e) -> idpath = loop.
Proof.
intros H.
enough (ap M_to_S (ident_l A e) = ap M_to_S (ident_r A e)) as H'.
- rewrite M_rec_beta_ident_l in H'. 
  simpl in H'.
  rewrite M_rec_beta_ident_r in H'.
  unfold S1op_nr in H'. 
  exact H'^.
- f_ap.
Defined.

Lemma M_not_hset : IsHSet (M A) -> False.
Proof.
intros H.
enough (idpath = loop). 
- assert (S1_encode _ idpath = S1_encode _ (loopexp loop (pos Int.one))) as H' by f_ap.
  rewrite S1_encode_loopexp in H'. simpl in H'. symmetry in H'.
  apply (pos_neq_zero H').
- apply M_S_ap.
  apply set_path2.
Defined.

End monoid_sphere.
