From HoTT Require Export HoTT.
From HoTT Require Import Pointed HIT.Pushout.
Require Import Circ HitTactics.

(* TODO: rewrite this with pointed types *)
Section WedgeSum.
Context {A B : Type}.
Context (a : A).
Context (b : B).
Definition wedgesum :=
  @pushout Unit A B (fun _ => a) (fun _ => b).

Definition wedge_point_l : wedgesum := pushl tt.
Definition wedge_point_r : wedgesum := pushr tt.
Definition wedge_point_eq : wedge_point_l = wedge_point_r := pp tt.
Definition wedge_l : A -> wedgesum := push o inl.
Definition wedge_r : B -> wedgesum := push o inr.

Definition wedgesum_rec' (P : Type) (f : A -> P) (g : B -> P)
  (fg_eq : f a = g b) : wedgesum -> P.
Proof.
simple refine (pushout_rec _ _ _).
- apply (sum_ind (fun _ => P) f g).
- intros []. simpl. exact fg_eq.
Defined.

Definition wedgesum_rec (P : Type) (p : P) (f : A -> P) (g : B -> P)
  (f_eq : f a = p) (g_eq : g b = p) : wedgesum -> P.
Proof.
simple refine (pushout_rec _ _ _).
- apply (sum_ind (fun _ => P) f g).
- intros []. simpl. apply (f_eq @ g_eq^).
Defined.

End WedgeSum.

Module Export eight.
Private Inductive eight : Type0 :=
| base8 : eight.
Axiom loop1 : base8 = base8.
Axiom loop2 : base8 = base8.

Definition Eight_ind (P : eight -> Type) (b : P base8) (l1 : loop1 # b = b) (l2 : loop2 # b = b)
  : forall (x:eight), P x := fun x =>
  match x return (_ -> _ -> P x) with
  | base8 => fun _ _ => b
  end l1 l2.

Axiom Eight_ind_beta_loop1 : forall (P : eight -> Type) (b : P base8) (l1 : loop1 # b = b) (l2 : loop2 # b = b),
    apD (Eight_ind P b l1 l2) loop1 = l1.
Axiom Eight_ind_beta_loop2 : forall (P : eight -> Type) (b : P base8) (l1 : loop1 # b = b) (l2 : loop2 # b = b),
    apD (Eight_ind P b l1 l2) loop2 = l2.
                    
Definition Eight_rec (P : Type) (b : P) (l1 l2 : b = b) :
  eight -> P.
Proof.
  refine (Eight_ind (fun _ => P) b _ _).
  refine (transport_const _ _ @ l1).
  refine (transport_const _ _ @ l2).
Defined.

Definition Eight_rec_beta_loop1 (P : Type) (b : P) (l1 l2 : b = b) :
  ap (Eight_rec P b l1 l2) loop1 = l1.
Proof.
  eapply (cancelL (transport_const loop1 _)).
  simple refine ((apD_const _ _)^ @ _).
  apply Eight_ind_beta_loop1.
Defined.

Definition Eight_rec_beta_loop2 (P : Type) (b : P) (l1 l2 : b = b) :
  ap (Eight_rec P b l1 l2) loop2 = l2.
Proof.
  eapply (cancelL (transport_const loop2 _)).
  simple refine ((apD_const _ _)^ @ _).
  apply Eight_ind_beta_loop2.
Defined.

End eight.

Instance Eight_recursion : HitRecursion eight := {
  indTy := _; recTy := _; 
  H_inductor := Eight_ind; H_recursor := Eight_rec }.


(* Equivalence *)

Definition ate := wedgesum base base.

Definition a2e : ate -> eight.
Proof.
simple refine (wedgesum_rec' _ _ _ _ _ _).
- hrecursion.
  * exact base8.
  * exact loop1.
- hrecursion.
  * exact base8.
  * exact loop2.
- simpl. reflexivity.
Defined.

(* TODO: this should be encapsulated better *)
Definition e2a : eight -> ate.
Proof. 
hrecursion.
- apply wedge_point_l.
- unfold wedge_point_l. unfold pushl. simple refine (ap (fun x => push (inl x)) _). apply loop.
- simple refine (pp _ @ _ @ (pp _)^). unfold pushr.
  simple refine (ap (fun x => push (inr x)) _). apply loop.
Defined.

Lemma eight_ate_eight :
  forall x : eight, a2e (e2a x) = x.
Proof.
hrecursion.
- reflexivity.
- rewrite (@transport_paths_FlFr _ _ _ idmap).
  hott_simpl.      
  rewrite (ap_compose e2a a2e _).
  rewrite Eight_rec_beta_loop1.
  rewrite <- (ap_compose (fun x => push (inl x)) a2e). simpl.
  rewrite S1_rec_beta_loop. hott_simpl.
- rewrite (@transport_paths_FlFr _ _ _ idmap).
  hott_simpl.      
  rewrite (ap_compose e2a a2e _).
  rewrite Eight_rec_beta_loop2. 
  rewrite ?ap_pp, ap_V. rewrite pushout_rec_beta_pp. hott_simpl.
  rewrite <- (ap_compose (fun x => push (inr x)) a2e). simpl.
  rewrite S1_rec_beta_loop. hott_simpl.
Defined.

Lemma ate_eight_l :
  forall a : S1, e2a (a2e (push (inl a))) = push (inl a).
Proof.
hrecursion.
- reflexivity.
- rewrite transport_paths_FlFr. hott_simpl.
  rewrite ap_compose.
  rewrite S1_rec_beta_loop.
  rewrite Eight_rec_beta_loop1. hott_simpl.
Defined.

Lemma ate_eight_r :
  forall a : S1, e2a (a2e (push (inr a))) = push (inr a).
Proof.
hrecursion.
- refine (_ @ pp _). reflexivity.
- rewrite transport_paths_FlFr. hott_simpl.
  rewrite ?concat_pp_p.          
  rewrite ap_compose.
  rewrite S1_rec_beta_loop.
  rewrite Eight_rec_beta_loop2.
  rewrite inv_pp. hott_simpl.
Defined.

Lemma ee : eight <~> ate.
Proof.
unshelve esplit.
- exact e2a.
- apply isequiv_biinv. unfold BiInv. split.
  + exists a2e. exact eight_ate_eight.
  + exists a2e. unfold Sect. simple refine (pushout_ind _ _ _ _ _); simpl.
    * simple refine (sum_ind _ _ _); simpl.     
      { exact ate_eight_l. }
      { exact ate_eight_r. }
    * intros []; simpl.
      rewrite transport_paths_FlFr. hott_simpl.
      rewrite ap_compose.
      rewrite pushout_rec_beta_pp. hott_simpl.
Defined.
