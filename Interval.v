Require Import HoTT.

(* Definition of the interval type *)
Module Export interval.
Private Inductive I : Type :=
  | zero : I
  | one : I.
Axiom seg : zero = one.

Definition I_ind (P : I -> Type)
  (x : P zero) (y : P one) (p : transport P seg x = y)
  (i : I) : P i
  := (match i return _ -> P i with
        | zero => fun _ => x
        | one  => fun _ => y
      end) p.
Definition I_rec :
  forall (P : Type) (x y : P) (p : x = y) (i : I), P
  := fun P x y p i => I_ind (fun _ => P) x y (transport_const _ _ @ p) i.

Axiom I_rec_beta_seg : forall P x y p,
    ap (I_rec P x y p) seg = p.
Axiom I_ind_beta_seg : forall P x y p,
    apD (I_ind P x y p) seg = p.
End interval.

(* (** ** From an interval type, we can prove function extensionality. *) *)

(* Theorem interval_impl_funext :  *)
(*   forall X Y (f g : X -> Y), f == g -> f = g. *)
(* Proof. *)
(*   intros X Y f g H. *)
(*   (* At each point 'x', there is a path f x ~~ g x,  *)
(*   hence there is a map from the interval to Y *) *)
(*   pose (m := fun x => I_rec _ (f x) (g x) (H x)). *)
(*   (* We get a function X -> I -> Y that we can curry *)
(*   to get a function I -> X -> Y *) *)
(*   pose (m' := fun i x => m x i). *)
(*   Eval compute in (m' zero). *)
(*   Eval compute in (m' one). *)
(*   (* Finally we "transport" the path 0 ~~ 1 to f ~~ g *) *)
(*   apply (ap m' seg). *)
(* Qed. *)

(* (* We can repeat the same argument for Funcext for dependent  *)
(*    functions *) *)
(* Theorem interval_impl_depfunext :  *)
(*   forall X Y (f g : forall (x : X), Y x), f == g -> f = g. *)
(* Proof. *)
(*   intros X Y f g H. *)
(*   pose (m := fun x => I_rec _ (f x) (g x) (H x)). *)
(*   pose (m' := fun i x => m x i). *)
(*   apply (ap m' seg). *)
(* Qed. *)

(** ** Interval is contractible via encode-decode *)
Section code_decode.
Context `{Univalence}.
Definition code_zero : I -> Type := I_rec _ Unit Unit idpath.
Definition code_one : I -> Type := I_rec _ Unit Unit idpath.

Definition code : I -> I -> Type.
Proof.
simple refine (I_rec _ _ _ _).
- exact code_zero.
- exact code_one.
- reflexivity.
Defined.

Instance code_set x y : IsHSet (code x y).
Proof. revert x y.
simple refine (I_ind _ _ _ _); simpl.
- simple refine (I_ind _ _ _ _); simpl; [ | | apply path_ishprop ].
  + apply _.
  + apply _.
- simple refine (I_ind _ _ _ _); simpl; [ | | apply path_ishprop ].
  + apply _.
  + apply _.
- apply path_ishprop.
Defined.

Lemma transport_code_zero_x : 
  transport code_zero seg = idmap.
Proof.
  apply path_forall. intros u.
  transport_to_ap.
  rewrite I_rec_beta_seg. hott_simpl.
Defined.

Lemma transport_code_one_x : 
  transport code_one seg = idmap.
Proof. apply transport_code_zero_x. Defined.

Lemma transport_code_one_x_V  : 
  transport code_one seg^ = idmap.
Proof. 
  apply path_forall. intros u.
  transport_to_ap.
  rewrite ap_V.
  rewrite I_rec_beta_seg. hott_simpl.
Defined.

Lemma transport_code_x_zero : 
  transport (fun x => code x zero) seg = idmap.
Proof.
  apply path_forall. intros u.
  transport_to_ap.  
  transitivity (transport idmap (ap ((fun f => f zero) o code) seg) u).
  { reflexivity. }
  rewrite (ap_compose code (fun f => f zero) seg).
  rewrite I_rec_beta_seg. hott_simpl.
Defined.

Lemma transport_code_x_one : 
  transport (fun x => code x one) seg = idmap.
Proof.
  apply path_forall. intros u.
  transport_to_ap.  
  transitivity (transport idmap (ap ((fun f => f one) o code) seg) u).
  { reflexivity. }
  rewrite (ap_compose code (fun f => f _) seg).
  rewrite I_rec_beta_seg. hott_simpl.
Defined.

Lemma ap_diag {A : Type} {x y : A} (p : x = y) :
  ap (fun x : A => (x, x)) p = path_prod' p p.   
Proof.
  by path_induction.
Defined.

Lemma transport_code_diag z :
  transport (fun i : I => code i i) seg z = z.
Proof.
  transitivity (transport (fun x => (fun y => code (fst y) (snd y)) (x, x)) seg z).
  { f_ap. }
  rewrite transport_compose.
  rewrite ap_diag.
  rewrite transport_path_prod; simpl.
  rewrite transport_code_x_one.
  rewrite transport_code_zero_x.
  reflexivity.
Defined.

Definition r : forall (x : I), code x x.
Proof.
simple refine (I_ind _ _ _ _); simpl.
- exact tt.
- exact tt.
- apply transport_code_diag.
Defined.

Definition encode_pre : forall (x y : I), x = y -> code x y
  := fun x y p => transport (fun z => code x z) p (r x).

Definition encode : forall x y, Trunc 0 (x = y) -> code x y.
Proof.
  intros x y.
  apply Trunc_rec.
  refine (fun p => transport (fun z => code x z) p _). clear p.
  revert x. simple refine (I_ind _ _ _ _); simpl.
  - exact tt.
  - exact tt.
  - (* TODO: this does not work (universe levels) : apply (transport_code_diag tt). *)
    transitivity (transport (fun x => (fun y => code (fst y) (snd y)) (x, x)) seg tt).
    { f_ap. }
    rewrite transport_compose.
    rewrite ap_diag.
    rewrite transport_path_prod; simpl.
    rewrite transport_code_x_one.
    rewrite transport_code_zero_x.
    reflexivity.
Defined.

(* TODO: remove this *)
Lemma transport_paths_FlFr_trunc :
  forall {A B : Type} (f g : A -> B) {x1 x2 : A} (p : x1 = x2)
  (q : f x1 = g x1),
    transport (fun x : A => Trunc 0 (f x = g x)) p (tr q) = tr (((ap f p)^ @ q) @ ap g p).
Proof.
  destruct p; simpl. intro q.
  refine (ap tr _).
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition decode_zero : forall (y : I ), code_zero y -> zero = y.
Proof.
simple refine (I_ind _ _ _ _); simpl.
- exact (fun _ => idpath).
- exact (fun _ => seg).
- apply path_forall. intro t.
  refine (transport_arrow _ _ _ @ _).
  refine (transport_paths_FlFr _ _ @ _).
  hott_simpl.
Defined.

Definition decode_one : forall (y : I ), code_one y -> one = y.
Proof.
simple refine (I_ind _ _ _ _); simpl.
- exact (fun _ => seg^).
- exact (fun _ => idpath).
- apply path_forall. intro t.
  refine (transport_arrow _ _ _ @ _).
  refine (transport_paths_FlFr _ _ @ _).
  hott_simpl.
Defined.

Definition decode : forall (x y : I), code x y -> Trunc 0 (x = y).
Proof.
simple refine (I_ind _ _ _ _); simpl.
- intro y. refine (tr o _). exact (decode_zero y).
- intro y. refine (tr o _). exact (decode_one y).
- apply path_forall. intro z.
  rewrite transport_forall_constant.
  apply path_forall. intros c.
  rewrite transport_arrow.
  rewrite transport_paths_FlFr_trunc. hott_simpl.
  revert z c. simple refine (I_ind _ _ _ _); simpl.
  + intro. hott_simpl.
  + intro. hott_simpl.
  + apply path_forall. intros ?. apply set_path2.
Defined.

Lemma decode_encode (u v : I) : forall (p : Trunc 0 (u = v)),
  decode u v (encode u v p) = p.
Proof.
apply Trunc_ind.
- apply _.
- intros p. induction p.
  simpl. revert u. simple refine (I_ind _ _ _ _).
  + simpl. reflexivity.
  + simpl. reflexivity.    
  + apply set_path2.
Defined.

Lemma encode_decode : forall (u v : I) (c : code u v),
    encode u v (decode u v c) = c.
Proof.
simple refine (I_ind _ _ _ _).
- simple refine (I_ind _ _ _ _).
  + simpl. induction c. reflexivity.
  + simpl. induction c. rewrite transport_code_zero_x. reflexivity.
  + apply path_forall; intros ?. apply set_path2.
- simple refine (I_ind _ _ _ _).
  + simpl. induction c. rewrite transport_code_one_x_V. reflexivity.
  + simpl. induction c. reflexivity.
  + apply path_forall; intros ?. apply set_path2.
- repeat (apply path_forall; intros ?). apply set_path2.
Defined.

End code_decode.

