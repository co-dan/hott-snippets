From HoTT Require Import HoTT HIT.Truncations.
From HoTT Require Export HIT.Circle.
Require Import HitTactics.

Instance S1_recursion : HitRecursion S1 := {
  indTy := _; recTy := _; 
  H_inductor := S1_ind; H_recursor := S1_rec }.

Section coding.
Context `{Univalence}.

(** * Covering space *)

(** We split the definition of the covering space into two
definitions. First we define [code base] and then use it to define
[code]. *)
Definition code_base : S1 -> Type.
hrecursion.
- exact Int.
- exact (path_universe succ_int).
Defined.

(** The [code_base] is a set. *)
Instance code_base_set x : IsHSet (code_base x).
Proof.
hinduction x; [ | apply path_ishprop ].
apply _.
Defined.

(** By recursion, we give a homotopy [code base == code_base], that
sends each [x] on a circle to a fiber [code_base x = Z] with numbering
shifted by one. This will result the covering space [code] over S1 *
S1 to behave in such a way that going aroung the first circle
corresponds to going "up" in the helix, and going around the second
circle corresponds to going "down" *)
Definition code_base_pred_path : code_base == code_base.
Proof.
  unfold pointwise_paths. hrecursion.
  + apply (path_universe succ_int^-1).
  + simpl. refine (transport_paths_FlFr loop _ @ _).
    refine (ap (fun p =>  (p^ @ path_universe pred_int) @ p) (S1_rec_beta_loop _ _ _) @ _).
    etransitivity; [ apply concat_pp_p |].
    refine (ap (fun p => p @ (path_universe pred_int @ path_universe succ_int)) (path_universe_V _)^ @ _).
    apply moveR_Mp.
    simpl. etransitivity; [ | apply ((concat_Vp _)^) ].        
    refine (ap (fun p => p @ _) (path_universe_V succ_int) @ _).
    apply concat_Vp.
Defined.

Definition code : S1 -> S1 -> Type.
Proof.
hrecursion.
- exact code_base. 
- apply path_forall. exact code_base_pred_path.
Defined.

Instance code_set x y : IsHSet (code x y).
Proof.
hinduction x; [ | apply path_ishprop ].
apply _.
Defined.

(** * Auxiliary lemmas *)
Lemma ap_diag {A : Type} {x y : A} (p : x = y) :
  ap (fun x : A => (x, x)) p = path_prod' p p.   
Proof.
  by path_induction.
Defined.
Lemma ap11_up {A B : Type} {f g : A -> B} {x y :A} (h : f = g) (p : x = y):
  ap11 h p = ap f p @ ap (fun k => k y) h.
Proof.
  by path_induction.
Defined.
Lemma ap_path_forall : forall {X Y : Type} (h k : X -> Y) (b : X) (g : forall x, h x = k x),
  ap (fun f => f b) (path_forall _ _ g) = g b.
Proof.
intros X Y h k b g.
refine ((ap_apply_lD (path_forall h k g) b) @ _).
apply (apD10_path_forall _ _ _ b).
Defined.

(* TODO: are those in the library somewhere?
Or can it be proved without induction? *)
Lemma transport_paths_r_trunc :
forall {A : Type} {x y1 y2 : A} (p : y1 = y2) (q : x = y1),
  transport (fun y : A => Trunc 0 (x = y)) p (tr q) = tr (q @ p).
Proof.
   by path_induction.
Defined.
Lemma transport_paths_FlFr_trunc :
  forall {A B : Type} (f g : A -> B) {x1 x2 : A} (p : x1 = x2)
  (q : f x1 = g x1),
    transport (fun x : A => Trunc 0 (f x = g x)) p (tr q) = tr (((ap f p)^ @ q) @ ap g p).
Proof.
  destruct p; simpl. intro q.
  refine (ap tr _).
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition coe_succ n :
transport idmap (path_universe succ_int) n = succ_int n :=
  ap (fun f => f n) 
   (transport_idmap_path_universe (BuildEquiv _ _ succ_int _)).
Definition coe_pred n :
transport idmap (path_universe pred_int) n = pred_int n :=
  ap (fun f => f n) 
   (transport_idmap_path_universe (BuildEquiv _ _ succ_int^-1 _)).

(** * Characterizations of [transport] in the [code] fibration *)

(** When the right variable is a free one *)
Lemma transport_code_r (z : Int) :
  transport code_base loop z = succ_int z.
Proof. 
  transport_to_ap.
  refine (ap (fun p => transport idmap p z) (S1_rec_beta_loop _ _ _) @ _).
  apply coe_succ.
Defined.
Lemma transport_code_r_V (z : Int)
  : transport code_base loop^ z = pred_int z.
Proof.
  transport_to_ap.
  rewrite ap_V.
  rewrite S1_rec_beta_loop.
  rewrite <- (path_universe_V succ_int).
  apply coe_pred.
Qed.

(** When the left variable is a free one *)
Lemma transport_code_l n :
  transport (fun x => code x base) loop n = pred_int n.
Proof. 
  transport_to_ap.
  transitivity (transport idmap (ap ((fun f => f base) o code) loop) n).
  { reflexivity. }
  rewrite (ap_compose code (fun f => f base)).
  rewrite S1_rec_beta_loop.
  rewrite ap_path_forall. simpl.
  apply coe_pred.
Defined.

Lemma transport_code_l_V n :
  transport (fun x => code x base) loop^ n = succ_int n.
Proof. 
  transport_to_ap.
  transitivity (transport idmap (ap ((fun f => f base) o code) loop^) n).
  { reflexivity. }
  rewrite (ap_compose code (fun f => f base)).
  rewrite ap_V.
  rewrite S1_rec_beta_loop.
  rewrite <- (path_forall_V). 
  rewrite (ap_path_forall _ _ base). simpl.
  rewrite <- path_universe_V. simpl.
  assert (isequiv_succ_int = (@isequiv_inverse Int Int pred_int
             (@isequiv_inverse Int Int succ_int isequiv_succ_int))) as PS.
  { apply hprop_isequiv. }
  rewrite <- PS.
  apply (coe_succ n).
Defined.

Lemma transport_code_diag n :
  transport (fun x => code x x) loop n = n.
Proof.
  transitivity (transport (fun x => (fun y => code (fst y) (snd y)) (x, x)) loop n).
  { f_ap. }
  rewrite transport_compose.
  rewrite ap_diag.
  rewrite transport_path_prod; simpl.
  rewrite transport_code_r.
  rewrite transport_code_l.
  revert n. intros [[|n] | | [|n]]; reflexivity.
Defined.

(** * Reflexivity, encode, and decode *)
Definition r : forall x, code x x.
Proof.
hinduction.
- exact Int.zero.
- apply transport_code_diag.
Defined.

(** We define "pre-encoding" that encodes the total path space [x =
y]; then, since [code] is a set, [encode_pre] factors through the
truncation. *)
Definition encode_pre : forall (x y : S1), x = y -> code x y
  := fun x y p => transport (fun z => code x z) p (r x).

Definition encode : forall x y, Trunc 0 (x = y) -> code x y.
Proof.
  intros x y.
  apply Trunc_rec.
  apply (encode_pre x y).
Defined.

Definition decode_base : forall (y : S1), code_base y -> base = y.
Proof.
hinduction.
- intro n. apply (loopexp loop n).
- apply path_forall. intros z.
  refine (transport_arrow _ _ _ @ _).    
  refine (transport_paths_r loop _ @ _).
  rewrite transport_code_r_V.
  destruct z as [[|n] | | [|n]]; simpl.
   by apply concat_pV_p.
   by apply concat_pV_p.
   by apply concat_Vp.
   by apply concat_1p.
   reflexivity.
Defined.

Definition decode : forall (x y : S1), code x y -> Trunc 0 (x = y).
Proof.
hinduction.
- intro y. refine (tr o _). exact (decode_base y).
- apply path_forall. intros x.
  rewrite transport_forall_constant.
  apply path_forall. intros z.
  rewrite transport_arrow.
  rewrite transport_paths_FlFr_trunc. hott_simpl.
  revert z. hinduction x.
  + intro z.
    rewrite transport_code_l_V.
    induction z as [[|n] | | [|n]]; simpl; refine (ap tr _).
    * by apply concat_p1. 
    * induction n; simpl.
      reflexivity.
      hott_simpl. rewrite IHn. reflexivity.
    * by apply concat_Vp.
    * by apply concat_V_pp.
    * induction n; simpl.
      hott_simpl.
      hott_simpl. rewrite IHn. reflexivity.
  + apply path_forall. intros ?. apply set_path2.
Defined.

(** * Equivalence *)
Lemma decode_encode (u v : S1) : forall (p : Trunc 0 (u = v)),
  decode u v (encode u v p) = p.
Proof.
apply Trunc_ind.
- apply _.
- intros p. induction p.
  simpl.
  hinduction u.
  + reflexivity.
  + (* rewrite transport_paths_FlFr_D. *) apply set_path2.
Defined.

Lemma encode_pre_loopexp (z : Int) :
  encode_pre base base (loopexp loop z) = z.
Proof. unfold encode_pre.
  destruct z as [n | | n]; simpl.
  - induction n; simpl in *.
    + by apply transport_code_r_V. 
    + rewrite transport_pp.
      refine (moveR_transport_V _ loop _ _ _).
      refine (_ @ (transport_code_r _)^).
      assumption.
  - reflexivity.
  - induction n; simpl in *.
    + by apply transport_code_r.
    + rewrite transport_pp.
      refine (moveR_transport_p _ loop _ _ _).
      refine (_ @ (transport_code_r_V _)^).
      assumption.
Defined.

Lemma encode_decode : forall (u v : S1) (c : code u v),
    encode u v (decode u v c) = c.
Proof.
hinduction.
- hinduction.
  + apply encode_pre_loopexp. 
  + apply path_forall; intros ?. apply set_path2.
- repeat (apply path_forall; intros ?). apply set_path2.
Defined.

 
Lemma canon'_0 (p : base = base) :
  (@tr 0 _ p) = tr (loopexp loop (encode_pre base base p)).
Proof.
  transitivity (decode base base (encode base base (tr p))).
  { symmetry. apply decode_encode. }
  simpl. reflexivity.
Defined.

Lemma canon_0 : forall (p : base = base), exists n, @tr 0 _ p = tr (loopexp loop n).
Proof. intro p. exists (encode_pre base base p). apply canon'_0. Defined.

End coding.
