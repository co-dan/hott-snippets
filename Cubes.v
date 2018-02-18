Require Import HoTT.
Require Import Circ HitTactics.

(** * PathOver *)
Inductive PathOver {A : Type} (C : A -> Type) {a1 : A} :
  forall {a2 : A}, (a1 = a2) -> C a1 -> C a2 -> Type :=
| pid : forall {c : C a1}, PathOver C idpath c c.
Arguments pid _ _ _ _.

Instance PathOver_reflexive {A : Type} (C : A -> Type) a : Reflexive (PathOver C (idpath a)).
Proof. intros c. apply pid. Defined.

Definition apdo {A : Type} {C : A -> Type} (f : forall a, C a) {a b : A} (p : a = b) : PathOver C p (f a) (f b) :=
  match p with idpath => pid _ end.

Lemma pathover_transport {A : Type} {B : A -> Type} {a1 a2 : A} {p : a1 = a2} {b1 : B a1} {b2 : B a2} (q : PathOver B p b1 b2) : transport B p b1 = b2.
Proof. induction q. reflexivity. Defined.

Lemma transport_pathover {A : Type} {B : A -> Type} {a1 a2 : A} {p : a1 = a2} {b1 : B a1} {b2 : B a2} (q : transport B p b1 = b2) : PathOver B p b1 b2.
Proof. induction p,q. reflexivity. Defined.

Instance isequiv_transport_pathover {A : Type} {B : A -> Type} {a1 a2 : A} {p : a1 = a2} {b1 : B a1} {b2 : B a2} : IsEquiv (@transport_pathover A B a1 a2 p b1 b2).
Proof.
  apply isequiv_biinv.
  split; exists pathover_transport.
  - intros x. induction p. induction x. reflexivity.
  - intros x. induction x. reflexivity.
Defined.

Lemma pathover_transport_apdo {A : Type} {C : A -> Type} (f : forall a, C a) {a b : A} (p : a = b) : pathover_transport (apdo f p) = apD f p.
Proof. induction p. reflexivity. Defined.

Lemma transport_pathover_apD {A : Type} {C : A -> Type} (f : forall a, C a) {a b : A} (p : a = b) : transport_pathover (apD f p) = apdo f p.
Proof. induction p. reflexivity. Defined.

Lemma path_sigma {A : Type} {B : A -> Type} {a1 a2 : A} (p : a1 = a2) {b1 : B a1} {b2 : B a2} (q : PathOver B p b1 b2) : (a1;b1) = (a2;b2).
Proof. induction q. reflexivity. Defined.

Definition path_pathover {A : Type} {B : A -> Type} {a : A} {b1 b2 : B a}
           (p : PathOver B idpath b1 b2) : (b1 = b2) := pathover_transport p.

Definition pathover_path {A : Type} {B : A -> Type} {a : A} {b1 b2 : B a}
           (p : b1 = b2) : PathOver B idpath b1 b2 :=
  @transport_pathover _ _ _ _ idpath _ _ p.

Lemma pathover_forall {A : Type} {B : A -> Type}
      {C : (sig B) -> Type}
      {a1 a2 : A} {p : a1 = a2}
      {f : forall (b : B a1), C (a1; b)}
      {g : forall (b : B a2), C (a2; b)} :
  PathOver (fun a => forall (b : B a), C (a;b)) p f g ->
  forall (x : B a1) (y : B a2) (q : PathOver B p x y), PathOver C (path_sigma p q) (f x) (g y).
Proof.
  intros α x y β. induction β. simpl.
  apply pathover_path. apply path_pathover in α.
  refine (ap (fun h => h c) α).
Defined.

Lemma forall_pathover `{Univalence} {A : Type} {B : A -> Type}
      {C : (sig B) -> Type}
      {a1 a2 : A} {p : a1 = a2}
      {f : forall (b : B a1), C (a1; b)}
      {g : forall (b : B a2), C (a2; b)} :
  (forall (x : B a1) (y : B a2) (q : PathOver B p x y), PathOver C (path_sigma p q) (f x) (g y)) ->
  PathOver (fun a => forall (b : B a), C (a;b)) p f g.
Proof.
  intros β. induction p.
  apply pathover_path. apply path_forall. intro x.
  specialize (β x x (@pid _ B a1 x)).
  apply path_pathover. exact β.
Defined.

(** * Square *)

Inductive Square {A : Type} {a00 : A} : forall {a01 a10 a11 : A},
    (a00 = a01) -> (a00 = a10) -> (a01 = a11) -> (a10 = a11) -> Type :=
| sid : Square idpath idpath idpath idpath.

(** Square l t b r :

a00---- t ----a10
 |             |
 |             |
 l             r
 |             |
 |             |
a01---- b ----a11

l @ b = t @ r
*)

Definition disc_square {A : Type} {a00 a01 a10 a11 : A}
           (l : a00 = a01) (t : a00 = a10) (b : a01 = a11) (r : a10 = a11) :
  Square l t b r -> (l @ b = t @ r).
Proof. intros s. induction s. reflexivity. Defined.

Definition square_disc {A : Type} {a00 a01 a10 a11 : A}
           (l : a00 = a01) (t : a00 = a10) (b : a01 = a11) (r : a10 = a11) :
  (l @ b = t @ r) -> Square l t b r.
Proof.
  induction l,b,r. simpl. intros s.
  apply (transport (fun z => Square 1 z 1 1) (s @ concat_p1 t)).
  apply sid.
Defined.

(** hrefl p :

 a----- 1 -----a
 |             |
 |             |
 p             p
 |             |
 |             |
 b----- 1 -----b
*)
Definition hrefl {A : Type} {a b : A} {p : a = b} : Square p 1 1 p.
Proof. induction p. apply sid. Defined.

(** vrefl p :

 a----- p -----b
 |             |
 |             |
 1             1
 |             |
 |             |
 a----- p -----b
*)
Definition vrefl {A : Type} {a b : A} {p : a = b} : Square 1 p p 1.
Proof. induction p. apply sid. Defined.

Instance reflexive_horizontal {A : Type} {a b : A} : Reflexive (fun (p q : a = b) => Square p 1 1 q).
Proof. intros p. apply hrefl. Defined.
Instance reflexive_vertical {A : Type} {a b : A} : Reflexive (fun (p q : a = b) => Square 1 p q 1).
Proof. intros p. apply vrefl. Defined.

(** Image of a aquare under f *)
Definition ap_square {A B : Type} (f : A -> B) {a00 a01 a10 a11 : A}
  {l : a00 = a01} {t : a00 = a10} {b : a01 = a11} {r : a10 = a11} :
  Square l t b r -> Square (ap f l) (ap f t) (ap f b) (ap f r).
Proof.
  intros s. induction s. simpl. apply sid.
Defined.

(** Product of two squares *)
Definition prod_square {A B : Type}
  {a00 a01 a10 a11 : A}
  {l : a00 = a01} {t : a00 = a10} {b : a01 = a11} {r : a10 = a11}
  (s : Square l t b r)
  {b00 b01 b10 b11 : B}
  {l' : b00 = b01} {t' : b00 = b10} {b' : b01 = b11} {r' : b10 = b11}
  (s' : Square l' t' b' r') :
  Square (path_prod' l l') (path_prod' t t') (path_prod' b b') (path_prod' r r').
Proof. induction s, s'. apply sid. Defined.

(** Whiskering *)

(**

      ____ t'____
     /           \
   a00---- t ----a10
  / |             | \
 |  |             |  |
 l' l             r  r'
 |  |             |  |
  \ |             | /
   a01---- b ----a11
     \____ b'____/

*)
Definition whisker_square {A : Type} {a00 a01 a10 a11 : A}
  {l l' : a00 = a01} {t t' : a00 = a10} {b b' : a01 = a11} {r r' : a10 = a11}
  (ll : l = l') (tt : t = t') (bb : b = b') (rr : r = r') :
  Square l t b r -> Square l' t' b' r'.
Proof.
  induction 1.
  apply (transport (fun z => Square z t' b' r') ll).
  apply (transport (fun z => Square 1 z b' r') tt).
  apply (transport (fun z => Square 1 1 z r') bb).
  apply (transport (fun z => Square 1 1 1 z) rr).
  apply sid.
Defined.

Definition whisker_square_l {A : Type} {a00 a01 a10 a11 : A}
  {l l' : a00 = a01} {t : a00 = a10} {b : a01 = a11} {r : a10 = a11}
  (ll : l = l') :
  Square l t b r -> Square l' t b r := whisker_square ll 1 1 1.

Definition whisker_square_t {A : Type} {a00 a01 a10 a11 : A}
  {l : a00 = a01} {t t' : a00 = a10} {b : a01 = a11} {r : a10 = a11}
  (tt : t = t') :
  Square l t b r -> Square l t' b r := whisker_square 1 tt 1 1.

Definition whisker_square_b {A : Type} {a00 a01 a10 a11 : A}
  {l : a00 = a01} {t : a00 = a10} {b b' : a01 = a11} {r : a10 = a11}
  (bb : b = b') :
  Square l t b r -> Square l t b' r := whisker_square 1 1 bb 1.

Definition whisker_square_r {A : Type} {a00 a01 a10 a11 : A}
  {l : a00 = a01} {t : a00 = a10} {b : a01 = a11} {r r' : a10 = a11}
  (rr : r = r') :
  Square l t b r -> Square l t b r' := whisker_square 1 1 1 rr.

(** Composition of squares *)
(**
a00---- t ----a10---- t' ---a20
 |             |             |
 |             |             |
 l             r             r'
 |             |             |
 |             |             |
a01---- b ----a11---- b' ---a21
 |             |
 |             |
 l'            r'
 |             |
 |             |
a02---- b' ---a12
*)
Definition compose_v {A : Type} {a00 a01 a10 a11 a02 a12 : A}
  {l : a00 = a01} {t : a00 = a10} {b : a01 = a11} {r : a10 = a11}
  {l' : a01 = a02} {b' : a02 = a12} {r' : a11 = a12} :
  Square l t b r -> Square l' b b' r' -> Square (l @ l') t b' (r @ r').
Proof.
  induction 1. intros s.
  apply (transport (fun x => Square x 1 b' (1 @ r')) (concat_1p _)^).
  apply (transport (fun x => Square l' 1 b' x) (concat_1p _)^ s).
Defined.

Definition compose_h {A : Type} {a00 a01 a10 a11 a20 a21 : A}
  {l : a00 = a01} {t : a00 = a10} {b : a01 = a11} {r : a10 = a11}
  {t' : a10 = a20} {b' : a11 = a21} {r' : a20 = a21} :
  Square l t b r -> Square r t' b' r' -> Square l (t @ t') (b @ b') r'.
Proof.
  induction 1. intros s.
  apply (transport (fun x => Square 1 x (1 @ b') r') (concat_1p _)^).
  apply (transport (fun x => Square 1 t' x r') (concat_1p _)^ s).
Defined.

(* Notation "p @@ q" := (compose_h p q). *)
(* Notation "p 'oo' q" := (compose_v p q). *)

(* Lemma compose_v_1p {A : Type} {a00 a01 a10 a11 : A}    *)
(*   {l : a00 = a01} {t : a00 = a10} {b : a01 = a11} {r : a10 = a11} *)
(*   (s : Square l t b r) : compose_v vrefl s = s. *)

(** Square symmetry *)
(**
a00---- t ----a10   a00---- l ----a01
 |             |     |             |
 |             |     |             |
 l             r  ≃  t             b
 |             |     |             |
 |             |     |             |
a01---- b ----a11   a10---- r ----a11
*)

Definition square_sym {A : Type} {a00 a01 a10 a11 : A}
  {l : a00 = a01} {t : a00 = a10} {b : a01 = a11} {r : a10 = a11}
  (s : Square l t b r) : Square t l r b.
Proof. induction s. apply sid. Defined.

Instance isequiv_square_sym {A : Type} {a00 a01 a10 a11 : A}
  {l : a00 = a01} {t : a00 = a10} {b : a01 = a11} {r : a10 = a11} :
  IsEquiv (@square_sym A _ _ _ _ l t b r).
Proof.
  apply isequiv_biinv.
  split; exists square_sym; intros x; induction x; reflexivity.
Defined.

(** Kan fillings *)
Definition fill_horn {A : Type} {a00 a01 a10 a11 : A}
  (l : a00 = a01) (t : a00 = a10) (b : a01 = a11) :
  exists (r : a10 = a11), Square l t b r.
Proof.
  exists (t^ @ l @ b).
  apply square_disc.
  hott_simpl.
Defined.

(** * Circle *)

Definition S1_elim (P : S1 -> Type) (b : P base)
  (l : PathOver P loop b b) : forall x, P x.
Proof.
  hinduction.
  - apply b.
  - by apply pathover_transport.
Defined.

Definition S1_elim_beta (P : S1 -> Type) (b : P base)
  (l : PathOver P loop b b) : apdo (S1_elim P b l) loop = l.
Proof.
  rewrite <- transport_pathover_apD.
  unfold S1_elim. rewrite S1_ind_beta_loop.
  apply isequiv_transport_pathover.
Defined.
