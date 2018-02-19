Require Import HoTT.
Require Import Circ HitTactics.

(** * PathOver *)
Inductive PathOver {A : Type} (C : A -> Type) {a1 : A} :
  forall {a2 : A}, (a1 = a2) -> C a1 -> C a2 -> Type :=
| pid : forall {c : C a1}, PathOver C idpath c c.
Arguments pid {_ _ _ _}.

Instance PathOver_reflexive {A : Type} (C : A -> Type) a : Reflexive (PathOver C (idpath a)).
Proof. intros c. apply pid. Defined.

Definition apdo {A : Type} {C : A -> Type} (f : forall a, C a) {a b : A} (p : a = b) : PathOver C p (f a) (f b) :=
  match p with idpath => pid end.

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

Definition PathOver_const_out {A P : Type} {a b : A} {p : a = b} {x y : P} :
  PathOver (fun (_ : A) => P) p x y -> x = y :=
  fun x => match x with pid _ => idpath end.

Definition PathOver_const_in {A P : Type} {a b : A} {p : a = b} {x y : P} :
  x = y -> PathOver (fun (_ : A) => P) p x y :=
  fun q => match p,q with idpath,idpath => pid end.

Lemma PathOver_const {A P : Type} (x y : P) {a b : A} (p : a = b) :
  x = y <~> PathOver (fun (_ : A) => P) p x y.
Proof.
  simple refine (BuildEquiv _ _ _ _).
  - apply PathOver_const_in.
  - apply isequiv_biinv. split; exists PathOver_const_out.
    + intros q. induction p,q. reflexivity.
    + intros q. induction q. reflexivity.
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

Lemma Square_ind_vert (A : Type) (a b : A) (p : a = b)
  (P : forall q, Square 1 p q 1 -> Type) (HP : P p vrefl) : forall q x, P q x.
Proof. Abort. (* TODO *)
  
(** PathOver in a path space is a square *)
(** 

f a1----- q1 ----g a1         Σa. fa = ga
  |               |
  |               |               |
ap f p          ap g p            |
  |               |               |
  |               |               v
f a2----- q2 ----g a2             A

*)
Definition PathOver_paths_out {A B : Type} {f g : A -> B}
      {a1 a2 : A} {p : a1 = a2}
      {q1 : f a1 = g a1}
      {q2 : f a2 = g a2} :
  PathOver (fun a => f a = g a) p q1 q2 ->
  Square (ap f p) q1 q2 (ap g p).
Proof. induction 1. apply vrefl. Defined.
Definition PathOver_paths_in {A B : Type} {f g : A -> B}
      {a1 a2 : A} {p : a1 = a2}
      {q1 : f a1 = g a1}
      {q2 : f a2 = g a2} :
  Square (ap f p) q1 q2 (ap g p) ->
  PathOver (fun a => f a = g a) p q1 q2.
Proof.
  induction p. simpl. Abort.
  (* TODO: apply Square_ind_vert. *)
(* Lemma PathOver_paths {A B : Type} {f g : A -> B} *)
(*       {a1 a2 : A} {p : a1 = a2} *)
(*       {α : f a1 = g a1} *)
(*       {β : f a2 = g a2} : *)
(*   Square (ap f p) α β (ap g p) <~> *)
(*   PathOver (fun a => f a = g a) p α β. *)
(* Proof. *)
(*   simple refine (BuildEquiv _ _ _ _). *)
(*   - apply PathOver_paths_in. *)
(*   - apply isequiv_biinv. split; exists PathOver_paths_out. *)


(** Image of a aquare under f *)
Definition ap_square {A B : Type} (f : A -> B) {a00 a01 a10 a11 : A}
  {l : a00 = a01} {t : a00 = a10} {b : a01 = a11} {r : a10 = a11} :
  Square l t b r -> Square (ap f l) (ap f t) (ap f b) (ap f r).
Proof.
  intros s. induction s. simpl. apply sid.
Defined.

(** Product of two squares *)
Definition square_prod {A B : Type}
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
Definition fill_sq {A : Type} {a00 a01 a10 a11 : A}
  (l : a00 = a01) (t : a00 = a10) (b : a01 = a11) :
  exists (r : a10 = a11), Square l t b r.
Proof.
  exists (t^ @ l @ b).
  apply square_disc.
  hott_simpl.
Defined.

(** Inverses and composition from Kan filling *)
Definition inv_filler {A : Type} {a b : A} (p : a = b) : b = a
  := (fill_sq 1 p 1).1.
Definition comp_filler {A : Type} {a b c : A} (p : a = b) (q : b = c) : a = c
  := (fill_sq p 1 q).1.

(** Square over a square *)
Inductive SquareOver {A : Type} (B : A -> Type)
  {a00 : A} {b00 : B a00} : forall {a01 a10 a11 : A}
  {l : a00 = a01} {t : a00 = a10} {b : a01 = a11} {r : a10 = a11}
  (s : Square l t b r)
  {b01 b10 b11}
  (bl : PathOver B l b00 b01)
  (bt : PathOver B t b00 b10)
  (bb : PathOver B b b01 b11)
  (br : PathOver B r b10 b11), Type :=
soid : SquareOver B sid pid pid pid pid.

Definition SquareOver_const_out {A P : Type}
  {a00 a01 a10 a11 : A}
  {l : a00 = a01} {t : a00 = a10} {b : a01 = a11} {r : a10 = a11}
  {s : Square l t b r}
  {p00 p01 p10 p11 : P}
  {ppl : PathOver (fun _ => P) l p00 p01}
  {ppt : PathOver (fun _ => P) t p00 p10}
  {ppb : PathOver (fun _ => P) b p01 p11}
  {ppr : PathOver (fun _ => P) r p10 p11} :
  SquareOver (fun (_ : A) => P) s ppl ppt ppb ppr ->
  Square
    (PathOver_const_out ppl)
    (PathOver_const_out ppt)
    (PathOver_const_out ppb)
    (PathOver_const_out ppr).
Proof. induction 1. reflexivity. Defined.

Definition SquareOver_const_in {A P : Type}
  {a00 a01 a10 a11 : A}
  {l : a00 = a01} {t : a00 = a10} {b : a01 = a11} {r : a10 = a11}
  {s : Square l t b r}
  {p00 p01 p10 p11 : P}
  {l' : p00 = p01} {t' : p00 = p10} {b' : p01 = p11} {r' : p10 = p11} :
  Square l' t' b' r' ->
  SquareOver (fun (_ : A) => P) s
    (PathOver_const_in l')
    (PathOver_const_in t')
    (PathOver_const_in b')
    (PathOver_const_in r').
Proof. induction 1. induction s. reflexivity. Defined.

Definition SquareOver_const_out' {A P : Type}
  {a00 a01 a10 a11 : A}
  {l : a00 = a01} {t : a00 = a10} {b : a01 = a11} {r : a10 = a11}
  {s : Square l t b r}
  {p00 p01 p10 p11 : P}
  {l' : p00 = p01} {t' : p00 = p10} {b' : p01 = p11} {r' : p10 = p11} :
  SquareOver (fun (_ : A) => P) s
    (PathOver_const _ _ _ l')
    (PathOver_const _ _ _ t')
    (PathOver_const _ _ _ b')
    (PathOver_const _ _ _ r') ->
  Square l' t' b' r'.
Proof.
  intros so.
  assert (l' = PathOver_const_out (p:=l) (PathOver_const_in l')) as ->. 
  { symmetry.
    change ((PathOver_const _ _ l)^-1 (PathOver_const _ _ l l') = l'). 
    apply eissect. }
  assert (t' = PathOver_const_out (p:=t) (PathOver_const_in t')) as ->. 
  { symmetry.
    change ((PathOver_const _ _ t)^-1 (PathOver_const _ _ t t') = t'). 
    apply eissect. }
  assert (b' = PathOver_const_out (p:=b) (PathOver_const_in b')) as ->. 
  { symmetry.
    change ((PathOver_const _ _ b)^-1 (PathOver_const _ _ b b') = b'). 
    apply eissect. }
  assert (r' = PathOver_const_out (p:=r) (PathOver_const_in r')) as ->. 
  { symmetry.
    change ((PathOver_const _ _ r)^-1 (PathOver_const _ _ r r') = r'). 
    apply eissect. }
  eapply SquareOver_const_out. exact so.
Defined.

Definition SquareOver_const (A P : Type)
  {a00 a01 a10 a11 : A}
  {l : a00 = a01} {t : a00 = a10} {b : a01 = a11} {r : a10 = a11}
  (s : Square l t b r)  
  {p00 p01 p10 p11 : P}
  {l' : p00 = p01} {t' : p00 = p10} {b' : p01 = p11} {r' : p10 = p11} :
  Square l' t' b' r'
    <~>
  SquareOver (fun (_ : A) => P) s 
    (PathOver_const _ _ _ l')
    (PathOver_const _ _ _ t')
    (PathOver_const _ _ _ b')
    (PathOver_const _ _ _ r').
Proof.
  simple refine (BuildEquiv _ _ _ _).
  - apply SquareOver_const_in.
  - apply isequiv_biinv. split;
    exists SquareOver_const_out'.
    + intros q. induction s,q. simpl. compute. reflexivity.
    + intros q. simpl in q. Abort.

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

(** * Torus *)
Module Export torus.
Private Inductive T : Type :=
  | a : T.
Axiom p : a = a.
Axiom q : a = a.
Axiom f : Square p q q p.

Definition T_ind (P : T -> Type)
  (a' : P a) (p' : PathOver P p a' a') (q' : PathOver P q a' a')
  (f' : SquareOver P f p' q' q' p')
  (x : T) : P x
  := (match x return _ -> _ -> _ -> P x with
        | a => fun _ _ _ => a'
      end) p q f.

Definition T_rec (P : Type) (a' : P) (p' q' : a' = a') (f' : Square p' q' q' p') (t : T) : P.
Proof.
  simple refine (T_ind (fun _ => P) a' _ _ _ t).
  - apply PathOver_const. exact p'.
  - apply PathOver_const. exact q'.
  - simpl. apply SquareOver_const_in. exact f'.
Defined.

End torus.

