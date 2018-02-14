From HoTT Require Export HoTT.
From HoTT Require Import Pointed HIT.Pushout.
Require Import vK.WedgeSum Circ HitTactics.

Definition concatD {A : Type} {P : A -> Type} {a b c : A} (f : a = b) (g : b = c) {x : P a} {y : P b} {z : P c} : forall (p : f # x = y) (q : g # y = z), (f @ g) # x = z.
Proof.
destruct f,g. exact concat.
  (* match f, g return (forall (p : f # x = y) (q : g # y = z), (f @ g) # x = z) *)
  (* with idpath,idpath => fun p q => p @ q end. *)
(* exact (p @ q). *)
Defined.
Notation "p @D q" := (concatD _ _ p%path q%path) (at level 20) : path_scope.
(* TODO: See exercise 6.1 *)

Definition apD2 {A : Type} {C : A -> Type} (f : forall x, C x)
  {x x' : A} {p p': x = x'}
  (θ : p = p') : (transport (fun q => q # f x = f x') θ (apD f p)) = (apD f p').
Proof.
induction θ. reflexivity.
Defined.

Lemma apD_concat {A : Type} {C : A -> Type} (f : forall x, C x) 
  {x y z : A} (p : x = y) (q : y = z) :
  apD f (p @ q) = apD f p @D apD f q.
Proof. induction p, q; simpl. reflexivity. Defined.
(* TODO: see apD_pp *)

Notation ap2 := ap02.
Notation ap2_concat := ap02_pp.

Module Export T.
Private Inductive T : Type0 :=
| b : T.
Axiom loop1 : b = b.
Axiom loop2 : b = b.
Axiom surf : loop1 @ loop2 = loop2 @ loop1.

Section T_ind.
  Variable P : T -> Type.
  Variable b' : P b.
  Variable p1 : loop1 # b' = b'.
  Variable p2 : loop2 # b' = b'.
  Variable s  : transport (fun p => p # b' = b') surf (p1 @D p2) = p2 @D p1.
                  
  Definition T_ind : forall x : T, P x := fun x =>
    match x return (_ -> _ -> _ -> P x) with
    | b => fun _ _ _ => b'
    end p1 p2 s.
  
  Axiom T_ind_beta_loop1 : apD T_ind loop1 = p1.
  Axiom T_ind_beta_loop2 : apD T_ind loop2 = p2.

  (* To formulate the computational rule for the surface we need to
     transport the LHS along some path. This is due to the fact that
     [apD_concat] and [T_ind_beta_loop_a/b] are only propositional
     equalities. *)
  Definition γ :
    (transport (fun q => q # b' = b') surf (apD T_ind (loop1 @ loop2)) = apD T_ind (loop2 @ loop1))
     =
    (transport (fun q => q # b' = b') surf (p1 @D p2) = p2 @D p1).
  Proof.
  etransitivity.
  { apply (ap (fun z => transport (fun q => q # b' = b') surf z = apD T_ind (loop2 @ loop1)) (apD_concat _ loop1 loop2)). }
  etransitivity.
  { apply (ap (fun z => transport (fun q => q # b' = b') surf (_ @D _) = z) (apD_concat _ loop2 loop1)). }
  etransitivity.
  { apply (ap (fun z => transport (fun q => q # b' = b') surf (z @D _) = _ @D z) T_ind_beta_loop1). }
  { apply (ap (fun z => transport (fun q => q # b' = b') surf (_ @D z) = z @D _) T_ind_beta_loop2). }
  Defined.

  Axiom T_ind_beta_surf : transport idmap γ (apD2 T_ind surf) = s.

End T_ind.

Section T_rec.
  Variable P : Type.
  Variable b' : P.
  Variable p1 p2 : b' = b'.
  Variable s : p1 @ p2 = p2 @ p1.
  
  Definition T_rec : T -> P. (* := fun x => *)
    (* match x return (_ -> _ -> _ -> P) with *)
    (* | baseT => fun _ _ _ => b' *)
    (* end p1 p2 s. *)
Proof.
  simple refine (T_ind (fun _ => P) b' _ _ _); simpl.
  - refine (transport_const _ _ @ p1).
  - refine (transport_const _ _ @ p2).
  - refine (transport_paths_FlFr surf _ @ _).
    refine (ap (fun z => _ @ z) (ap_const _ _) @ _).
    refine ((concat_p1 _) @ _).    
    
rewrite <- T_ind_beta_loop1.
Defined.

  Axiom T_rec_beta_loop1 : ap T_rec loop1 = p1.
  Axiom T_rec_beta_loop2 : ap T_rec loop2 = p2.
  

  Definition γrec : 
    (ap T_rec (loop1 @ loop2) = ap T_rec (loop2 @ loop1))
    =
    (p1 @ p2 = p2 @ p1).
  Proof.
  etransitivity.
  { apply (ap (fun z => z = _) (ap_pp _ _ _)). }
  etransitivity.
  { apply (ap (fun z => _ = z) (ap_pp _ _ _)). }
  etransitivity.
  { apply (ap (fun z => (z @ _) = (_ @ z)) T_rec_beta_loop1). }
  { apply (ap (fun z => (_ @ z) = (z @ _)) T_rec_beta_loop2). }
  Defined.
  

  Axiom T_rec_beta_surf : transport idmap γrec (ap2 T_rec surf) = s.
End T_rec.
End T.

Instance Torus_recursion : HitRecursion T := {
  indTy := _; recTy := _; 
  H_inductor := T_ind; H_recursor := T_rec }.

Section torus_subdivision.

Definition i1 : eight -> T.
Proof.
hrecursion.
- exact b.
- exact loop1.
- exact loop2.
Defined.

Definition i2 : Unit -> T := fun _ => b.

Definition e_circ : S1 -> eight.
Proof.
hrecursion.
- exact base8.
- exact (eight.loop1 @ eight.loop2 @ eight.loop1^ @ eight.loop2^).
Defined.

Definition T' : Type.
Proof.
  refine (@pushout S1 Unit eight _ _).
  - exact (fun _ => tt).
  - exact e_circ.
Defined.

Definition i : T' -> T. 
Proof. 
simple refine (pushout_rec T (sum_ind _ i2 i1) _).
hrecursion.
- cbv. reflexivity.
- rewrite transport_paths_FlFr. hott_simpl.
rewrite ap_compose.
rewrite S1_rec_beta_loop.
rewrite ?ap_pp. rewrite ?ap_V.
rewrite ?Eight_rec_beta_loop1.
rewrite ?Eight_rec_beta_loop2.
rewrite surf. hott_simpl.
Defined.

Definition j : T -> T'.
Proof.
hrecursion.
- exact (push  base). 
- simple refine (ap pushr _). apply loop.
- 
- rewrite <- (ap_pp (push o inr) eight.loop1 eight.loop2).
  rewrite <- (ap_pp (push o inr) eight.loop2 eight.loop1).
  
Defined.
End torus_subdivision.
