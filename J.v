(* ML identity type *)
Inductive Id {A : Type} : A -> A -> Type
  := refl : forall (a : A), @Id A a a.

(* Check Id_ind. *)
(* Check Id_rec. *)

(* Paulin-Mohring identity type *)

Inductive Path {A : Type} (M : A) : A -> Type
  := idpath : Path M M.

(* Check Path_ind. *)

(* The fibration 'Path A M x' over 'A' is ismorphic to
   \Sigma (x : A), x = M *)
Definition PathTo (A : Type) (M : A) := exists (y : A), Id y M.

Theorem PathTo_contr : forall A M (k : PathTo A M), Id k (exist _ M (refl M)).
Proof.
  intros A M k.  
  destruct k as [N p].
  induction p. apply refl.
Qed.
