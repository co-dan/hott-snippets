From HoTT Require Import HoTT HIT.Truncations.

(** If ||Σ n, f n = 0||, then Σ n, f n = 0 *)
(** This method is similar to the "ConstructiveEpsilon" in Coq, adapted to HoTT/hProp. It can be further generalized to arbitrary decidable hProps. *)
Section contents.
  Context `{Univalence}.
  Variable f : nat -> nat.

  Hypothesis root : Trunc -1 (sig (fun n => f n = 0)).

  Inductive rootD : nat -> Type :=
  | is_root : forall {n}, f n = 0 -> rootD n
  | root_step : forall {n}, f n <> 0 -> rootD (S n) -> rootD n.

  (* Here we use the fact that 'nat' is an hset, hence
     ||f n = 0|| = (f n = 0) *)
  Instance rootD_hprop n : IsHProp (rootD n).
  Proof.
    apply hprop_allpath.
    intros x y. induction y as [n p|n p].
    - destruct x as [n q|n q].
      + f_ap. apply path_ishprop.
      + refine (Empty_rec (q p)).
    - destruct x as [n q|n q].
      + refine (Empty_rec (p q)).
      + f_ap. apply path_ishprop.
  Defined.

  Lemma rootD_step n (y : rootD n) (w : ~ (f n = 0)) : rootD (S n).
  Proof.
    induction y.
    - refine (Empty_rec (w p)).
    - apply y.
  Defined.

  Fixpoint search n (w : rootD n) {struct w} : sig (fun n => f n = 0).
  Proof.
    destruct (dec_paths (f n) 0) as [p | p].
    - exists n. apply p.
    - apply (search (S n)).
      apply rootD_step; assumption.
  Defined.

  Lemma downclosure n : rootD n -> rootD 0.
  Proof.
    induction n.
    - exact idmap.
    - intros Hr. apply IHn.
      destruct (dec_paths (f n) 0) as [p | p].
      + by apply is_root.
      + by apply root_step.
  Defined.

  Theorem witness : sig (fun n => f n = 0).
  Proof.
    apply (search 0).
    strip_truncations.
    destruct root as [n Hroot].
    apply (downclosure n).
    by apply is_root.
  Defined.

End contents.

