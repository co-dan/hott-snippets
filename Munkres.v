Require Import HoTT.

Definition homotopic {A P} 
           (f : forall (x:A), P x) (g : forall (x : A), P x) :=
  forall x, f x = g x.

Notation "f ~ g" := (homotopic f g) (at level 85) : equiv_scope.

Theorem m51_1 : forall X Y Z (h h' : X -> Y) (k k' : Y -> Z),
  h ~ h' -> k ~ k' -> k o h ~ k' o h'. 
Proof.
  intros X Y Z h h' k k' H K.
  intro x. rewrite (H x). rewrite (K (h' x)).
  reflexivity.
Qed.

Theo
