(* 集合・位相入門(松坂)1 をCoqで証明しつつ読んでいく *)

From mathcomp Require Import ssreflect.

Module Ensembles.

Variable U: Type.

Definition Ensemble := U -> Prop.

Definition In (a: U) (A: Ensemble) := A a.

Notation "a \in A" := (In a A) (at level 11).

(* 外延性の公理 *)
Axiom ensemble_eq: forall (A B: Ensemble),
  (forall (x: U), (x \in A <-> x \in B)) -> A = B.

Definition Subset (A B: Ensemble) := forall x, x \in A -> x \in B.

Notation "A \subset B" := (Subset A B) (at level 11).

Theorem eq_subset: forall (A B: Ensemble), A = B <-> A \subset B /\ B \subset A.
Proof.
move=> A B.
split.
- move=> HA_eq_B.
  split.
  + rewrite /Subset.
    move=> x Hx_in_A.
    by rewrite -HA_eq_B.
  + rewrite /Subset.
    move=> x Hx_in_B.
    by rewrite HA_eq_B.
- case.
  move=> HA_subset_B HB_subset_A.
  apply ensemble_eq.
  move=> x.
  split.
  + move=> Hx_in_A.
    by apply HA_subset_B.
  + move=> Hx_in_B.
    by apply HB_subset_A.
Qed.







