(* 集合・位相入門(松坂)1 をCoqで証明しつつ読んでいく *)

From mathcomp Require Import ssreflect.

Module Ensembles.

Variable U: Type.

Definition Ensemble := U -> Prop.

Definition In (a: U) (A: Ensemble) := A a.
Notation "a \in A" := (In a A) (at level 11).

Definition EmptySet: Ensemble := fun _ => False.

(* 外延性の公理 *)
Axiom ensemble_eq: forall (A B: Ensemble),
  (forall (x: U), (x \in A <-> x \in B)) -> A = B.

Definition Subset (A B: Ensemble) := forall x, x \in A -> x \in B.
Notation "A \subset B" := (Subset A B) (at level 11).

(* (1.3) *)
Theorem eq_subset: forall (A B: Ensemble), A = B <-> A \subset B /\ B \subset A.
Proof.
move=> A B.
split.
- move=> HA_eq_B.
  split.
  + rewrite HA_eq_B.
    by rewrite /Subset.
  + rewrite HA_eq_B.
    by rewrite /Subset.
- case.
  move=> HA_subset_B HB_subset_A.
  apply ensemble_eq.
  move=> x.
  split.
  + by apply HA_subset_B.
  + by apply HB_subset_A.
Qed.

(* (1.4)
   本にあるのは A \subset B /\ B \subset C だけれど、明らかに同等な上にこちらのほうがCoq的に扱いやすいのでこう書いた
   今後も同じような例が出てくるが、同様に行う *)
Theorem subset_trans: forall (A B C: Ensemble), A \subset B -> B \subset C -> A \subset C.
Proof.
move=> A B C HA_subset_B HB_subset_C.
rewrite /Subset.
move=> x Hx_in_A.
by apply /HB_subset_C /HA_subset_B.
Qed.

(* (1.5) *)
Theorem empty_set_subset: forall A: Ensemble, EmptySet \subset A.
Proof.
move=> A.
rewrite /Subset.
move=> x.
rewrite /In.
by rewrite /EmptySet.
Qed.

Definition Cup (A B: Ensemble) := fun x: U => x \in A \/ x \in B.
Notation "A \cup B" := (Cup A B) (at level 10).

(* (2.2.1) *)
Theorem subset_cup_l: forall (A B: Ensemble), A \subset A \cup B.
Proof.
move=> A B.
rewrite /Subset.
move=> x Hx_in_A.
rewrite /Cup /In.
by left.
Qed.

(* (2.2.2) *)
Theorem subset_cup_r: forall (A B: Ensemble), B \subset A \cup B.
Proof.
move=> A B.
rewrite /Subset.
move=> x Hx_in_B.
rewrite /Cup /In.
by right.
Qed.

(* 2.3 *)
Theorem subsets_cup: forall (A B C: Ensemble), A \subset C -> B \subset C -> A \cup B \subset C.
Proof.
move=> A B C HA_subset_C HB_subset_C.
rewrite /Subset /Cup /In.
move=> x.
case.
- by apply /HA_subset_C.
- by apply /HB_subset_C.
Qed.

(* (2.4) *)
Theorem cup_diag: forall A, A \cup A = A.
Proof.
move=> A.
apply eq_subset.
split.
- by apply subsets_cup => //.
- by apply subset_cup_l.
Qed.

Search (forall a, _ a a = _).

(* (2.5) *)
Theorem cup_comm: forall (A B: Ensemble), A \cup B = B \cup A.
Proof.
move=> A B.
Search Ensemble (_ = _).
apply eq_subset.
split.
- rewrite /Cup /Subset /In.
  move=> x.
  by apply or_comm.
- rewrite /Cup /Subset /In.
  move=> x.
  by apply or_comm.
Qed.
















