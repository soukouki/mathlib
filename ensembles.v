(* 集合・位相入門(松坂)1 をCoqで証明しつつ読んでいく *)

From mathcomp Require Import ssreflect.

Module Ensembles.

Variable U: Type.

Definition Ensemble := U -> Prop.

Definition In (a: U) (A: Ensemble) := A a.
Notation "a \in A" := (In a A) (at level 11).

Definition EmptySet: Ensemble := fun _ => False.
Notation "\emptyset" := EmptySet.

(* 外延性の公理 *)
Axiom ensemble_eq: forall (A B: Ensemble),
  (forall (x: U), (x \in A <-> x \in B)) -> A = B.

Definition Subset (A B: Ensemble) := forall x, x \in A -> x \in B.
Notation "A \subset B" := (Subset A B) (at level 11).

(* (1.3) *)
Theorem eq_subset: forall A B, A = B <-> A \subset B /\ B \subset A.
Proof.
move=> A B.
split.
- move=> HA_eq_B.
  rewrite HA_eq_B.
  by rewrite /Subset.
- case.
  move=> HA_subset_B HB_subset_A.
  apply ensemble_eq => x.
  split.
  + by apply HA_subset_B.
  + by apply HB_subset_A.
Qed.

(* (1.4)
   本にあるのは A \subset B /\ B \subset C だけれど、明らかに同等な上にこちらのほうがCoq的に扱いやすいのでこう書いた
   今後も同じような例が出てくるが、同様に行う *)
Theorem subset_trans: forall A B C, A \subset B -> B \subset C -> A \subset C.
Proof.
move=> A B C HA_subset_B HB_subset_C.
rewrite /Subset => x Hx_in_A.
by apply /HB_subset_C /HA_subset_B.
Qed.

(* (1.5) *)
Theorem empty_set_subset: forall A, \emptyset \subset A.
Proof.
by rewrite /Subset /In /EmptySet.
Qed.


Definition Cup (A B: Ensemble) := fun x: U => x \in A \/ x \in B.
Notation "A \cup B" := (Cup A B) (at level 10).

(* (2.2.1) *)
Theorem subset_cup_l: forall A B, A \subset A \cup B.
Proof.
by left.
Qed.

(* (2.2.2) *)
Theorem subset_cup_r: forall A B, B \subset A \cup B.
Proof.
move=> A B.
by right.
Qed.

(* 2.3 *)
Theorem subsets_cup: forall A B C, A \subset C -> B \subset C -> A \cup B \subset C.
Proof.
move=> A B C HA_subset_C HB_subset_C.
rewrite /Cup /In => x.
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

(* (2.5) *)
Theorem cup_comm: forall A B, A \cup B = B \cup A.
Proof.
move=> A B.
apply eq_subset.
split.
- rewrite /Cup /Subset /In => x.
  by apply or_comm.
- rewrite /Cup /Subset /In => x.
  by apply or_comm.
Qed.

(* (2.6) *)
Theorem cup_assoc: forall A B C, (A \cup B) \cup C = A \cup (B \cup C).
Proof.
move=> A B C.
apply eq_subset.
split.
- rewrite /Subset /Cup /In.
  move=> x.
  by apply or_assoc.
- rewrite /Subset /Cup /In.
  move=> x.
  by apply or_assoc.
Qed.

(* (2.7) *)
Theorem subset_cup_eq: forall A B, A \subset B <-> A \cup B = B.
Proof.
move=> A B.
split.
- move=> HA_subset_B.
  apply eq_subset.
  split.
  + by apply subsets_cup => //.
  + by apply subset_cup_r.
- move=> H; rewrite -H.
  by apply subset_cup_l.
Qed.

(* (2.8) *)
Theorem subset_cups_subset: forall A B C, A \subset B -> A \cup C \subset B \cup C.
Proof.
move=> A B C HA_subset_B.
apply subsets_cup.
- rewrite /Subset /Cup /In.
  move=> x HA.
  left.
  by apply HA_subset_B.
- by apply subset_cup_r.
Qed.

(* (2.9) *)
Theorem empty_set_cup: forall A, \emptyset \cup A = A.
move=> A.
by apply subset_cup_eq.
Qed.


Definition Cap (A B: Ensemble) := fun x: U => x \in A /\ x \in B.
Notation "A \cap B" := (Cap A B) (at level 10).

(* (2.2.1)'
   本ではsupsetを使っているが、今回はすべてsubsetで統一する *)
Theorem cap_subset_l: forall A B, A \cap B \subset A.
Proof.
move=> A B.
rewrite /Subset /Cap /In.
move=> x.
by case.
Qed.

(* (2.2.2)' *)
Theorem cap_subset_r: forall A B, A \cap B \subset B.
Proof.
move=> A B.
rewrite /Subset /Cap /In.
move=> x.
by case.
Qed.

(* (2.3)' *)
Theorem subsets_cap: forall A B C, C \subset A -> C \subset B -> C \subset A \cap B.
Proof.
move=> A B C HC_subset_A HC_subset_B.
rewrite /Subset /Cap /In.
move=> x.
split.
- by apply HC_subset_A.
- by apply HC_subset_B.
Qed.

(* (2.4)' *)
Theorem cap_diag: forall A, A \cap A = A.
Proof.
move=> A.
apply eq_subset.
split.
- rewrite /Subset /Cap /In.
  move=> x.
  by case.
- rewrite /Subset /Cap /In.
  move=> x.
  by split => //.
Qed.

(* (2.5)' *)
Theorem cap_comm: forall A B, A \cap B = B \cap A.
Proof.
move=> A B.
apply eq_subset.
split.
- rewrite /Subset /Cap /In.
  move=> x.
  by apply and_comm.
- rewrite /Subset /Cap /In.
  move=> x.
  by apply and_comm.
Qed.

(* (2.6)' *)
Theorem cap_assoc: forall A B C, (A \cap B) \cap C = A \cap (B \cap C).
Proof.
move=> A B C.
apply eq_subset.
split.
- rewrite /Subset /Cap /In.
  move=> x.
  by apply and_assoc.
- rewrite /Subset /Cap /In.
  move=> x.
  by apply and_assoc.
Qed.

(* (2.7)' *)
Theorem subset_cap_eq: forall A B, A \subset B <-> A \cap B = A.
Proof.
move=> A B.
split.
- move=> HA_subset_B.
  apply eq_subset.
  split.
  + by apply cap_subset_l.
  + by apply subsets_cap => //.
- move=> H; rewrite -H.
  by apply cap_subset_r.
Qed.

(* (2.8)' *)
Theorem subset_caps_subset: forall A B C, A \subset B -> A \cap C \subset B \cap C.
Proof.
move=> A B C HA_subset_B.
apply subsets_cap.
- rewrite /Subset /Cap /In.
  move=> x.
  case => HA HC.
  by apply HA_subset_B.
- by apply cap_subset_r.
Qed.

(* (2.9)' *)
Theorem empty_set_cap: forall A, \emptyset \cap A = \emptyset.
Proof.
move=> A.
by apply subset_cap_eq.
Qed.






















