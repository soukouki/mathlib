(* 集合・位相入門(松坂)1 をCoqで証明しつつ読んでいく *)

From mathcomp Require Import ssreflect.
Require Import Classical.

Module Ensembles.

Section Section1.

Variable T: Type.

Definition Ensemble := T -> Prop.

Definition In (a: T) (A: Ensemble): Prop := A a.
Notation "a \in A" := (In a A) (at level 55).

Definition EmptySet: Ensemble := fun _ => False.
Notation "\emptyset" := EmptySet.

(* 外延性の公理 *)
Axiom eq_axiom: forall (A B: Ensemble),
  (forall (x: T), (x \in A <-> x \in B)) -> A = B.

Definition Subset (A B: Ensemble): Prop := forall x: T, x \in A -> x \in B.
Notation "A \subset B" := (Subset A B) (at level 55).

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
  apply eq_axiom => x.
  split.
  + by apply HA_subset_B.
  + by apply HB_subset_A.
Qed.

Lemma eq_subset': forall A B, A \subset B -> B \subset A -> A = B.
Proof.
move=> A B HAB HBA.
apply eq_subset => //.
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


Definition Cup (A B: Ensemble): Ensemble := fun x: T => x \in A \/ x \in B.
Notation "A \cup B" := (Cup A B) (at level 50).

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
apply eq_subset'.
- by apply subsets_cup => //.
- by apply subset_cup_l.
Qed.

(* (2.5) *)
Theorem cup_comm: forall A B, A \cup B = B \cup A.
Proof.
move=> A B.
apply eq_subset'.
- rewrite /Cup /Subset /In => x.
  by apply or_comm.
- rewrite /Cup /Subset /In => x.
  by apply or_comm.
Qed.

(* (2.6) *)
Theorem cup_assoc: forall A B C, (A \cup B) \cup C = A \cup (B \cup C).
Proof.
move=> A B C.
apply eq_subset'.
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
  apply eq_subset'.
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


Definition Cap (A B: Ensemble): Ensemble := fun x: T => x \in A /\ x \in B.
Notation "A \cap B" := (Cap A B) (at level 50).

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
apply eq_subset'.
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
apply eq_subset'.
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
apply eq_subset'.
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
  apply eq_subset'.
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

(* (2.10) *)
Theorem cup_cap_distrib: forall A B C, (A \cup B) \cap C = (A \cap C) \cup (B \cap C).
Proof.
move=> A B C.
apply eq_subset'.
- rewrite /Subset /Cup /Cap /In => x.
  case.
  case.
  + move=> HA HC.
    left.
    by split => //.
  + move=> HB HC.
    right.
    by split => //.
- rewrite /Subset /Cup /Cap /In => x.
  case.
  + case => HA HC.
    split => //.
    by left.
  + case => HB HC.
    split => //.
    by right.
Qed.

(* (2.11) *)
Theorem cap_cup_distrib: forall A B C, (A \cap B) \cup C = (A \cup C) \cap (B \cup C).
Proof.
move=> A B C.
apply eq_subset'.
- rewrite /Subset /Cup /Cap /In => x.
  case.
  + case => HA HB.
    split.
    * by left.
    * by left.
  + move=> HC.
    split.
    * by right.
    * by right.
- rewrite /Subset /Cup /Cap /In => x.
  case.
  case.
  + move=> HA.
    case.
    * by left.
    * by right.
  + by right.
Qed.

(* (2.11) *)
Theorem cup_absorption: forall A B, (A \cup B) \cap A = A.
Proof.
move=> A B.
rewrite cap_comm.
apply subset_cap_eq.
by apply subset_cup_l.
Qed.

(* (2.11)' *)
Theorem cap_absorption: forall A B, (A \cap B) \cup A = A.
Proof.
move=> A B.
apply subset_cup_eq.
by apply cap_subset_l.
Qed.


Definition Sub (A B: Ensemble) := fun x: T => x \in A /\ ~ x \in B.
Notation "A - B" := (Sub A B). (* at level 50 *)

Definition FullSet: Ensemble := fun _ => True.

Definition ComplementarySet (A: Ensemble) := FullSet - A.
Notation "A ^ 'c'" := (ComplementarySet A) (at level 30).

Lemma complementary_set: forall A, A^c = fun x => ~ x \in A.
Proof.
move=> A.
apply eq_subset'.
- rewrite /ComplementarySet /Sub /Subset /In => x.
  by case.
- rewrite /ComplementarySet /Sub /Subset /In => x.
  by split => //.
Qed.

Lemma complementary_set_in: forall A x, x \in A^c <-> ~ x \in A.
Proof.
move=> A x.
by rewrite complementary_set.
Qed.

(* (2.12.1) *)
Theorem complementary_set_cup: forall A, A \cup A^c = FullSet.
Proof.
move=> A.
apply eq_axiom => x.
split => // _.
rewrite complementary_set /Cup /In.
by apply classic. (* ここで古典論理を使い始めた *)
Qed.

(* (2.12.2) *)
Theorem complementary_set_cap: forall A, A \cap A^c = EmptySet.
Proof.
move=> A.
apply eq_axiom => x.
split => //.
rewrite complementary_set /Cap /In.
by case.
Qed.

(* (2.13) *)
Theorem complementary_set_twice: forall A, A^c^c = A.
Proof.
move=> A.
apply eq_axiom => x.
rewrite 2!complementary_set_in.
rewrite /In.
split.
- by apply NNPP.
- by move=> H.
Qed.

(* (2.14.1) *)
Theorem complementary_set_empty_set: EmptySet^c = FullSet.
Proof.
apply eq_axiom => x.
split => // _.
by rewrite complementary_set_in.
Qed.

(* (2.14.2) *)
Theorem complementary_set_full_set: FullSet^c = EmptySet.
Proof.
apply eq_axiom => x.
split => //.
by rewrite complementary_set_in /FullSet /In.
Qed.

(* (2.15) これどうして証明できたのかよくわからない *)
Theorem complementary_set_subset: forall A B, A \subset B <-> B^c \subset A^c.
Proof.
move=> A B.
split.
- rewrite 2!complementary_set /Subset => HA_to_B x.
  rewrite {1}/In /not => HB HA.
  apply HB.
  by apply HA_to_B.
- rewrite 2!complementary_set /Subset {1 3}/In => HB_to_A x HA.
  move: (HB_to_A x).
  rewrite /not.
  move=> H.
  apply NNPP.
  rewrite /not.
  move=> HB.
  apply H => //.
Qed.


(* (2.16) *)
Theorem de_morgan_cup: forall A B, (A \cup B)^c = A^c \cap B^c.
Proof.
(* eq_subset'を使ったあとでrewriteしまくる形でもできるけれど、形式化に左右されづらいこの形式にした *)
move=> A B.
apply eq_axiom => x.
split.
- rewrite complementary_set_in /Cup {1}/In => HA_or_B.
  rewrite /Cap {1}/In.
  rewrite 2!complementary_set_in.
  split.
  + move=> HA.
    apply HA_or_B.
    by left.
  + move=> HB.
    apply HA_or_B.
    by right.
- rewrite complementary_set_in /Cup {2}/In.
  case => HA HB.
  case.
  + by apply HA.
  + by apply HB.
Qed.

(* (2.16)' *)
Theorem de_morgan_cap: forall A B, (A \cap B)^c = A^c \cup B^c.
Proof.
move=> A B.
apply eq_axiom => x.
split.
- rewrite complementary_set_in /Cap {1}/In => HA_and_B.
  rewrite /Cup {1}/In.
  rewrite 2!complementary_set_in.
  by apply not_and_or.
- rewrite /Cup {1}/In 3!complementary_set_in.
  case => H HA_cap_B.
  + apply H.
    apply HA_cap_B.
  + apply H.
    apply HA_cap_B.
Qed.

End Section1.

Section Section2.

Variable T: Type.

Variable FamilyEnsemble: (Ensemble (Ensemble T)).

Variable Ensemble: Ensemble T.

Definition CAP (A: FamilyEnsemble): Ensemble := 




















