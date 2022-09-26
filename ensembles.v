(* 集合・位相入門(松坂)1 をCoqで証明しつつ読んでいく *)

From mathcomp Require Import ssreflect.
Require Import Classical.

Module Ensembles.

Section Section1.

Variable T: Type.

Definition Ensemble := T -> Prop.

Definition In (a: T) (A: Ensemble): Prop := A a.
Notation "a \in A" := (In a A) (at level 55).

Inductive EmptySet: Ensemble := .
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
by move=> A.
Qed.


Inductive Cup (A B: Ensemble): Ensemble :=
  | Cup_introl: forall x: T, x \in A -> x \in Cup A B
  | Cup_intror: forall x: T, x \in B -> x \in Cup A B.
Notation "A \cup B" := (Cup A B) (at level 50).

(* (2.2.1) *)
Theorem subset_cup_l: forall A B, A \subset A \cup B.
Proof.
by left.
Qed.

(* (2.2.2) *)
Theorem subset_cup_r: forall A B, B \subset A \cup B.
Proof.
by right.
Qed.

Lemma cup_or: forall A B x, x \in A \/ x \in B <-> x \in A \cup B.
Proof.
move=> A B x.
split.
- case => H.
  + by left.
  + by right.
- case => x' H.
  + by left.
  + by right.
Qed.

(* 2.3 *)
Theorem subsets_cup: forall A B C, A \subset C -> B \subset C -> A \cup B \subset C.
Proof.
move=> A B C HA_subset_C HB_subset_C.
rewrite /Subset => x1.
case => x2.
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
apply eq_subset' => x;
  rewrite -2!cup_or;
  by rewrite or_comm.
Qed.

(* (2.6) *)
Theorem cup_assoc: forall A B C, (A \cup B) \cup C = A \cup (B \cup C).
Proof.
move=> A B C.
apply eq_subset' => x;
  rewrite -4!cup_or;
  by rewrite or_assoc.
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
- left.
  by apply HA_subset_B.
- by apply subset_cup_r.
Qed.

(* (2.9) *)
Theorem empty_set_cup: forall A, \emptyset \cup A = A.
Proof.
move=> A.
by apply subset_cup_eq.
Qed.


Inductive Cap (B C: Ensemble): Ensemble :=
  Cap_intro: forall x: T, x \in B -> x \in C -> x \in (Cap B C).
Notation "A \cap B" := (Cap A B) (at level 50).

(* (2.2.1)'
   本ではsupsetを使っているが、今回はすべてsubsetで統一する *)
Theorem cap_subset_l: forall A B, A \cap B \subset A.
Proof.
move=> A B x.
by case.
Qed.

(* (2.2.2)' *)
Theorem cap_subset_r: forall A B, A \cap B \subset B.
Proof.
move=> A B x.
by case.
Qed.

Lemma cap_and: forall A B x, x \in A /\ x \in B <-> x \in A \cap B.
Proof.
move=> A B x.
split;
  by case.
Qed.

(* (2.3)' *)
Theorem subsets_cap: forall A B C, C \subset A -> C \subset B -> C \subset A \cap B.
Proof.
move=> A B C HC_subset_A HC_subset_B x.
split.
- by apply HC_subset_A.
- by apply HC_subset_B.
Qed.

(* (2.4)' *)
Theorem cap_diag: forall A, A \cap A = A.
Proof.
move=> A.
apply eq_subset' => x;
  rewrite -cap_and.
- by case.
- by split => //.
Qed.

(* (2.5)' *)
Theorem cap_comm: forall A B, A \cap B = B \cap A.
Proof.
move=> A B.
apply eq_subset' => x;
  rewrite -2!cap_and.
- by rewrite and_comm.
- by case.
Qed.

(* (2.6)' *)
Theorem cap_assoc: forall A B C, (A \cap B) \cap C = A \cap (B \cap C).
Proof.
move=> A B C.
apply eq_subset' => x;
  rewrite -4!cap_and;
  by rewrite and_assoc.
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
apply subsets_cap => x1.
- case => x2 HA HC.
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
apply eq_axiom => x1.
split.
- case => x2.
  case => x3 H HC.
  + left.
    by split => //.
  + right.
    by split => //.
- case => x2.
  + case => x3 HA HC.
    split => //.
    by left.
  + case => x3 HB HC.
    split => //.
    by right.
Qed.

(* (2.11) *)
Theorem cap_cup_distrib: forall A B C, (A \cap B) \cup C = (A \cup C) \cap (B \cup C).
Proof.
move=> A B C.
apply eq_axiom => x1.
split.
- case => x2.
  + case => x3 HA HB.
    split; by left.
  + split; by right.
- case => x2.
  + case => x3 H HBC.
    move: HBC H.
    case => x4 H HA.
    * left.
      split => //.
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


Inductive Sub (A B: Ensemble): Ensemble :=
  | Sub_intro: forall x: T, x \in A -> ~ x \in B -> x \in Sub A B.
Notation "A - B" := (Sub A B). (* at level 50 *)

Lemma sub_empty_set: forall A, A - \emptyset = A.
Proof.
move=> A.
apply eq_axiom => x.
split.
- by case.
- by split => //.
Qed.

Lemma empty_set_sub: forall A, \emptyset - A = \emptyset.
Proof.
move=> A.
apply eq_axiom => x.
split => //.
by case.
Qed.

Inductive FullSet: Ensemble :=
  | FullSet_intro: forall x, x \in FullSet.

Lemma full_set_cap: forall A, FullSet \cap A = A.
Proof.
move=> A.
by rewrite cap_comm -subset_cap_eq.
Qed.

Lemma full_set_cup: forall A, FullSet \cup A = FullSet.
Proof.
move=> A.
by rewrite cup_comm -subset_cup_eq.
Qed.

Inductive ComplementarySet (A: Ensemble): Ensemble :=
  | ComplementarySet_intro: forall x, x \in FullSet - A -> x \in ComplementarySet A.
Notation "A ^ 'c'" := (ComplementarySet A) (at level 30).

Lemma complementary_set: forall A, A^c = fun x => ~ x \in A.
Proof.
move=> A.
apply eq_subset'.
- move=> x1 HA.
  case HA => x2.
  by case.
- split.
  split => //.
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
rewrite -cup_or.
rewrite complementary_set.
by apply classic. (* ここで古典論理を使い始めた *)
Qed.

(* (2.12.2) *)
Theorem complementary_set_cap: forall A, A \cap A^c = EmptySet.
Proof.
move=> A.
apply eq_axiom => x.
split => //.
rewrite complementary_set.
by case.
Qed.

(* (2.13) *)
Theorem complementary_set_twice: forall A, A^c^c = A.
Proof.
move=> A.
apply eq_axiom => x.
rewrite 2!complementary_set_in.
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
apply eq_axiom => x1.
split => //.
case => x2.
by case.
Qed.

(* (2.15) *)
Theorem complementary_set_subset: forall A B, A \subset B <-> B^c \subset A^c.
Proof.
move=> A B.
split.
- move=> HA_subset_B x.
  rewrite 2!complementary_set_in => HB HA.
  by apply /HB /HA_subset_B.
- move=> HB_subset_A.
  rewrite -[A]complementary_set_twice -[B]complementary_set_twice => x.
  rewrite 2!(complementary_set_in (_^c) _) => HA HB.
  apply HA.
  by apply HB_subset_A.
Qed.


(* (2.16) *)
Theorem de_morgan_cup: forall A B, (A \cup B)^c = A^c \cap B^c.
Proof.
move=> A B.
apply eq_axiom => x1.
split.
- rewrite complementary_set_in => HA_cup_B.
  split.
  + rewrite complementary_set_in => HA.
    apply HA_cup_B.
    by left.
  + rewrite complementary_set_in => HB.
    apply HA_cup_B.
    by right.
- case => x2.
  rewrite 3!complementary_set_in => HA HB HAB.
  move: HAB HA HB.
  by case => x3 //.
Qed.

(* (2.16)' *)
Theorem de_morgan_cap: forall A B, (A \cap B)^c = A^c \cup B^c.
Proof.
move=> A B.
apply eq_axiom => x1.
split.
- rewrite complementary_set_in => HA_cap_B.
  rewrite -cup_or 2!complementary_set_in.
  apply not_and_or => HA_and_B.
  apply HA_cap_B.
  by case HA_and_B.
- rewrite complementary_set_in.
  case => x2.
  + rewrite complementary_set_in => HA HA_cap_B.
    apply HA.
    by case HA_cap_B.
  + rewrite complementary_set_in => HB HA_cap_B.
    apply HB.
    by case HA_cap_B.
Qed.

End Section1.


Section Section2.

Variable T: Type.

Definition FamilyEnsemble := (Ensemble (Ensemble T)).

Notation "a \in A" := (In _ a A) (at level 55).
Notation "\emptyset" := (EmptySet _).
Notation "A \subset B" := (Subset _ A B) (at level 55).
Notation "A \cup B" := (Cup _ A B) (at level 50).
Notation "A \cap B" := (Cap _ A B) (at level 50).
Notation "A - B" := (Sub _ A B). (* at level 50 *)
Notation "A ^ 'c'" := (ComplementarySet _ A) (at level 30).

(* ドイツ文字の変数は、AA, BBのように2文字つなげて区別する *)

Inductive CUP (AA: FamilyEnsemble): Ensemble T :=
  | CUP_intro: forall x: T, (exists A: Ensemble T, A \in AA -> x \in A) -> x \in CUP AA.
Notation "\CUP AA" := (CUP AA) (at level 50).

Inductive CAP (AA: FamilyEnsemble): Ensemble T :=
  | CAP_intro: forall x: T, (forall A: Ensemble T, A \in AA -> x \in A) -> x \in CAP AA.
Notation "\CAP AA" := (CAP AA) (at level 50).


(* (2.17) *)
Theorem CUP_in: forall AA A, A \in AA -> A \subset \CUP AA.
Proof.
move=> AA A HA_in_AA.
split.
by exists A.
Qed.

(* (2.18) *)
(* /\になってる部分は->だと思うんだけれど、->だと証明できなかった・・・そのうち考える *)
Theorem CUP_subset: forall AA C, (forall A, A \in AA /\ A \subset C) -> \CUP AA \subset C.
Proof.
move=> AA C HA_subset_C x1.
case => x2.
case => A Hx_in_A.
move: (HA_subset_C A).
case => HA_in_AA.
apply.
by apply Hx_in_A.
Qed.

(* (2.17)' *)
Theorem CAP_in: forall AA A, A \in AA -> \CAP AA \subset A.
Proof.
move=> AA A HA_in_AA x1.
case => x2.
by apply.
Qed.

(* (2.18)' *)
Theorem CAP_subset: forall AA C, (forall A, A \in AA -> C \subset A) -> C \subset \CAP AA.
Proof.
move=> AA C HC_subset_A x1 Hx_in_C.
split => A HA_in_AA.
apply HC_subset_A => //.
Qed.


(* S2 問題1についてはやろうかどうか迷ったけど、一旦置いとく *)

Lemma empty_set_not_in: forall A, A = \emptyset <-> forall x: T, ~ x \in A.
Proof.
move=> A.
split.
- move=> HA x.
  by rewrite HA.
- move=> Hnx.
  apply eq_axiom => x.
  split => //.
  by move: (Hnx x).
Qed.

(* S2 問題2 *)
(* 本ではAとBの入れ替わったバージョンもあるが、そちらは簡単に導けるので今回はこちらだけ証明する *)
Theorem cap_eq_empty_set: forall A B: Ensemble T, A \cap B = \emptyset <-> A \subset B^c.
Proof.
move=> A B.
split.
- move=> HA_cap_B x.
  apply or_to_imply.
  rewrite -complementary_set_in.
  rewrite cup_or.
  rewrite -de_morgan_cap.
  rewrite HA_cap_B.
  by rewrite complementary_set_empty_set.
- move=> HA_subset_Bc.
  rewrite empty_set_not_in => x.
  case => x' HA.
  suff: ~ x' \in B. by [].
  rewrite -complementary_set_in.
  by apply HA_subset_Bc.
Qed.

(* S2 問題3a 本ではA=B=C=Dと4つの式を等号でつないでいるが、今回はA=D, A=B, A=Cの3つの定理として順番に証明していく *)

(* S2 問題3a-1 (A=D) *)
Theorem sub_cap_complementary_set: forall A B: Ensemble T, A - B = A \cap B^c.
Proof.
move=> A B.
apply eq_axiom => x.
split.
- split;
  by case H.
- case => x' HA HB.
  split => //.
  by rewrite -complementary_set_in.
Qed.

(* S2 問題3a-2 (A=B) *)
Theorem sub_cup_sub: forall A B: Ensemble T, A - B = (A \cup B) - B.
Proof.
move=> A B.
rewrite 2!sub_cap_complementary_set.
rewrite cup_cap_distrib.
rewrite complementary_set_cap.
by rewrite cup_comm empty_set_cup.
Qed.

(* S2 問題3a-3 (A=C) *)
Theorem sub_cap_sub: forall A B: Ensemble T, A - B = A - (A \cap B).
Proof.
move=> A B.
rewrite 2!sub_cap_complementary_set.
rewrite de_morgan_cap.
rewrite [A \cap (_ \cup _)]cap_comm cup_cap_distrib.
rewrite [A^c \cap A]cap_comm complementary_set_cap empty_set_cup.
by rewrite cap_comm.
Qed.

(* S2 問題3b *)
Theorem sub_cap_empty: forall A B: Ensemble T, A - B = A <-> A \cap B = \emptyset.
Proof.
move=> A B.
split.
- move=> HA; rewrite -HA.
  apply cap_eq_empty_set.
  rewrite sub_cap_complementary_set.
  by apply cap_subset_r.
- move=> HA_cap_B.
  rewrite sub_cap_sub HA_cap_B.
  by apply sub_empty_set.
Qed.

(* S2 問題3c *)
Theorem sub_eq_empty_set: forall A B: Ensemble T, A - B = \emptyset <-> A \subset B.
Proof.
move=> A B.
rewrite sub_cap_complementary_set.
rewrite cap_eq_empty_set.
by rewrite complementary_set_twice.
Qed.

(* S2 問題4a *)
Theorem sub_cup: forall A B C: Ensemble T, A - (B \cup C) = (A - B) \cap (A - C).
Proof.
move=> A B C.
rewrite sub_cap_complementary_set.
rewrite de_morgan_cup.
rewrite -{1}[A]cap_diag.
rewrite cap_assoc.
rewrite [A \cap (B^c \cap C^c)]cap_comm.
rewrite cap_assoc.
rewrite -[A \cap _]cap_assoc.
rewrite [C^c \cap A]cap_comm.
by rewrite -2!sub_cap_complementary_set.
Qed.

(* S2 問題4b *)
Theorem sub_cap: forall A B C: Ensemble T, A - (B \cap C) = (A - B) \cup (A - C).
Proof.
move=> A B C.
rewrite sub_cap_complementary_set.
rewrite de_morgan_cap.
rewrite cap_comm.
rewrite cup_cap_distrib.
rewrite 2![_ \cap A]cap_comm.
by rewrite -2!sub_cap_complementary_set.
Qed.

(* S2 問題4c *)
Theorem cup_sub: forall A B C: Ensemble T, (A \cup B) - C = (A - C) \cup (B - C).
Proof.
move=> A B C.
rewrite sub_cap_complementary_set.
rewrite cup_cap_distrib.
by rewrite -2!sub_cap_complementary_set.
Qed.

(* S2 問題4d *)
Theorem cap_sub: forall A B C: Ensemble T, (A \cap B) - C = (A - C) \cap (B - C).
Proof.
move=> A B C.
rewrite sub_cap_complementary_set.
rewrite -[C^c]cap_diag.
rewrite -cap_assoc.
rewrite [(A \cap B) \cap C^c]cap_comm.
rewrite -cap_assoc.
rewrite cap_assoc.
rewrite [C^c \cap A]cap_comm.
by rewrite -2!sub_cap_complementary_set.
Qed.

(* S2 問題4e *)
Theorem cap_sub': forall A B C: Ensemble T, A \cap (B - C) = (A \cap B) - (A \cap C).
Proof.
move=> A B C.
rewrite [(A \cap B) - (A \cap C)]sub_cap_complementary_set.
rewrite de_morgan_cap.
rewrite [(A \cap B) \cap _]cap_comm.
rewrite cup_cap_distrib.
rewrite -cap_assoc.
rewrite [A^c \cap A]cap_comm.
rewrite complementary_set_cap.
rewrite empty_set_cap empty_set_cup.
rewrite [C^c \cap _]cap_comm.
rewrite cap_assoc.
by rewrite -sub_cap_complementary_set.
Qed.

(* S2 問題5a *)
Theorem sub_sub_eq_sub_cup: forall A B C: Ensemble T, (A - B) - C = A - (B \cup C).
Proof.
move=> A B C.
apply eq_axiom => x.
rewrite sub_cap_complementary_set -cap_and.
rewrite sub_cap_complementary_set -cap_and.
rewrite and_assoc.
rewrite 2!cap_and.
rewrite -de_morgan_cup.
by rewrite -sub_cap_complementary_set.
Qed.

(* S2 問題5b *)
Theorem sub_sub_eq_cup: forall A B C: Ensemble T, A - (B - C) = (A - B) \cup (A \cap C).
Proof.
move=> A B C.
rewrite [B-C]sub_cap_complementary_set.
rewrite sub_cap.
rewrite [A - C^c]sub_cap_complementary_set.
by rewrite complementary_set_twice.
Qed.

(* S2 問題6 *)
Theorem cup_cap_eq_cup_cap: forall A C: Ensemble T, A \subset C -> forall B, A \cup (B \cap C) = (A \cup B) \cap C.
Proof.
move => A C HA_subset_C B.
apply eq_subset'.
- rewrite cup_comm cap_cup_distrib.
  rewrite cup_comm.
  rewrite 2![(A \cup B) \cap _]cap_comm.
  apply subset_caps_subset.
  rewrite -{2}[C]cup_diag cup_comm.
  by apply subset_cups_subset.
- rewrite cup_cap_distrib.
  apply subset_cups_subset.
  apply cap_subset_l.
Qed.

Definition SymmetricDifference (A B: Ensemble T) := (A \cap B^c) \cup (A^c \cap B).
Notation "A \triangle B" := (SymmetricDifference A B) (at level 50).

(* もう一つの等式 *)
Lemma symmetric_difference_sub_cup: forall A B, A \triangle B = (A - B) \cup (B - A).
Proof.
move=> A B.
rewrite /SymmetricDifference.
rewrite 2!sub_cap_complementary_set.
by rewrite [B \cap A^c]cap_comm.
Qed.

(* S2 問題7a *)
Theorem symmetric_difference_comm: forall A B, A \triangle B = B \triangle A.
Proof.
move=> A B.
rewrite /SymmetricDifference.
rewrite [B \cap A^c]cap_comm [B^c \cap A]cap_comm.
by rewrite cup_comm.
Qed.

(* S2 問題7b *)
Theorem symmetric_difference_sub: forall A B, A \triangle B = (A \cup B) - (A \cap B).
Proof.
move=> A B.
rewrite /SymmetricDifference.
rewrite cap_cup_distrib.
rewrite cup_comm cap_cup_distrib.
rewrite cup_comm complementary_set_cup full_set_cap.
rewrite cup_comm.
rewrite [B^c \cup _]cup_comm cap_cup_distrib.
rewrite complementary_set_cup [_ \cap FullSet _]cap_comm full_set_cap.
rewrite -de_morgan_cap.
by rewrite -sub_cap_complementary_set.
Qed.

(* S2 問題7c *)
Theorem symmetric_difference_assoc: forall A B C,
  (A \triangle B) \triangle C = A \triangle (B \triangle C).
Proof.
move=> A B C.


























