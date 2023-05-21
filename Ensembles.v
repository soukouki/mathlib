(* 集合・位相入門(松坂)1 をCoqで証明しつつ読んでいく *)

Add LoadPath "." as Local.

From mathcomp Require Import ssreflect.
Require Import Coq.Logic.Description.
Require Import Local.Classical.
Require Import Coq.Logic.FunctionalExtensionality.

Module Ensembles.
Declare Scope ensemble_scope.
Open Scope ensemble_scope.

Section Section1.

Variable T: Type.
Implicit Type x: T.

Definition Ensemble := T -> Prop.
Implicit Types A B C: Ensemble.

Definition In (a: T) (A: Ensemble): Prop := A a.
Notation "a \in A" := (In a A) (at level 55).

Notation "a \notin A" := (~ In a A) (at level 55).

Inductive EmptySet: Ensemble := .
Notation "\emptyset" := EmptySet.

(* 外延性の公理 *)
Axiom eq_axiom: forall (A B: Ensemble),
  (forall (x: T), (x \in A <-> x \in B)) -> A = B.

Lemma eq_iff A B:
  (forall (x: T), (x \in A <-> x \in B)) <-> A = B.
Proof.
split.
- by apply eq_axiom.
- move=> HAB x.
  by rewrite HAB.
Qed.

Definition Subset A B: Prop := forall x, x \in A -> x \in B.
Notation "A \subset B" := (Subset A B) (at level 55).

(* (1.3) *)
Theorem eq_subset A B: A = B <-> A \subset B /\ B \subset A.
Proof.
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

Lemma eq_subset' A B: A \subset B -> B \subset A -> A = B.
Proof.
move=> HAB HBA.
apply eq_subset => //.
Qed.

(* (1.4)
   本にあるのは A \subset B /\ B \subset C だけれど、明らかに同等な上にこちらのほうがCoq的に扱いやすいのでこう書いた
   今後も同じような例が出てくるが、同様に行う *)
Theorem subset_trans A B C: A \subset B -> B \subset C -> A \subset C.
Proof.
move=> HA_subset_B HB_subset_C.
rewrite /Subset => x Hx_in_A.
by apply /HB_subset_C /HA_subset_B.
Qed.

(* (1.5) *)
Theorem emptyset_subset A: \emptyset \subset A.
Proof. by []. Qed.


Inductive Cup A B: Ensemble :=
  | Cup_introl: forall x: T, x \in A -> x \in Cup A B
  | Cup_intror: forall x: T, x \in B -> x \in Cup A B.
Notation "A \cup B" := (Cup A B) (at level 50).

(* (2.2.1) *)
Theorem subset_cup_l A B: A \subset A \cup B.
Proof. by left. Qed.

(* (2.2.2) *)
Theorem subset_cup_r A B: B \subset A \cup B.
Proof. by right. Qed.

Lemma cup_or A B x: x \in A \/ x \in B <-> x \in A \cup B.
Proof.
split.
- case => H.
  + by left.
  + by right.
- case => x' H.
  + by left.
  + by right.
Qed.

(* 2.3 *)
Theorem subsets_cup A B C: A \subset C -> B \subset C -> A \cup B \subset C.
Proof.
move=> HA_subset_C HB_subset_C.
rewrite /Subset => x1.
case => x2.
- by apply /HA_subset_C.
- by apply /HB_subset_C.
Qed.

(* (2.4) *)
Theorem cup_diag A: A \cup A = A.
Proof.
apply eq_subset'.
- by apply subsets_cup => //.
- by apply subset_cup_l.
Qed.

(* (2.5) *)
Theorem cup_comm A B: A \cup B = B \cup A.
Proof.
apply eq_subset' => x;
  rewrite -2!cup_or;
  by rewrite or_comm.
Qed.

(* (2.6) *)
Theorem cup_assoc A B C: (A \cup B) \cup C = A \cup (B \cup C).
Proof.
apply eq_subset' => x;
  rewrite -4!cup_or;
  by rewrite or_assoc.
Qed.

(* (2.7) *)
Theorem subset_cup_eq A B: A \subset B <-> A \cup B = B.
Proof.
split.
- move=> HA_subset_B.
  apply eq_subset'.
  + by apply subsets_cup => //.
  + by apply subset_cup_r.
- move=> H; rewrite -H.
  by apply subset_cup_l.
Qed.

(* (2.8) *)
Theorem subset_cups_subset A B C: A \subset B -> A \cup C \subset B \cup C.
Proof.
move=> HA_subset_B.
apply subsets_cup.
- left.
  by apply HA_subset_B.
- by apply subset_cup_r.
Qed.

(* (2.9) *)
Theorem emptyset_cup A: \emptyset \cup A = A.
Proof. by apply subset_cup_eq. Qed.


Inductive Cap A B: Ensemble :=
  Cap_intro: forall x: T, x \in A -> x \in B -> x \in (Cap A B).
Notation "A \cap B" := (Cap A B) (at level 50).

(* (2.2.1)'
   本ではsupsetを使っているが、今回はすべてsubsetで統一する *)
Theorem cap_subset_l A B: A \cap B \subset A.
Proof.
move=> x.
by case.
Qed.

(* (2.2.2)' *)
Theorem cap_subset_r A B: A \cap B \subset B.
Proof.
move=> x.
by case.
Qed.

Lemma cap_and A B x: x \in A /\ x \in B <-> x \in A \cap B.
Proof.
split;
  by case.
Qed.

(* (2.3)' *)
Theorem subsets_cap A B C: C \subset A -> C \subset B -> C \subset A \cap B.
Proof.
move=> HC_subset_A HC_subset_B x.
split.
- by apply HC_subset_A.
- by apply HC_subset_B.
Qed.

(* (2.4)' *)
Theorem cap_diag A: A \cap A = A.
Proof.
apply eq_subset' => x;
  rewrite -cap_and.
- by case.
- by split.
Qed.

(* (2.5)' *)
Theorem cap_comm A B: A \cap B = B \cap A.
Proof.
apply eq_subset' => x;
  rewrite -2!cap_and.
- by rewrite and_comm.
- by case.
Qed.

(* (2.6)' *)
Theorem cap_assoc A B C: (A \cap B) \cap C = A \cap (B \cap C).
Proof.
apply eq_subset' => x;
  rewrite -4!cap_and;
  by rewrite and_assoc.
Qed.

(* (2.7)' *)
Theorem subset_cap_eq A B: A \subset B <-> A \cap B = A.
Proof.
split.
- move=> HA_subset_B.
  apply eq_subset'.
  + by apply cap_subset_l.
  + by apply subsets_cap => //.
- move=> H; rewrite -H.
  by apply cap_subset_r.
Qed.

(* (2.8)' *)
Theorem subset_caps_subset A B C: A \subset B -> A \cap C \subset B \cap C.
Proof.
move=> HA_subset_B.
apply subsets_cap => x1.
- case => x2 HA HC.
  by apply HA_subset_B.
- by apply cap_subset_r.
Qed.

(* (2.9)' *)
Theorem emptyset_cap A: \emptyset \cap A = \emptyset.
Proof. by apply subset_cap_eq. Qed.

(* (2.10) *)
Theorem cup_cap_distrib A B C: (A \cup B) \cap C = (A \cap C) \cup (B \cap C).
Proof.
apply eq_axiom => x1.
split.
- case => x2.
  by case => x3 H HC;
    [left | right];
    split => //.
- case => x2;
    case => x3;
    [move=> HA | move=> HB];
    split => //;
    by [left | right].
Qed.

(* (2.11) *)
Theorem cap_cup_distrib A B C: (A \cap B) \cup C = (A \cup C) \cap (B \cup C).
Proof.
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
Theorem cup_absorption A B: (A \cup B) \cap A = A.
Proof.
rewrite cap_comm.
apply subset_cap_eq.
by apply subset_cup_l.
Qed.

(* (2.11)' *)
Theorem cap_absorption A B: (A \cap B) \cup A = A.
Proof.
apply subset_cup_eq.
by apply cap_subset_l.
Qed.


Inductive Sub A B: Ensemble :=
  | Sub_intro: forall x: T, x \in A -> x \notin B -> x \in Sub A B.
Notation "A - B" := (Sub A B). (* at level 50 *)

Lemma sub_iff A B x: x \in A - B <-> x \in A /\ x \notin B.
Proof.
split.
- case => x1.
  by split.
- case.
  by apply Sub_intro.
Qed.

Lemma sub_emptyset A: A - \emptyset = A.
Proof.
apply eq_axiom => x.
split.
- by case.
- by split.
Qed.

Lemma emptyset_sub A: \emptyset - A = \emptyset.
Proof.
apply eq_axiom => x.
split => //.
by case.
Qed.

Lemma sub_sim_emptyset A: A - A = \emptyset.
Proof.
apply eq_axiom => x.
split => //.
rewrite sub_iff.
by case.
Qed.


Inductive FullSet: Ensemble :=
  | FullSet_intro: forall x, x \in FullSet.

Lemma fullset_cap A: FullSet \cap A = A.
Proof. by rewrite cap_comm -subset_cap_eq. Qed.

Lemma fullset_cup A: FullSet \cup A = FullSet.
Proof. by rewrite cup_comm -subset_cup_eq. Qed.

Lemma eq_fullset A: (forall x, x \in A) <-> A = FullSet.
Proof.
split.
- move=> H.
  apply eq_subset.
  by split.
- move=> H x.
  by rewrite H.
Qed.

Inductive ComplementarySet (A: Ensemble): Ensemble :=
  | ComplementarySet_intro: forall x, x \in FullSet - A -> x \in ComplementarySet A.
Notation "A ^ 'c'" := (ComplementarySet A) (at level 30).

Lemma __compset A: A^c = fun x => x \notin A.
Proof.
apply eq_subset'.
- move=> x1 HA.
  case HA => x2.
  by case.
- split.
  by split.
Qed.

Lemma compset_in A x: x \in A^c <-> x \notin A.
Proof. by rewrite __compset. Qed.

(* (2.12.1) *)
Theorem compset_cup A: A \cup A^c = FullSet.
Proof.
apply eq_axiom => x.
split => // _.
rewrite -cup_or.
rewrite compset_in.
by apply classic. (* ここで古典論理を使い始めた *)
Qed.

(* (2.12.2) *)
Theorem compset_cap A: A \cap A^c = EmptySet.
Proof.
apply eq_axiom => x1.
split => //.
case => x2.
by rewrite compset_in.
Qed.

(* (2.13) *)
Theorem compset_twice A: A^c^c = A.
Proof.
apply eq_axiom => x.
rewrite 2!compset_in.
split.
- by apply NNPP.
- by move=> H.
Qed.

(* (2.14.1) *)
Theorem compset_emptyset: EmptySet^c = FullSet.
Proof.
apply eq_axiom => x.
split => // _.
by rewrite compset_in.
Qed.

(* (2.14.2) *)
Theorem compset_fullset: FullSet^c = EmptySet.
Proof.
apply eq_axiom => x1.
split => //.
case => x2.
by case.
Qed.

(* (2.15) *)
Theorem compset_subset A B: A \subset B <-> B^c \subset A^c.
Proof.
split.
- move=> HA_subset_B x.
  rewrite 2!compset_in => HB HA.
  by apply /HB /HA_subset_B.
- move=> HB_subset_A.
  rewrite -[A]compset_twice -[B]compset_twice => x.
  rewrite 2!(compset_in (_^c) _) => HA HB.
  apply HA.
  by apply HB_subset_A.
Qed.


(* (2.16) *)
Theorem de_morgan_cup A B: (A \cup B)^c = A^c \cap B^c.
Proof.
apply eq_axiom => x1.
split.
- rewrite compset_in => HA_cup_B.
  split.
  + rewrite compset_in => HA.
    apply HA_cup_B.
    by left.
  + rewrite compset_in => HB.
    apply HA_cup_B.
    by right.
- case => x2.
  rewrite 3!compset_in => HA HB HAB.
  move: HAB HA HB.
  by case => x3 //.
Qed.

(* (2.16)' *)
Theorem de_morgan_cap A B: (A \cap B)^c = A^c \cup B^c.
Proof.
apply eq_axiom => x1.
split.
- rewrite compset_in => HA_cap_B.
  rewrite -cup_or 2!compset_in.
  apply not_and_or => HA_and_B.
  apply HA_cap_B.
  by case HA_and_B.
- rewrite compset_in.
  case => x2.
  + rewrite compset_in => HA HA_cap_B.
    apply HA.
    by case HA_cap_B.
  + rewrite compset_in => HB HA_cap_B.
    apply HB.
    by case HA_cap_B.
Qed.

Lemma sub_fullset A: A - FullSet = \emptyset.
Proof.
apply eq_axiom => x.
rewrite sub_iff.
rewrite -compset_in compset_fullset.
rewrite cap_and.
by rewrite cap_comm emptyset_cap.
Qed.

Lemma fullset_sub A: FullSet - A = A^c.
Proof.
apply eq_axiom => x.
rewrite sub_iff.
rewrite -compset_in.
rewrite cap_and.
by rewrite fullset_cap.
Qed.

Lemma sub_compset A: A - A^c = A.
Proof.
apply eq_axiom => x.
rewrite sub_iff.
rewrite -compset_in.
rewrite compset_twice.
by split => //; case.
Qed.

End Section1.


Arguments In {_} _ _.
Arguments EmptySet {_}.
Arguments FullSet {_}.
Arguments Subset {_} _ _.
Arguments Cup {_} _ _.
Arguments Cap {_} _ _.
Arguments Sub {_} _ _.
Arguments ComplementarySet {_} _.

Notation "a \in A" := (In a A) (at level 55): ensemble_scope.
Notation "a \notin A" := (~ In a A) (at level 55): ensemble_scope.
Notation "\emptyset" := (EmptySet): ensemble_scope.
Notation "A \subset B" := (Subset A B) (at level 55): ensemble_scope.
Notation "A \cup B" := (Cup A B) (at level 50): ensemble_scope.
Notation "A \cap B" := (Cap A B) (at level 50): ensemble_scope.
Notation "A - B" := (Sub A B) (* at level 50 *): ensemble_scope.
Notation "A ^ 'c'" := (ComplementarySet A) (at level 30): ensemble_scope.


Section Section2.

Variable T: Type.
Implicit Type x: T.
Implicit Type A B C: Ensemble T.

Definition FamilyEnsemble := (Ensemble (Ensemble T)).
Implicit Types AA BB: FamilyEnsemble.

(* ドイツ文字の変数は、AA, BBのように2文字つなげて区別する *)

Inductive BigCup AA: Ensemble T :=
  | big_cup_intro: forall x: T, (exists A: Ensemble T, A \in AA -> x \in A) -> x \in BigCup AA.
Notation "\bigcup AA" := (BigCup AA) (at level 50).

Inductive BigCap AA: Ensemble T :=
  | big_cap_intro: forall x: T, (forall A: Ensemble T, A \in AA -> x \in A) -> x \in BigCap AA.
Notation "\bigcap AA" := (BigCap AA) (at level 50).

(* (2.17) *)
Theorem big_cup_in AA A: A \in AA -> A \subset \bigcup AA.
Proof.
move=> HA_in_AA.
split.
by exists A.
Qed.

(* (2.18) *)
(* /\になってる部分は->だと思うんだけれど、->だと証明できなかった・・・ *)
(* ->の場合、A \in AA までたどり着くけどそれ自体の証明ができない *)
Theorem big_cup_subset AA C: (forall A, A \in AA /\ A \subset C) -> \bigcup AA \subset C.
Proof.
move=> HA_subset_C x1.
case => x2.
case => A Hx_in_A.
move: (HA_subset_C A).
case => HA_in_AA.
apply.
by apply Hx_in_A.
Qed.

(* (2.17)' *)
Theorem big_cap_in AA A: A \in AA -> \bigcap AA \subset A.
Proof.
move=> HA_in_AA x1.
case => x2.
by apply.
Qed.

(* (2.18)' *)
Theorem big_cap_subset AA C: (forall A, A \in AA -> C \subset A) -> C \subset \bigcap AA.
Proof.
move=> HC_subset_A x1 Hx_in_C.
split => A HA_in_AA.
apply HC_subset_A => //.
Qed.


(* S2 問題1についてはやろうかどうか迷ったけど、一旦置いとく *)

Lemma emptyset_not_in A: A = \emptyset <-> forall x: T, x \notin A.
Proof.
split.
- move=> HA x.
  by rewrite HA.
- move=> Hnx.
  apply eq_axiom => x.
  split => //.
  by move: (Hnx x).
Qed.

(* S2 問題2 *)
(* 本ではAとBの入れ替わったバージョンもあるが、そちらはこちらが成り立つことから自明に求められるため、省略する *)
Theorem cap_eq_emptyset A B: A \cap B = \emptyset <-> A \subset B^c.
Proof.
split.
- move=> HA_cap_B x.
  apply or_to_imply.
  rewrite -compset_in.
  rewrite cup_or.
  rewrite -de_morgan_cap.
  rewrite HA_cap_B.
  by rewrite compset_emptyset.
- move=> HA_subset_Bc.
  rewrite emptyset_not_in => x.
  case => x' HA.
  suff: x' \notin B. by [].
  rewrite -compset_in.
  by apply HA_subset_Bc.
Qed.

(* S2 問題3a 本ではA=B=C=Dと4つの式を等号でつないでいるが、今回はA=D, A=B, A=Cの3つの定理として順番に証明していく *)

(* S2 問題3a-1 (A=D) *)
Theorem sub_cap_compset A B: A - B = A \cap B^c.
Proof.
apply eq_axiom => x.
by rewrite sub_iff -cap_and -compset_in.
Qed.

(* S2 問題3a-2 (A=B) *)
Theorem sub_cup_sub A B: A - B = (A \cup B) - B.
Proof.
apply eq_axiom => x.
rewrite 2!sub_cap_compset.
rewrite cup_cap_distrib.
rewrite compset_cap.
by rewrite cup_comm emptyset_cup.
Qed.

(* S2 問題3a-3 (A=C) *)
Theorem sub_cap_sub A B: A - B = A - (A \cap B).
Proof.
rewrite 2!sub_cap_compset.
rewrite de_morgan_cap.
rewrite [A \cap (_ \cup _)]cap_comm cup_cap_distrib.
rewrite [A^c \cap A]cap_comm compset_cap emptyset_cup.
by rewrite cap_comm.
Qed.

(* S2 問題3b *)
Theorem sub_cap_empty A B: A - B = A <-> A \cap B = \emptyset.
Proof.
split.
- move=> HA; rewrite -HA.
  apply cap_eq_emptyset.
  rewrite sub_cap_compset.
  by apply cap_subset_r.
- move=> HA_cap_B.
  rewrite sub_cap_sub HA_cap_B.
  by apply sub_emptyset.
Qed.

(* S2 問題3c *)
Theorem sub_eq_emptyset A B: A - B = \emptyset <-> A \subset B.
Proof.
rewrite sub_cap_compset.
rewrite cap_eq_emptyset.
by rewrite compset_twice.
Qed.

(* S2 問題4a *)
Theorem sub_cup A B C: A - (B \cup C) = (A - B) \cap (A - C).
Proof.
rewrite sub_cap_compset.
rewrite de_morgan_cup.
rewrite -{1}[A]cap_diag.
rewrite cap_assoc.
rewrite [A \cap (B^c \cap C^c)]cap_comm.
rewrite cap_assoc.
rewrite -[A \cap _]cap_assoc.
rewrite [C^c \cap A]cap_comm.
by rewrite -2!sub_cap_compset.
Qed.

(* S2 問題4b *)
Theorem sub_cap A B C: A - (B \cap C) = (A - B) \cup (A - C).
Proof.
rewrite sub_cap_compset.
rewrite de_morgan_cap.
rewrite cap_comm.
rewrite cup_cap_distrib.
rewrite 2![_ \cap A]cap_comm.
by rewrite -2!sub_cap_compset.
Qed.

(* S2 問題4c *)
Theorem cup_sub A B C: (A \cup B) - C = (A - C) \cup (B - C).
Proof.
rewrite sub_cap_compset.
rewrite cup_cap_distrib.
by rewrite -2!sub_cap_compset.
Qed.

(* S2 問題4d *)
Theorem cap_sub A B C: (A \cap B) - C = (A - C) \cap (B - C).
Proof.
rewrite sub_cap_compset.
rewrite -[C^c]cap_diag.
rewrite -cap_assoc.
rewrite [(A \cap B) \cap C^c]cap_comm.
rewrite -cap_assoc.
rewrite cap_assoc.
rewrite [C^c \cap A]cap_comm.
by rewrite -2!sub_cap_compset.
Qed.

(* S2 問題4e *)
Theorem cap_sub' A B C: A \cap (B - C) = (A \cap B) - (A \cap C).
Proof.
rewrite [(A \cap B) - (A \cap C)]sub_cap_compset.
rewrite de_morgan_cap.
rewrite [(A \cap B) \cap _]cap_comm.
rewrite cup_cap_distrib.
rewrite -cap_assoc.
rewrite [A^c \cap A]cap_comm.
rewrite compset_cap.
rewrite emptyset_cap emptyset_cup.
rewrite [C^c \cap _]cap_comm.
rewrite cap_assoc.
by rewrite -sub_cap_compset.
Qed.

(* S2 問題5a *)
Theorem sub_sub_eq_sub_cup A B C: (A - B) - C = A - (B \cup C).
Proof.
apply eq_axiom => x.
rewrite sub_cap_compset -cap_and.
rewrite sub_cap_compset -cap_and.
rewrite and_assoc.
rewrite 2!cap_and.
rewrite -de_morgan_cup.
by rewrite -sub_cap_compset.
Qed.

(* S2 問題5b *)
Theorem sub_sub_eq_cup A B C: A - (B - C) = (A - B) \cup (A \cap C).
Proof.
rewrite [B-C]sub_cap_compset.
rewrite sub_cap.
rewrite [A - C^c]sub_cap_compset.
by rewrite compset_twice.
Qed.

(* S2 問題6 *)
Theorem cup_cap_eq_cup_cap A C: A \subset C -> forall B, A \cup (B \cap C) = (A \cup B) \cap C.
Proof.
move=> HA_subset_C B.
rewrite cup_comm.
rewrite cap_cup_distrib.
rewrite [B \cup A]cup_comm [C \cup A]cup_comm.
have: A \cup C = C.
  by rewrite -subset_cup_eq.
move=> H.
by rewrite H.
Qed.

Definition SymmetricDifference A B := (A - B) \cup (B - A).
Notation "A \triangle B" := (SymmetricDifference A B) (at level 50).

(* もう一つの等式 *)
Lemma sym_diff_compset A B: A \triangle B = (A \cap B^c) \cup (A^c \cap B).
Proof.
rewrite /SymmetricDifference.
rewrite 2!sub_cap_compset.
by rewrite [B \cap A^c]cap_comm.
Qed.

(* S2 問題7a *)
Theorem sym_diff_comm A B: A \triangle B = B \triangle A.
Proof.
rewrite 2!sym_diff_compset.
rewrite [B \cap A^c]cap_comm [B^c \cap A]cap_comm.
by rewrite cup_comm.
Qed.

(* S2 問題7b *)
Theorem sym_diff_sub A B: A \triangle B = (A \cup B) - (A \cap B).
Proof.
rewrite /SymmetricDifference.
rewrite cup_sub.
rewrite 2!sub_cap.
rewrite 2!sub_sim_emptyset.
by rewrite [_ \cup \emptyset]cup_comm 2!emptyset_cup.
Qed.

Lemma sub_comm A B C: (A - B) - C = (A - C) - B.
Proof.
apply eq_axiom => x.
by rewrite !sub_iff !and_assoc [_ \notin _ /\ _ \notin _]and_comm.
Qed.

(* きれいな解法を思いつかなかった *)
Lemma sub_merge A B C: (A - C) - (B - C) = A - B - C.
Proof.
rewrite !sub_cap_compset.
rewrite de_morgan_cap.
rewrite compset_twice.
rewrite 2!cap_assoc.
rewrite [C^c \cap _]cap_comm.
rewrite cup_cap_distrib.
rewrite compset_cap.
rewrite [_ \cup \emptyset]cup_comm emptyset_cup.
by rewrite [B^c \cap C^c]cap_comm.
Qed.

Lemma sub_sub_cap A B C: A - (B - C) \cap B = A \cap B \cap C.
Proof.
rewrite !sub_cap_compset.
rewrite de_morgan_cap.
rewrite compset_twice.
rewrite cap_assoc.
rewrite cup_cap_distrib.
rewrite [B^c \cap B]cap_comm compset_cap.
rewrite emptyset_cup.
by rewrite [C \cap B]cap_comm cap_assoc.
Qed.

Lemma sym_diff_assoc_help A B C:
  (A - ((B - C) \cup (C - B))) = ((A - B) - C) \cup (A \cap B \cap C).
Proof.
rewrite -sub_sub_eq_sub_cup.
rewrite sub_sub_eq_cup.
rewrite sub_comm.
rewrite sub_merge.
by rewrite sub_sub_cap.
Qed.

(* S2 問題7c *)
Theorem sym_diff_assoc A B C:
  (A \triangle B) \triangle C = A \triangle (B \triangle C).
Proof.
apply eq_trans_r with
  (y := (A - B - C) \cup (B - C - A) \cup (C - A - B) \cup (A \cap B \cap C)).
- rewrite /SymmetricDifference.
  rewrite cup_sub.
  rewrite [B - A - C]sub_comm.
  rewrite sym_diff_assoc_help.
  rewrite [C \cap A]cap_comm cap_assoc [C \cap B]cap_comm cap_assoc.
  by rewrite !cup_assoc.
- rewrite /SymmetricDifference.
  rewrite cup_sub.
  rewrite [C - B - A]sub_comm.
  rewrite sym_diff_assoc_help.
  rewrite cup_assoc [(_ \cap _) \cup _]cup_comm.
  by rewrite !cup_assoc.
Qed.

(* S2 問題7d *)
Theorem sym_diff_cap_distrib A B C:
  A \cap (B \triangle C) = (A \cap B) \triangle (A \cap C).
Proof.
apply eq_trans_r with
  (y := (A \cap B \cap C^c) \cup (A \cap C \cap B^c)).
- rewrite sym_diff_compset.
  rewrite cap_comm cup_cap_distrib.
  rewrite [B \cap C^c]cap_comm [(C^c \cap B) \cap A]cap_assoc [C^c \cap (B \cap A)]cap_comm [B \cap A]cap_comm.
  rewrite [(B^c \cap C) \cap A]cap_assoc [B^c \cap (C \cap A)]cap_comm [C \cap A]cap_comm.
  by [].
- rewrite sym_diff_compset.
  rewrite 2!de_morgan_cap.
  rewrite [(A \cap B) \cap (A^c \cup C^c)]cap_comm 2!cup_cap_distrib.
  rewrite -2![A^c \cap (A \cap _)]cap_assoc.
  rewrite [A^c \cap A]cap_comm compset_cap 2!emptyset_cap 2!emptyset_cup.
  rewrite 2![_^c \cap _]cap_comm.
  by [].
Qed.

(* S2 問題8a *)
Theorem sym_diff_emptyset_l A: A \triangle EmptySet = A.
Proof.
rewrite /SymmetricDifference.
rewrite sub_emptyset emptyset_sub.
by rewrite cup_comm emptyset_cup.
Qed.

(* S2 問題8b *)
Theorem sym_diff_fullset A: A \triangle FullSet = A^c.
Proof.
rewrite /SymmetricDifference.
rewrite sub_fullset fullset_sub.
by rewrite emptyset_cup.
Qed.

(* S2 問題8c *)
Theorem sym_diff_emptyset_r A: A \triangle A = EmptySet.
Proof.
rewrite /SymmetricDifference.
rewrite sub_sim_emptyset.
by rewrite cup_diag.
Qed.

(* S2 問題8d *)
Theorem sym_diff_compset_fullset A: A \triangle A^c = FullSet.
Proof.
rewrite sym_diff_compset.
rewrite compset_twice.
rewrite 2!cap_diag.
by rewrite compset_cup.
Qed.

Lemma sym_diff_not_in_from_in A B x: x \in A -> x \in B -> x \notin A \triangle B.
Proof.
move=> HA HB H.
move: H HA HB.
case => x';
  rewrite sub_iff;
  by case.
Qed.

Lemma sub_sym_diff A1 A2 B1 B2 x:
  x \in A1 - B1 ->
  A1 \triangle A2 = B1 \triangle B2 ->
  x \in A2 \triangle B2.
Proof.
case => x2 => HA1 HB1 Htriangle.
case: (classic (x2 \in A2)).
- move=> HA2.
  left.
  split => //.
  have: x2 \notin A1 \triangle A2.
    by apply sym_diff_not_in_from_in => //.
  rewrite Htriangle => HBnotin HB2.
  apply /HBnotin.
  rewrite sym_diff_comm.
  left.
  by split.
- move=> HA2.
  right.
  split => //.
  have: x2 \in A1 \triangle A2.
    left.
    by split.
  rewrite Htriangle => H.
  move: HB1.
  case H => x3;
    by case.
Qed.

(* S2 問題9 *)
Theorem sym_diff_shakeup A1 A2 B1 B2: A1 \triangle A2 = B1 \triangle B2 -> A1 \triangle B1 = A2 \triangle B2.
Proof.
move=> Htriangle.
rewrite -eq_iff => x0.
split.
- rewrite {1}/SymmetricDifference.
  case => x1 Hsub.
  + by apply (sub_sym_diff A1 A2 B1 B2).
  + rewrite sym_diff_comm.
    by apply (sub_sym_diff B1 B2 A1 A2).
- have: (A2 \triangle A1 = B2 \triangle B1).
    symmetry.
    by rewrite [B2 \triangle B1]sym_diff_comm [A2 \triangle A1]sym_diff_comm.
  move=> Htriangle'.
  rewrite {1}/SymmetricDifference.
  case => x1 Hsub.
  + by apply (sub_sym_diff A2 A1 B2 B1).
  + rewrite sym_diff_comm.
    by apply (sub_sym_diff B2 B1 A2 A1).
Qed.

End Section2.


Arguments BigCup {_} _ _.
Arguments BigCap {_} _ _.

Notation "\bigcup AA" := (BigCup AA) (at level 50).
Notation "\bigcap AA" := (BigCap AA) (at level 50).


Section Section3.

Implicit Types A B: Type.

(* Corr = Correspondence *)
Definition Corr A B := A -> Ensemble B.
Notation "A ->c B" := (Corr A B) (at level 99).

Definition Graph {A B} (C: A ->c B): Ensemble (A * B) := (fun x: (A * B) => (snd x) \in C (fst x)).

(* (3.1) *)
Theorem corr_from_graph {A B} (C: A ->c B) (a: A):
  C a = ((fun b => (Graph C) (pair a b)): Ensemble B).
Proof. by []. Qed.

(* S3 定理1 *)
Theorem exists_one_graph_from_pair A B (X: Ensemble (A * B)): exists! (G: A ->c B), X = Graph G.
Proof.
exists (fun a b => X (pair a b)).
split.
- rewrite /Graph.
  apply eq_axiom => x.
  by rewrite /In -surjective_pairing.
- move=> C HX.
  by rewrite HX.
Qed.

Definition DefRange   {A B} (C: A ->c B): Ensemble A := fun a: A => exists b: B, (a, b) \in Graph(C).
Definition ValueRange {A B} (C: A ->c B): Ensemble B := fun b: B => exists a: A, (a, b) \in Graph(C).

Definition InvCorr {A B} (C: A->c B): B ->c A := fun (b: B) (a: A) => b \in C a.

Theorem def_range_neq_empty_set A B (C: A ->c B): DefRange C = fun a: A => C a <> \emptyset.
Proof.
apply eq_subset'.
- move=> a.
  rewrite /In /DefRange.
  case => b HinG.
  rewrite emptyset_not_in => H.
  by apply (H b).
- move=> a.
  rewrite /In /DefRange.
  rewrite emptyset_not_in.
  rewrite -exists_iff_not_forall_not.
  case => b Hin.
  by exists b.
Qed.

(* (3.2) *)
Theorem in_inv_corr A B (C: A ->c B) a b: b \in C a <-> a \in (InvCorr C) b.
Proof. by []. Qed.

(* (3.3) *)
Theorem def_range_inv_corr_to_value_range A B (C: A ->c B): DefRange(InvCorr C) = ValueRange C.
Proof. by []. Qed.

(* (3.3)' *)
Theorem value_range_inv_corr_to_def_range A B (C: A ->c B): ValueRange(InvCorr C) = DefRange C.
Proof. by []. Qed.

(* 3.4 *)
Theorem inv_corr_twice A B (C: A ->c B): InvCorr (InvCorr C) = C.
Proof. by []. Qed.

(* p.27 *)
Theorem inv_corr_is_not_empty_iff_in_value_range A B b (C: A ->c B):
  (InvCorr C b <> \emptyset) <-> b \in ValueRange C.
split.
- move=> Hneq.
  apply NNPP => Hnot_in.
  apply Hneq.
  apply eq_subset' => // x Hin_inv.
  apply False_ind.
  apply Hnot_in.
  rewrite /ValueRange.
  exists x.
  by apply Hin_inv.
- move=> Hb Hneq.
  move: Hb.
  case => a Hgraph.
  suff: a \notin (InvCorr C b) => //.
  by rewrite Hneq.
Qed.

(* 
(* Map = Mapping *)
Definition Map (A B: Type) := A -> B.
Notation "A -> B" := (Map A B) (at level 90).

これは関数と等しいので、今回は定義しない。
 *)

Definition MapAsCorr {A B} (f: A -> B): A ->c B := 
  fun a b => b = f a.

Definition Identity {A} (f: A -> A) := identity.

(* 分かりづらいんじゃ！ *)
Set Implicit Arguments.
Definition get_value := proj1_sig.
Definition get_proof := proj2_sig.
Unset Implicit Arguments.

(* S3 定理2 *)
Theorem exist_one_map_equivalent_to_graphs {A B} G:
  (exists f: A -> B, G = Graph (MapAsCorr f)) <-> (forall a, exists! b, (a, b) \in G).
Proof.
split.
- case => f HG a.
  exists (f a).
  rewrite HG.
  by split.
- move=> HinG.
  have: (forall a: A, {b: B | (a, b) \in G}).
    move=> a.
    apply constructive_definite_description.
    by apply HinG.
  move=> Sigb.
  exists (fun a: A => get_value (Sigb a)).
  apply eq_subset'.
  + move=> x Hx.
    rewrite /Graph /MapAsCorr /In.
    (* bからグラフ上の(a, b)は一意に求められることを示す。
       uniqueness = forall x y: A, P x -> P y -> x = y という定義で、_ = _ を処理するのに使える *)
    have: (uniqueness (fun b: B => (fst x, b) \in G)).
      by apply unique_existence.
    apply.
    * by rewrite -surjective_pairing.
    * by apply get_proof.
  + move=> x Hx.
    rewrite /MapAsCorr /Graph /In in Hx.
    rewrite (surjective_pairing x).
    rewrite Hx.
    by apply get_proof.
Qed.

(* S3 問題3 *)
Theorem map_as_corr_inv_corr {A B: Type} (C: A ->c B):
  (exists! f: A -> B, MapAsCorr f = C) <->
  (DefRange C = FullSet /\ (forall b b', b <> b' -> InvCorr C b \cap InvCorr C b' = \emptyset)).
Proof.
split.
- move=> Hf.
  have: {f: A -> B | MapAsCorr f = C}.
    by apply constructive_definite_description.
  clear Hf => Hf.
  split.
  + rewrite -eq_fullset => a.
    case Hf => f Hfeq.
    exists (f a).
    by rewrite -Hfeq.
  + move=> b b' HB.
    rewrite cap_eq_emptyset.
    move: Hf.
    case => f Hf a.
    rewrite -Hf => Heq.
    rewrite compset_in => Heq'.
    move: Heq.
    rewrite /InvCorr /MapAsCorr /In.
    rewrite /InvCorr /MapAsCorr /In in Heq'.
    by rewrite -Heq'.
- case.
  rewrite -eq_fullset => Hdef H.
  Search DefRange.
  rewrite -unique_existence.
  Search InvCorr.
  split.
  + (* 仮定を崩さない限りは進めない感じがしてきた・・・ *)

  (* 定義域が全体かつ、全てのbとb'(b<>b')に対して逆対応がかぶらないなら対応する関数が存在する *)
Admitted.

Lemma def_range_map_as_corr {A B} (f: A -> B) a:
  a \in DefRange (MapAsCorr f) <-> exists b, f a = b.
Proof.
split;
  case => b H;
  by exists b.
Qed.

Lemma value_range_map_as_corr {A B} (f: A -> B) b:
  b \in ValueRange (MapAsCorr f) <-> exists a, f a = b.
Proof.
split;
  case => a H;
  by exists a.
Qed.

End Section3.


Notation "A ->c B" := (Corr A B) (at level 99).


Section Section4.

Implicit Types A B: Type.

(* メモ: Imageが来たら先でexists *)
Definition Image {A B} (f: A -> B) (P: Ensemble A): Ensemble B :=
  fun b: B => exists a, a \in P /\ f a = b.

(* p.30 *)
Theorem image_def_range_eq_value_range {A B} (f: A -> B):
  Image f (FullSet: Ensemble A) = ValueRange (MapAsCorr f).
Proof.
apply eq_subset'.
- move=> b.
  case => a.
  case => _ Heq.
  by exists a.
- move=> b.
  case => a Hb.
  by exists a.
Qed.

(* p.30 *)
Theorem image_emptyset_iff {A B} (f: A -> B) {P}:
  Image f P = \emptyset <-> P = \emptyset.
Proof.
split.
- rewrite emptyset_not_in.
  move=> Himg.
  rewrite emptyset_not_in => a HP.
  apply (Himg (f a)).
  by exists a.
- move=> HP.
  rewrite emptyset_not_in => b.
  case => a.
  case.
  by rewrite HP.
Qed.

Definition InvImage {A B} (f: A -> B) (Q: Ensemble B): Ensemble A :=
  fun a: A => f a \in Q.

(* p.31 *)
Theorem invimage_fullset {A B} (f: A -> B):
  InvImage f (FullSet: Ensemble B) = (FullSet: Ensemble A).
Proof.
by apply eq_subset' => //.
Qed.

(* 4.1 *)
Theorem image_subset {A B} (f: A -> B) (P1 P2: Ensemble A):
  P1 \subset P2 -> Image f P1 \subset Image f P2.
Proof.
move=> Hsub b.
case => a.
case => HP1 Heq.
exists a.
split => //.
by apply Hsub.
Qed.

(* 4.2 *)
Theorem image_cup {A B} (f: A -> B) (P1 P2: Ensemble A):
  Image f (P1 \cup P2) = Image f P1 \cup Image f P2.
Proof.
apply eq_subset'.
- move=> b H.
  case H => a'.
  case.
  case => a HP Heq;
    [left | right];
    exists a;
    by split.
- apply subsets_cup;
  apply /image_subset;
  by [apply subset_cup_l | apply subset_cup_r].
Qed.

(* 4.3 *)
Theorem image_cap {A B} (f: A -> B) (P1 P2: Ensemble A):
  Image f (P1 \cap P2) \subset Image f P1 \cap Image f P2.
Proof.
apply subsets_cap.
- apply image_subset.
  by apply cap_subset_l.
- apply image_subset.
  by apply cap_subset_r.
Qed.

(* 4.4 *)
Theorem image_sub {A B} (f: A -> B) (P: Ensemble A):
  Image f FullSet - Image f P \subset Image f (FullSet - P).
Proof.
move=> b.
rewrite image_def_range_eq_value_range.
case => b'.
rewrite value_range_map_as_corr.
case => a.
move=> Heq Hex.
rewrite fullset_sub.
exists a.
split => //.
rewrite compset_in.
move=> Hin.
apply Hex.
exists a.
by split.
Qed.

(* 4.1' *)
Theorem invimage_subset {A B} (f: A -> B) (Q1 Q2: Ensemble B):
  Q1 \subset Q2 -> InvImage f Q1 \subset InvImage f Q2.
Proof.
move=> Hsubset a Hinv.
by apply Hsubset.
Qed.

(* 4.2' *)
Theorem invimage_cup {A B} (f: A -> B) (Q1 Q2: Ensemble B):
  InvImage f (Q1 \cup Q2) = InvImage f Q1 \cup InvImage f Q2.
Proof.
apply eq_subset'.
- move=> a H.
  rewrite /InvImage [a \in _]/In in H.
  rewrite -cup_or in H.
  case H => Ha;
    by [left | right].
- apply subsets_cup;
    by [left | right].
Qed.

(* こっちのほうは=で繋がれてて綺麗 *)
(* 4.3' *)
Theorem invimage_cap {A B} (f: A -> B) (Q1 Q2: Ensemble B):
  InvImage f (Q1 \cap Q2) = InvImage f Q1 \cap InvImage f Q2.
Proof.
apply eq_subset'.
- apply subsets_cap => a;
    rewrite /In /InvImage;
    rewrite -cap_and;
    by case.
- move=> a'.
  case => a HQ1 HQ2.
  by split.
Qed.

(* 4.4' *)
Theorem invimage_sub {A B} (f: A -> B) (Q: Ensemble B):
  InvImage f (FullSet - Q) = FullSet - InvImage f Q.
Proof.
rewrite 2!fullset_sub.
apply eq_subset'.
- rewrite /InvImage => a Hin.
  rewrite compset_in => Hout.
  by rewrite {1}/In compset_in in Hin.
- rewrite /InvImage => a.
  rewrite compset_in => Hout.
  by rewrite {1}/In compset_in => Hin.
Qed.

(* 4.5 *)
Theorem invimage_image {A B} (f: A -> B) (P: Ensemble A):
  P \subset InvImage f (Image f P).
Proof.
move=> a H.
by exists a.
Qed.

(* 4.5' *)
Theorem image_invimage {A B} (f: A -> B) (Q: Ensemble B):
  Image f (InvImage f Q) \subset Q.
Proof.
move=> b.
case => a.
case => H Heq.
by rewrite -Heq.
Qed.

Definition Surjective {A B} (f: A -> B) := Image f FullSet = FullSet.

Definition Injective {A B} (f: A -> B) := forall a a', f a = f a' -> a = a'.

Definition Bijective {A B} (f: A -> B) := Surjective f /\ Injective f.

Theorem surjective_exists {A B} (f: A -> B):
  Surjective f <-> forall b, exists a, f a = b.
Proof.
rewrite /Surjective.
rewrite -eq_fullset.
rewrite image_def_range_eq_value_range.
split;
  move=> H b;
  by [rewrite -value_range_map_as_corr | rewrite value_range_map_as_corr].
Qed.

Theorem injective_exists_unique {A B} (f: A -> B):
  Injective f <-> forall b, b \in ValueRange (MapAsCorr f) -> exists! a, f a = b.
Proof.
rewrite /Injective.
Search ValueRange MapAsCorr.
split.
- move=> H b.
  rewrite value_range_map_as_corr.
  case => a Ha.
  subst.
  exists a.
  split => // a' Heq.
  by apply H.
- move=> H a a' Hfeq.
  move: (H (f a)) Hfeq; clear H.
  rewrite value_range_map_as_corr.
  case. (* ここでcaseするのは悪手な感じがする *)
    by exists a.
  move=> a2.
  rewrite /unique.
  case => Ha2 Heq.
  move: (Heq a').
  move=> H H2.



Admitted.

(* 標準的単射についての話が出てくるけれど、正直当たり前にしか見えないので一旦飛ばす *)

(* ここで関数外延性公理を使い始める *)
(* S4 定理4 *)
Theorem invcorr_is_map_iff_bijective {A B} (f: A -> B):
  (exists g: B -> A, InvCorr (MapAsCorr f) = MapAsCorr g) <-> Bijective f.
Proof.
split.
- case => g Hg.
  move: Hg.
  split.
  + rewrite /Surjective.
    rewrite -eq_fullset => b.
    rewrite image_def_range_eq_value_range. (* この特徴はSurjectiveに言えることだから、Lemmaを立てたほうがいい *)
    rewrite -def_range_inv_corr_to_value_range.
    rewrite Hg.
    rewrite def_range_map_as_corr.
    by exists (g b).
  + rewrite injective_exists_unique => b Hb.
    exists (g b).
    rewrite /unique.
    split.
    * (* f (g b) = b *)

      admit.
    * move=> a Heq.
      subst.
      (* g (f a) = a *)

      admit.
- case => Hsur Hin.
  suff: B -> A.
  move=> g.
  exists g.
  rewrite /InvCorr /MapAsCorr /In.
  apply functional_extensionality => b.
  apply functional_extensionality => a.


Admitted.

(* S4 定理4の一部 *)
Theorem invcorr_bijective {A B} (f: A -> B):
  Bijective f <-> (exists g: B -> A, Bijective g).
Proof.
rewrite -invcorr_is_map_iff_bijective.
split;
  case => g Hg;
  exists g.
- admit.
- admit.
Admitted.

Definition composite {A B C} (f: A -> B) (g: B -> C): (A -> C) := fun a => g(f a).




End Section4.

End Ensembles.















