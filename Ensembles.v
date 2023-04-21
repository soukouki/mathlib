(* 集合・位相入門(松坂)1 をCoqで証明しつつ読んでいく *)

Add LoadPath "." as Local.

From mathcomp Require Import ssreflect.
Require Import Coq.Logic.Description.
Require Import Local.Classical.

Module Ensembles.
Declare Scope ensemble_scope.
Open Scope ensemble_scope.

Section Section1.

Variable T: Type.

Definition Ensemble := T -> Prop.

Definition In (a: T) (A: Ensemble): Prop := A a.
Notation "a \in A" := (In a A) (at level 55).

Notation "a \notin A" := (~ In a A) (at level 55).

Inductive EmptySet: Ensemble := .
Notation "\emptyset" := EmptySet.

(* 外延性の公理 *)
Axiom eq_axiom: forall (A B: Ensemble),
  (forall (x: T), (x \in A <-> x \in B)) -> A = B.

Lemma eq_iff: forall (A B: Ensemble),
  (forall (x: T), (x \in A <-> x \in B)) <-> A = B.
Proof.
move=> A B.
split.
- by apply eq_axiom.
- move=> HAB x.
  by rewrite HAB.
Qed.

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
Theorem emptyset_subset: forall A, \emptyset \subset A.
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
Theorem emptyset_cup: forall A, \emptyset \cup A = A.
Proof.
move=> A.
by apply subset_cup_eq.
Qed.


Inductive Cap (A B: Ensemble): Ensemble :=
  Cap_intro: forall x: T, x \in A -> x \in B -> x \in (Cap A B).
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
Theorem emptyset_cap: forall A, \emptyset \cap A = \emptyset.
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
  | Sub_intro: forall x: T, x \in A -> x \notin B -> x \in Sub A B.
Notation "A - B" := (Sub A B). (* at level 50 *)

Lemma sub_iff: forall A B x, x \in A - B <-> x \in A /\ x \notin B.
Proof.
move=> A B x.
split.
- case => x1.
  by split => //.
- case.
  by apply Sub_intro.
Qed.

Lemma sub_emptyset: forall A, A - \emptyset = A.
Proof.
move=> A.
apply eq_axiom => x.
split.
- by case.
- by split => //.
Qed.

Lemma emptyset_sub: forall A, \emptyset - A = \emptyset.
Proof.
move=> A.
apply eq_axiom => x.
split => //.
by case.
Qed.

Lemma sub_sim_emptyset: forall A, A - A = \emptyset.
Proof.
move=> A.
apply eq_axiom => x.
split => //.
rewrite sub_iff.
by case.
Qed.


Inductive FullSet: Ensemble :=
  | FullSet_intro: forall x, x \in FullSet.

Lemma fullset_cap: forall A, FullSet \cap A = A.
Proof.
move=> A.
by rewrite cap_comm -subset_cap_eq.
Qed.

Lemma fullset_cup: forall A, FullSet \cup A = FullSet.
Proof.
move=> A.
by rewrite cup_comm -subset_cup_eq.
Qed.


Inductive ComplementarySet (A: Ensemble): Ensemble :=
  | ComplementarySet_intro: forall x, x \in FullSet - A -> x \in ComplementarySet A.
Notation "A ^ 'c'" := (ComplementarySet A) (at level 30).

Lemma __compset: forall A, A^c = fun x => x \notin A.
Proof.
move=> A.
apply eq_subset'.
- move=> x1 HA.
  case HA => x2.
  by case.
- split.
  by split => //.
Qed.

Lemma compset_in: forall A x, x \in A^c <-> x \notin A.
Proof.
move=> A x.
by rewrite __compset.
Qed.

(* (2.12.1) *)
Theorem compset_cup: forall A, A \cup A^c = FullSet.
Proof.
move=> A.
apply eq_axiom => x.
split => // _.
rewrite -cup_or.
rewrite compset_in.
by apply classic. (* ここで古典論理を使い始めた *)
Qed.

(* (2.12.2) *)
Theorem compset_cap: forall A, A \cap A^c = EmptySet.
Proof.
move=> A.
apply eq_axiom => x1.
split => //.
case => x2.
by rewrite compset_in.
Qed.

(* (2.13) *)
Theorem compset_twice: forall A, A^c^c = A.
Proof.
move=> A.
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
Theorem compset_subset: forall A B, A \subset B <-> B^c \subset A^c.
Proof.
move=> A B.
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
Theorem de_morgan_cup: forall A B, (A \cup B)^c = A^c \cap B^c.
Proof.
move=> A B.
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
Theorem de_morgan_cap: forall A B, (A \cap B)^c = A^c \cup B^c.
Proof.
move=> A B.
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

Lemma sub_fullset: forall A, A - FullSet = \emptyset.
Proof.
move=> A.
apply eq_axiom => x.
rewrite sub_iff.
rewrite -compset_in compset_fullset.
rewrite cap_and.
by rewrite cap_comm emptyset_cap.
Qed.

Lemma fullset_sub: forall A, FullSet - A = A^c.
Proof.
move=> A.
apply eq_axiom => x.
rewrite sub_iff.
rewrite -compset_in.
rewrite cap_and.
by rewrite fullset_cap.
Qed.

Lemma sub_compset: forall A, A - A^c = A.
Proof.
move=> A.
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

Definition FamilyEnsemble := (Ensemble (Ensemble T)).

(* ドイツ文字の変数は、AA, BBのように2文字つなげて区別する *)

Inductive BigCup (AA: FamilyEnsemble): Ensemble T :=
  | big_cup_intro: forall x: T, (exists A: Ensemble T, A \in AA -> x \in A) -> x \in BigCup AA.
Notation "\bigcup AA" := (BigCup AA) (at level 50).

Inductive BigCap (AA: FamilyEnsemble): Ensemble T :=
  | big_cap_intro: forall x: T, (forall A: Ensemble T, A \in AA -> x \in A) -> x \in BigCap AA.
Notation "\bigcap AA" := (BigCap AA) (at level 50).

(* (2.17) *)
Theorem big_cup_in: forall AA A, A \in AA -> A \subset \bigcup AA.
Proof.
move=> AA A HA_in_AA.
split.
by exists A.
Qed.

(* (2.18) *)
(* /\になってる部分は->だと思うんだけれど、->だと証明できなかった・・・そのうち考える *)
Theorem big_cup_subset: forall AA C, (forall A, A \in AA /\ A \subset C) -> \bigcup AA \subset C.
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
Theorem big_cap_in: forall AA A, A \in AA -> \bigcap AA \subset A.
Proof.
move=> AA A HA_in_AA x1.
case => x2.
by apply.
Qed.

(* (2.18)' *)
Theorem big_cap_subset: forall AA C, (forall A, A \in AA -> C \subset A) -> C \subset \bigcap AA.
Proof.
move=> AA C HC_subset_A x1 Hx_in_C.
split => A HA_in_AA.
apply HC_subset_A => //.
Qed.


(* S2 問題1についてはやろうかどうか迷ったけど、一旦置いとく *)

Lemma emptyset_not_in: forall A, A = \emptyset <-> forall x: T, x \notin A.
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
(* 本ではAとBの入れ替わったバージョンもあるが、そちらはこちらが成り立つことから自明に求められるため、省略する *)
Theorem cap_eq_emptyset: forall (A B: Ensemble T), A \cap B = \emptyset <-> A \subset B^c.
Proof.
move=> A B.
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
Theorem sub_cap_compset: forall A B: Ensemble T, A - B = A \cap B^c.
Proof.
move=> A B.
apply eq_axiom => x.
by rewrite sub_iff -cap_and -compset_in.
Qed.

(* S2 問題3a-2 (A=B) *)
Theorem sub_cup_sub: forall A B: Ensemble T, A - B = (A \cup B) - B.
Proof.
move=> A B.
apply eq_axiom => x.
rewrite 2!sub_cap_compset.
rewrite cup_cap_distrib.
rewrite compset_cap.
by rewrite cup_comm emptyset_cup.
Qed.

(* S2 問題3a-3 (A=C) *)
Theorem sub_cap_sub: forall A B: Ensemble T, A - B = A - (A \cap B).
Proof.
move=> A B.
rewrite 2!sub_cap_compset.
rewrite de_morgan_cap.
rewrite [A \cap (_ \cup _)]cap_comm cup_cap_distrib.
rewrite [A^c \cap A]cap_comm compset_cap emptyset_cup.
by rewrite cap_comm.
Qed.

(* S2 問題3b *)
Theorem sub_cap_empty: forall A B: Ensemble T, A - B = A <-> A \cap B = \emptyset.
Proof.
move=> A B.
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
Theorem sub_eq_emptyset: forall A B: Ensemble T, A - B = \emptyset <-> A \subset B.
Proof.
move=> A B.
rewrite sub_cap_compset.
rewrite cap_eq_emptyset.
by rewrite compset_twice.
Qed.

(* S2 問題4a *)
Theorem sub_cup: forall A B C: Ensemble T, A - (B \cup C) = (A - B) \cap (A - C).
Proof.
move=> A B C.
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
Theorem sub_cap: forall A B C: Ensemble T, A - (B \cap C) = (A - B) \cup (A - C).
Proof.
move=> A B C.
rewrite sub_cap_compset.
rewrite de_morgan_cap.
rewrite cap_comm.
rewrite cup_cap_distrib.
rewrite 2![_ \cap A]cap_comm.
by rewrite -2!sub_cap_compset.
Qed.

(* S2 問題4c *)
Theorem cup_sub: forall A B C: Ensemble T, (A \cup B) - C = (A - C) \cup (B - C).
Proof.
move=> A B C.
rewrite sub_cap_compset.
rewrite cup_cap_distrib.
by rewrite -2!sub_cap_compset.
Qed.

(* S2 問題4d *)
Theorem cap_sub: forall A B C: Ensemble T, (A \cap B) - C = (A - C) \cap (B - C).
Proof.
move=> A B C.
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
Theorem cap_sub': forall A B C: Ensemble T, A \cap (B - C) = (A \cap B) - (A \cap C).
Proof.
move=> A B C.
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
Theorem sub_sub_eq_sub_cup: forall A B C: Ensemble T, (A - B) - C = A - (B \cup C).
Proof.
move=> A B C.
apply eq_axiom => x.
rewrite sub_cap_compset -cap_and.
rewrite sub_cap_compset -cap_and.
rewrite and_assoc.
rewrite 2!cap_and.
rewrite -de_morgan_cup.
by rewrite -sub_cap_compset.
Qed.

(* S2 問題5b *)
Theorem sub_sub_eq_cup: forall A B C: Ensemble T, A - (B - C) = (A - B) \cup (A \cap C).
Proof.
move=> A B C.
rewrite [B-C]sub_cap_compset.
rewrite sub_cap.
rewrite [A - C^c]sub_cap_compset.
by rewrite compset_twice.
Qed.

(* S2 問題6 *)
Theorem cup_cap_eq_cup_cap: forall A C: Ensemble T, A \subset C -> forall B, A \cup (B \cap C) = (A \cup B) \cap C.
Proof.
move => A C HA_subset_C B.
rewrite cup_comm.
rewrite cap_cup_distrib.
rewrite [B \cup A]cup_comm [C \cup A]cup_comm.
have: A \cup C = C.
  by rewrite -subset_cup_eq.
move=> H.
by rewrite H.
Qed.

Definition SymmetricDifference (A B: Ensemble T) := (A - B) \cup (B - A).
Notation "A \triangle B" := (SymmetricDifference A B) (at level 50).

(* もう一つの等式 *)
Lemma sym_diff_compset: forall A B, A \triangle B = (A \cap B^c) \cup (A^c \cap B).
Proof.
move=> A B.
rewrite /SymmetricDifference.
rewrite 2!sub_cap_compset.
by rewrite [B \cap A^c]cap_comm.
Qed.

(* S2 問題7a *)
Theorem sym_diff_comm: forall A B, A \triangle B = B \triangle A.
Proof.
move=> A B.
rewrite 2!sym_diff_compset.
rewrite [B \cap A^c]cap_comm [B^c \cap A]cap_comm.
by rewrite cup_comm.
Qed.

(* S2 問題7b *)
Theorem sym_diff_sub: forall A B, A \triangle B = (A \cup B) - (A \cap B).
Proof.
move=> A B.
rewrite /SymmetricDifference.
rewrite cup_sub.
rewrite 2!sub_cap.
rewrite 2!sub_sim_emptyset.
by rewrite [_ \cup \emptyset]cup_comm 2!emptyset_cup.
Qed.

Lemma sub_comm: forall A B C: Ensemble T, (A - B) - C = (A - C) - B.
Proof.
move=> A B C.
apply eq_axiom => x.
by rewrite !sub_iff !and_assoc [_ \notin _ /\ _ \notin _]and_comm.
Qed.

(* きれいな解法を思いつかなかった *)
Lemma sub_merge: forall A B C: Ensemble T, (A - C) - (B - C) = A - B - C.
Proof.
move=> A B C.
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

Lemma sub_sub_cap: forall A B C: Ensemble T, A - (B - C) \cap B = A \cap B \cap C.
Proof.
move=> A B C.
rewrite !sub_cap_compset.
rewrite de_morgan_cap.
rewrite compset_twice.
rewrite cap_assoc.
rewrite cup_cap_distrib.
rewrite [B^c \cap B]cap_comm compset_cap.
rewrite emptyset_cup.
by rewrite [C \cap B]cap_comm cap_assoc.
Qed.

Lemma sym_diff_assoc_help: forall A B C: Ensemble T,
  (A - ((B - C) \cup (C - B))) = ((A - B) - C) \cup (A \cap B \cap C).
Proof.
move=> A B C.
rewrite -sub_sub_eq_sub_cup.
rewrite sub_sub_eq_cup.
rewrite sub_comm.
rewrite sub_merge.
by rewrite sub_sub_cap.
Qed.

(* S2 問題7c *)
Theorem sym_diff_assoc: forall A B C,
  (A \triangle B) \triangle C = A \triangle (B \triangle C).
Proof.
move=> A B C.
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
Theorem sym_diff_cap_distrib: forall A B C,
  A \cap (B \triangle C) = (A \cap B) \triangle (A \cap C).
Proof.
move=> A B C.
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
Theorem sym_diff_emptyset_l: forall A, A \triangle EmptySet = A.
Proof.
move=> A.
rewrite /SymmetricDifference.
rewrite sub_emptyset emptyset_sub.
by rewrite cup_comm emptyset_cup.
Qed.

(* S2 問題8b *)
Theorem sym_diff_fullset: forall A, A \triangle FullSet = A^c.
Proof.
move=> A.
rewrite /SymmetricDifference.
rewrite sub_fullset fullset_sub.
by rewrite emptyset_cup.
Qed.

(* S2 問題8c *)
Theorem sym_diff_emptyset_r: forall A, A \triangle A = EmptySet.
Proof.
move=> A.
rewrite /SymmetricDifference.
rewrite sub_sim_emptyset.
by rewrite cup_diag.
Qed.

(* S2 問題8d *)
Theorem sym_diff_compset_fullset: forall A, A \triangle A^c = FullSet.
Proof.
move=> A.
rewrite sym_diff_compset.
rewrite compset_twice.
rewrite 2!cap_diag.
by rewrite compset_cup.
Qed.

Lemma sym_diff_not_in_from_in: forall A B x, x \in A -> x \in B -> x \notin A \triangle B.
Proof.
move=> A B x1 HA HB H.
move: H HA HB.
case => x2.
- rewrite sub_iff.
  by case.
- rewrite sub_iff.
  by case.
Qed.

Lemma sub_sym_diff: forall A1 A2 B1 B2 x,
  x \in A1 - B1 ->
  A1 \triangle A2 = B1 \triangle B2 ->
  x \in A2 \triangle B2.
Proof.
move=> A1 A2 B1 B2 x1.
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
  case H => x3.
  + by case.
  + by case.
Qed.

(* S2 問題9 *)
Theorem sym_diff_shakeup: forall A1 A2 B1 B2, A1 \triangle A2 = B1 \triangle B2 -> A1 \triangle B1 = A2 \triangle B2.
Proof.
move=> A1 A2 B1 B2 Htriangle.
rewrite -eq_iff => x0.
split.
- rewrite {1}/SymmetricDifference.
  case => x1 Hsub.
  + by apply (sub_sym_diff A1 A2 B1 B2).
  + rewrite sym_diff_comm.
    by apply (sub_sym_diff B1 B2 A1 A2).
- assert (Htriangle': A2 \triangle A1 = B2 \triangle B1).
    symmetry.
    by rewrite [B2 \triangle B1]sym_diff_comm [A2 \triangle A1]sym_diff_comm.
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

(* Corr = Correspondence *)
Definition Corr (A B: Type) := A -> Ensemble B.
Notation "A ->c B" := (Corr A B) (at level 99).

Definition Graph {A B: Type} (C: A ->c B): Ensemble (A * B) := (fun x: (A * B) => (snd x) \in C (fst x)).

(* (3.1) *)
Theorem corr_from_graph:
  forall A B (C: A ->c B) (a: A), C a = ((fun b => (Graph C) (pair a b)): Ensemble B).
Proof.
move=> A B C a.
by [].
Qed.

(* S3 定理1 *)
Theorem exists_one_graph_from_pair: forall A B (X: Ensemble (A * B)), exists! (G: A ->c B), X = Graph G.
Proof.
move=> A B X.
exists (fun a b => X (pair a b)).
split.
- rewrite /Graph.
  apply eq_axiom => x.
  by rewrite /In -surjective_pairing.
- move=> C HX.
  by rewrite HX.
Qed.

Definition DefRange   {A B: Type} (C: A ->c B): Ensemble A := fun a: A => exists b: B, (a, b) \in Graph(C).
Definition ValueRange {A B: Type} (C: A ->c B): Ensemble B := fun b: B => exists a: A, (a, b) \in Graph(C).

Definition InvCorr {A B: Type} (C: A->c B): B ->c A := fun (b: B) (a: A) => b \in C a.

Theorem def_range_neq_empty_set: forall A B (C: A ->c B), DefRange C = fun a: A => C a <> \emptyset.
Proof.
move=> A B C.
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
Theorem in_inv_corr: forall A B (C: A ->c B) a b, b \in C a <-> a \in (InvCorr C) b.
Proof. by []. Qed.

(* (3.3) *)
Theorem def_range_inv_corr_to_value_range: forall A B (C: A ->c B), DefRange(InvCorr C) = ValueRange C.
Proof. by []. Qed.

(* (3.3)' *)
Theorem value_range_inv_corr_to_def_range: forall A B (C: A ->c B), DefRange(InvCorr C) = ValueRange C.
Proof. by []. Qed.

(* 3.4 *)
Theorem inv_corr_twice: forall A B (C: A ->c B), InvCorr (InvCorr C) = C.
Proof. by []. Qed.

(* p.27 *)
Theorem inv_corr_is_not_empty_iff_in_value_range: forall A B b (C: A ->c B),
  (InvCorr C b <> \emptyset) <-> b \in ValueRange C.
move=> A B b C.
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
Notation "A -> B" := (Corr A B) (at level 90).

これは関数と等しいので、今回は定義しない。
 *)

Definition MapAsCorr {A B: Type} (M: A -> B): A ->c B := 
  fun a b => b = M a.

Definition Identity {A: Type} (M: A -> A) := identity.

(* 分かりづらいんじゃ！ *)
Set Implicit Arguments.
Definition get_value := proj1_sig.
Definition get_proof := proj2_sig.
Unset Implicit Arguments.

(* S3 定理2 *)
Theorem exist_one_map_equivalent_to_graphs: forall {A B} G,
  (exists M: A -> B, G = Graph (MapAsCorr M)) <-> (forall a, exists! b, (a, b) \in G).
Proof.
move=> A B G.
split.
- case => M HG a.
  exists (M a).
  rewrite HG.
  by split => //.
- move=> HinG.
  have: (forall a: A, {b: B | (a, b) \in G}).
    move=> a.
    apply constructive_definite_description.
    by apply (HinG a).
  move=> Sigb.
  exists (fun a: A => get_value (Sigb a)).
  apply eq_subset'.
  + move=> x Hx.
    rewrite /Graph /MapAsCorr /In.
    (* bからグラフ上の(a, b)は一意に求められることを示す -> _ = _ を処理するのに使える *)
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
Theorem map_as_corr_inv_corr: forall {A B: Type} (C: A ->c B),
  (exists! M: A -> B, MapAsCorr M = C) <->
  (DefRange C = FullSet /\ (forall b b', b <> b' -> InvCorr C b \cap InvCorr C b' = \emptyset)).
Proof.
move=> A B C.
split.
- move=> HM.
  have: {M: A -> B | MapAsCorr M = C}.
    by apply constructive_definite_description.
  clear HM => HM.
  split.
  + apply eq_subset' => // a HA.
    rewrite /In /DefRange.
    exists (get_value HM a).
    rewrite /In /Graph /snd /fst.
    rewrite /In.
    rewrite /get_value.
    move: (proj2_sig HM) => H.
    try rewrite -H. (* Dependent type error *)
    admit.
  + move=> b b' HB.
    apply (iffRL (emptyset_not_in _ (InvCorr C b \cap InvCorr C b'))) => a.
    


    move=> H.
    apply HB. 
    move: H.
    case => a' HinB HinB'.
    




Restart.

move=> A B C.
split.
- move=> Hexists.
  split.
  + apply eq_subset' => // a _.
    rewrite /DefRange /In.
    have: {M: A -> B | MapAsCorr M = C}.
      by apply constructive_definite_description.
    move=> Hm.
    exists ((proj1_sig Hm) a).
    rewrite /Graph /In /=.
    move: (proj2_sig Hm) => Hm'.
    try rewrite -Hm'.
    admit.
  + move=> b b' Hbneqb'.
    apply eq_subset' => // a.
    have: {M: A -> B | MapAsCorr M = C}.
      by apply constructive_definite_description.
    move=> Hm.
    move: (proj2_sig Hm) => Hm'.
    rewrite -Hm'. (* こっちではできるんだ *)
    rewrite /MapAsCorr.
    (* bかb'のどっちかを固定しないと無理そう？ *)
    admit.
- case => HDefRange HInvCorr.
  rewrite -unique_existence.
  split.
  + (* exists (fun a: A => C a). Aを受け取ってBを返す関数がいる。そんでそれ自体をMapAsCorrに渡すとCと等しくなる、
    と思ったけど、Ensemble Bの中からbを取り出せる(emptysetでない)という証明もしないといけないから、そのままではいけない *)
  admit.
Admitted.

End Section3.


Section Section4.


(* メモ: Imageが来たら先でexists *)
Definition Image {A B: Type} (f: A -> B) (P: Ensemble A): Ensemble B :=
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


Definition InvImage {A B: Type} (f: A -> B) (Q: Ensemble B): Ensemble A :=
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

(* TODO: もっと場合分けの少ない、簡潔な証明にする *)
(* 4.2 *)
Theorem image_cup {A B} (f: A -> B) (P1 P2: Ensemble A):
  Image f (P1 \cup P2) = Image f P1 \cup Image f P2.
Proof.
apply eq_subset'.
- move=> b.
  case => a'.
  case.
  case; clear a'.
  + move=> a HP1 Heq.
    left.
    exists a.
    by split => //.
  + move=> a HP2 Heq.
    right.
    exists a.
    by split => //.
- move=> b'.
  case; clear b'.
  + move=> b.
    case => a.
    case => HP1 Heq.
    rewrite -Heq.
    exists a.
    split => //.
    by left.
  + move=> b.
    case => a.
    case => HP2 Heq.
    rewrite -Heq.
    exists a.
    split => //.
    by right.
Qed.

(* 4.3 *)
Theorem image_cap {A B} (f: A -> B) (P1 P2: Ensemble A):
  Image f (P1 \cap P2) \subset Image f P1 \cap Image f P2.
Proof.
move=> b.
case => a.
case.
rewrite -cap_and.
case => HP1 HP2 Heq.
rewrite -Heq.
by [split; exists a; split].
Qed.

(* 4.4 *)
Theorem image_sub {A B} (f: A -> B) (P: Ensemble A):
  Image f FullSet - Image f P \subset Image f (FullSet - P).
Proof.




End Section4.
About hoge.

End Ensembles.















