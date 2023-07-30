(* 集合・位相入門(松坂)1 をCoqで証明しつつ読んでいく *)

Set Implicit Arguments.

Add LoadPath "." as Local.

From mathcomp Require Import ssreflect.
Require Import Local.Classical.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.IndefiniteDescription.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.PropExtensionality.

Module Ensembles.

Declare Scope ensemble_scope.
Open Scope ensemble_scope.


Section Section1.

Variable T: Type.

Definition Ensemble := T -> Prop.

Definition In a (A: Ensemble): Prop := A a.
Notation "a \in A" := (In a A) (at level 55).

Notation "a \notin A" := (~ In a A) (at level 55).

Definition Singleton (a: T): Ensemble := fun a' => a = a'.
Notation "\{ a }" := (Singleton a).

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

Lemma eq_split A B: A \subset B -> B \subset A -> A = B.
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

Lemma singleton_eq a a': a \in \{a'} <-> a = a'.
Proof. by []. Qed.

(* S1 問題1 *)
Theorem singleton_subset a A: a \in A <-> \{a} \subset A.
Proof.
split.
- move=> HA a' Heq.
  by rewrite -Heq.
- move=> HA.
  by apply HA.
Qed.

End Section1.


Notation "a \in A" := (In a A) (at level 55): ensemble_scope.
Notation "\{ a }" := (Singleton a).
Notation "a \notin A" := (~ In a A) (at level 55): ensemble_scope.
Notation "\emptyset" := (EmptySet): ensemble_scope.
Arguments EmptySet {_}.
Notation "A \subset B" := (Subset A B) (at level 55): ensemble_scope.


Section Section2.

Variable T: Type.

Inductive Cup A B: Ensemble T :=
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
apply eq_split.
- by apply subsets_cup => //.
- by apply subset_cup_l.
Qed.

(* (2.5) *)
Theorem cup_comm A B: A \cup B = B \cup A.
Proof.
apply eq_split => x;
  rewrite -2!cup_or;
  by rewrite or_comm.
Qed.

(* (2.6) *)
Theorem cup_assoc A B C: (A \cup B) \cup C = A \cup (B \cup C).
Proof.
apply eq_split => x;
  rewrite -4!cup_or;
  by rewrite or_assoc.
Qed.

(* (2.7) *)
Theorem subset_cup_eq A B: A \subset B <-> A \cup B = B.
Proof.
split.
- move=> HA_subset_B.
  apply eq_split.
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


Inductive Cap A B: Ensemble T :=
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
apply eq_split => x;
  rewrite -cap_and.
- by case.
- by split.
Qed.

(* (2.5)' *)
Theorem cap_comm A B: A \cap B = B \cap A.
Proof.
apply eq_split => x;
  rewrite -2!cap_and.
- by rewrite and_comm.
- by case.
Qed.

(* (2.6)' *)
Theorem cap_assoc A B C: (A \cap B) \cap C = A \cap (B \cap C).
Proof.
apply eq_split => x;
  rewrite -4!cap_and;
  by rewrite and_assoc.
Qed.

(* (2.7)' *)
Theorem subset_cap_eq A B: A \subset B <-> A \cap B = A.
Proof.
split.
- move=> HA_subset_B.
  apply eq_split.
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
apply eq_split => x1.
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
apply eq_split => x1.
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


Inductive Sub A B: Ensemble T :=
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
apply eq_split => x.
- by case.
- by split.
Qed.

Lemma emptyset_sub A: \emptyset - A = \emptyset.
Proof.
apply eq_split => x //.
by case.
Qed.

Lemma sub_sim_emptyset A: A - A = \emptyset.
Proof.
apply eq_split => x //.
rewrite sub_iff.
by case.
Qed.


Inductive FullSet: Ensemble T :=
  | FullSet_intro: forall x: T, x \in FullSet.

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

Lemma not_emptyset x: x \notin \emptyset <-> x \in FullSet.
Proof.
split => // Hf.
case.
Qed.

Inductive ComplementarySet (A: Ensemble T): Ensemble T :=
  | ComplementarySet_intro: forall x, x \in FullSet - A -> x \in ComplementarySet A.
Notation "A ^ 'c'" := (ComplementarySet A) (at level 30).

Lemma __compset A: A^c = fun x => x \notin A.
Proof.
apply eq_split.
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
apply eq_split => x // _.
rewrite -cup_or.
rewrite compset_in.
by apply classic. (* ここで古典論理を使い始めた *)
Qed.

(* (2.12.2) *)
Theorem compset_cap A: A \cap A^c = EmptySet.
Proof.
apply eq_split => x1 //.
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
apply eq_split => x // _.
by rewrite compset_in.
Qed.

(* (2.14.2) *)
Theorem compset_fullset: FullSet^c = EmptySet.
Proof.
apply eq_split => x1 //.
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
apply eq_split => x1.
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
apply eq_split => x1.
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

Definition FamilyEnsemble T := (Ensemble (Ensemble T)).
Implicit Types AA BB: FamilyEnsemble T.

Definition PowerSet {T} (X: Ensemble T): FamilyEnsemble T := fun A: Ensemble T => A \subset X.

(* p.18にPowerSetの個数を問う問題があるので、余裕があったらやりたい *)

(* ドイツ文字の変数は、AA, BBのように2文字つなげて区別する *)

Inductive BigCup AA: Ensemble T :=
  | bigcup_intro: forall x: T, (exists A: Ensemble T, A \in AA -> x \in A) -> x \in BigCup AA.
Notation "\bigcup AA" := (BigCup AA) (at level 50).

Inductive BigCap AA: Ensemble T :=
  | bigcap_intro: forall x: T, (forall A: Ensemble T, A \in AA -> x \in A) -> x \in BigCap AA.
Notation "\bigcap AA" := (BigCap AA) (at level 50).

(* (2.17) *)
Theorem bigcup_in AA A: A \in AA -> A \subset \bigcup AA.
Proof.
move=> HA_in_AA.
split.
by exists A.
Qed.

(* (2.18) *)
(* /\になってる部分は->だと思うんだけれど、->だと証明できなかった・・・ *)
(* ->の場合、A \in AA までたどり着くけどそれ自体の証明ができない *)
Theorem bigcup_subset AA C: (forall A, A \in AA /\ A \subset C) -> \bigcup AA \subset C.
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
Theorem bigcap_in AA A: A \in AA -> \bigcap AA \subset A.
Proof.
move=> HA_in_AA x1.
case => x2.
by apply.
Qed.

(* (2.18)' *)
Theorem bigcap_subset AA C: (forall A, A \in AA -> C \subset A) -> C \subset \bigcap AA.
Proof.
move=> HC_subset_A x1 Hx_in_C.
split => A HA_in_AA.
by apply HC_subset_A.
Qed.


(* S2 問題1についてはやろうかどうか迷ったけど、一旦置いとく *)

Lemma emptyset_not_in A: A = \emptyset <-> forall x: T, x \notin A.
Proof.
split.
- move=> HA x.
  by rewrite HA.
- move=> Hnx.
  apply eq_split => x //.
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
rewrite -2!sub_cap_compset.
apply eq_refl.
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
have: A \cup C = C => [| H ].
  by rewrite -subset_cup_eq.
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
    by apply sym_diff_not_in_from_in.
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
  + by apply (sub_sym_diff Hsub).
  + rewrite sym_diff_comm.
    by apply (sub_sym_diff Hsub).
- have: (A2 \triangle A1 = B2 \triangle B1) => [| Htriangle' ].
    symmetry.
    by rewrite [B2 \triangle B1]sym_diff_comm [A2 \triangle A1]sym_diff_comm.
  rewrite {1}/SymmetricDifference.
  case => x1 Hsub.
  + by apply (sub_sym_diff Hsub).
  + rewrite sym_diff_comm.
    by apply (sub_sym_diff Hsub).
Qed.

End Section2.


Notation "A \cup B" := (Cup A B) (at level 50): ensemble_scope.
Notation "A \cap B" := (Cap A B) (at level 50): ensemble_scope.
Notation "A - B" := (Sub A B) (* at level 50 *): ensemble_scope.
Notation "A ^ 'c'" := (ComplementarySet A) (at level 30): ensemble_scope.

Arguments FullSet {_}.
Arguments BigCup {_} _ _.
Arguments BigCap {_} _ _.

Notation "\bigcup AA" := (BigCup AA) (at level 50): ensemble_scope.
Notation "\bigcap AA" := (BigCap AA) (at level 50): ensemble_scope.


Section Section3.

Implicit Types A B: Type.

(* Corr = Correspondence *)
Definition Corr A B := A -> Ensemble B.
Notation "A ->c B" := (Corr A B) (at level 99).

Definition Graph A B (C: A ->c B): Ensemble (A * B) := (fun x: (A * B) => (snd x) \in C (fst x)).

(* (3.1) *)
Theorem corr_from_graph A B C (a: A):
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

Definition DefRange   A B (C: A ->c B): Ensemble A := fun a: A => exists b: B, (a, b) \in Graph(C).
Definition ValueRange A B (C: A ->c B): Ensemble B := fun b: B => exists a: A, (a, b) \in Graph(C).

Definition InvCorr A B (C: A->c B): B ->c A := fun (b: B) (a: A) => b \in C a.

Theorem defrange_neq_empty_set A B (C: A ->c B): DefRange C = fun a: A => C a <> \emptyset.
Proof.
apply eq_split => a.
- rewrite /In /DefRange.
  case => b HinG.
  rewrite emptyset_not_in => H.
  by apply (H b).
- rewrite /In /DefRange.
  rewrite emptyset_not_in.
  rewrite -exists_iff_not_forall_not.
  case => b Hin.
  by exists b.
Qed.

Lemma defrange_exists A B (C: A ->c B): DefRange C = fun a: A => exists b, b \in C a.
Proof. by []. Qed.

(* (3.2) *)
Theorem in_invcorr A B (C: A ->c B) a b: b \in C a <-> a \in (InvCorr C) b.
Proof. by []. Qed.

(* (3.3) *)
Theorem defrange_invcorr_to_valuerange A B (C: A ->c B): DefRange(InvCorr C) = ValueRange C.
Proof. by []. Qed.

(* (3.3)' *)
Theorem valuerange_invcorr_to_defrange A B (C: A ->c B): ValueRange(InvCorr C) = DefRange C.
Proof. by []. Qed.

(* 3.4 *)
Theorem invcorr_twice A B (C: A ->c B): InvCorr (InvCorr C) = C.
Proof. by []. Qed.

Lemma in_emptyset A (x: A): x \in \emptyset <-> False.
Proof. by []. Qed.

(* p.27 *)
Theorem invcorr_is_not_empty_iff_in_valuerange A B b (C: A ->c B):
  (InvCorr C b <> \emptyset) <-> b \in ValueRange C.
split.
- move=> Hneq.
  apply NNPP => Hnot_in.
  apply Hneq.
  apply eq_split => // x Hin_inv.
  rewrite in_emptyset.
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

Definition MapAsCorr A B (f: A -> B): A ->c B := 
  fun a b => b = f a.

Definition Identity {A}: A -> A := fun a: A => a.
Notation "\I A" := (Identity: A -> A) (at level 30).


(* 分かりづらいんじゃ！ *)
Definition get_value := proj1_sig.
Definition get_proof := proj2_sig.

(* S3 定理2 *)
Theorem exist_one_map_equivalent_to_graphs A B (G: Ensemble (A * B)):
  (exists f: A -> B, G = Graph (MapAsCorr f)) <-> (forall a, exists! b, (a, b) \in G).
Proof.
split.
- case => f HG a.
  exists (f a).
  rewrite HG.
  by split.
- move=> HinG.
  have: (forall a: A, {b: B | (a, b) \in G}) => [| Sigb ].
    move=> a.
    apply constructive_definite_description.
    by apply HinG.
  exists (fun a: A => get_value (Sigb a)).
  apply eq_split.
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

Lemma singleton_unique_eq A a (P: Ensemble A):
  a \in P -> uniqueness (fun a' => a' \in P) -> \{a} = P.
Proof.
move=> Hin Huniq.
apply eq_split.
- move=> a' HA'.
  rewrite singleton_eq in HA'.
  by rewrite HA'.
- move=> a' HA'.
  rewrite singleton_eq.
  by apply Huniq.
Qed.

Lemma invcorr_cap_emptyset_unique A B (C: A ->c B):
  (forall b b', b <> b' -> InvCorr C b \cap InvCorr C b' = \emptyset) ->
  forall a, uniqueness (fun b => b \in C a).
Proof.
move=> Hinv a b1 b2 HB HB'.
apply NNPP => H1.
move: (Hinv b1 b2 H1).
rewrite cap_eq_emptyset.
rewrite /Subset => H2.
move: (H2 a).
rewrite compset_in.
rewrite -2!in_invcorr.
by apply.
Qed.

(* S3 問題3 *)
Theorem map_as_corr_invcorr A B (C: A ->c B):
  (exists! f: A -> B, MapAsCorr f = C) <->
  (DefRange C = FullSet /\ (forall b b', b <> b' -> InvCorr C b \cap InvCorr C b' = \emptyset)).
Proof.
rewrite -eq_fullset.
split.
- move=> Hf.
  have: {f: A -> B | MapAsCorr f = C}.
    by apply constructive_definite_description.
  clear Hf => Hf.
  split.
  + move => a.
    case Hf => f Hfeq.
    exists (f a).
    by rewrite -Hfeq.
  + move=> b b' HB.
    rewrite cap_eq_emptyset.
    case Hf => f Hf' a.
    rewrite -Hf' => Heq.
    rewrite compset_in => Heq'.
    rewrite /InvCorr /MapAsCorr /In in Heq.
    rewrite /InvCorr /MapAsCorr /In in Heq'.
    by rewrite Heq' in HB. (* ここまでは古い証明と同じ *)
- case => Hdef Hinv.
  move: (invcorr_cap_emptyset_unique Hinv) => Huniq.
  have: forall a: A, exists b, \{b} = C a => [ a | Hsig ].
    rewrite /In defrange_exists in Hdef.
    move: (constructive_indefinite_description _ (Hdef a)) => Bsig.
    exists (get_value Bsig).
    apply singleton_unique_eq => //.
    by apply (get_proof Bsig).
  move: (fun a => constructive_indefinite_description _ (Hsig a)) => fsig.
  rewrite -unique_existence.
  split.
  + exists (fun a => get_value (fsig a)).
    apply functional_extensionality => a.
    case (Hsig a) => b HB.
    rewrite -HB.
    symmetry.
    apply singleton_unique_eq.
    * rewrite /MapAsCorr /In.
      apply (Huniq a).
      - by rewrite -HB.
      - move: (get_proof (fsig a)) => H.
        rewrite -eq_iff in H.
        by rewrite -H.
    * rewrite /MapAsCorr /In => b1 b2 HB1 HB2.
      by subst.
  + move=> f f' Hfeq Hfeq'.
    apply functional_extensionality => a.
    apply (Huniq a);
      by [ rewrite -Hfeq | rewrite -Hfeq' ].
Qed.

(* 別証明 *)
Goal forall A B (C: A ->c B),
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
    case Hf => f Hf' a.
    rewrite -Hf' => Heq.
    rewrite compset_in => Heq'.
    rewrite /InvCorr /MapAsCorr /In in Heq.
    rewrite /InvCorr /MapAsCorr /In in Heq'.
    by rewrite Heq' in HB.
- case.
  rewrite -eq_fullset.
  rewrite /In defrange_exists => Hdef Hinv.
  move: (invcorr_cap_emptyset_unique Hinv) => Huniq.
  rewrite -unique_existence.
  split.
  + have: { f: A -> B | forall a b, f a = b -> b \in C a } => [| F ].
      apply constructive_indefinite_description.
      move: (fun a => constructive_indefinite_description _ (Hdef a)) => sigB.
      exists (fun a => get_value (sigB a)) => a b Heq.
      rewrite -Heq.
      by apply (get_proof (sigB a)).
    exists (get_value F).
    apply functional_extensionality => a.
    have: get_value F a \in C a => [| Hin ].
      by apply (get_proof F a (get_value F a)).
    apply eq_split.
    + move=> b H.
      by rewrite H.
    + move=> b Hb.
      by apply (Huniq a).
  + move=> f1 f2 Heq1 Heq2.
    apply functional_extensionality => a.
    apply (Huniq a);
      by [ rewrite -Heq1 | rewrite -Heq2 ].
Qed.

Lemma defrange_map_as_corr A B (f: A -> B) a:
  a \in DefRange (MapAsCorr f) <-> exists b, f a = b.
Proof.
split;
  case => b H;
  by exists b.
Qed.

Lemma valuerange_map_as_corr A B (f: A -> B) b:
  b \in ValueRange (MapAsCorr f) <-> exists a, f a = b.
Proof.
split;
  case => a H;
  by exists a.
Qed.

End Section3.


Notation "A ->c B" := (Corr A B) (at level 99): ensemble_scope.
Notation "\I A" := (Identity: A -> A) (at level 30): ensemble_scope.


Section Section4.

Implicit Types A B: Type.

(* メモ: Imageが来たら先でexists *)
Definition Image A B (f: A -> B) (P: Ensemble A): Ensemble B :=
  fun b: B => exists a, a \in P /\ f a = b.

(* p.30 *)
Theorem image_defrange_eq_valuerange A B (f: A -> B):
  Image f (FullSet: Ensemble A) = ValueRange (MapAsCorr f).
Proof.
apply eq_split.
- move=> b.
  case => a.
  case => _ Heq.
  by exists a.
- move=> b.
  case => a Hb.
  by exists a.
Qed.

(* p.30 *)
Theorem image_emptyset_iff A B (f: A -> B) P:
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

Definition InvImage A B (f: A -> B) (Q: Ensemble B): Ensemble A :=
  fun a: A => f a \in Q.

(* p.31 *)
Theorem invimage_fullset A B f:
  InvImage f (FullSet: Ensemble B) = (FullSet: Ensemble A).
Proof.
by apply eq_split => //.
Qed.

(* 4.1 *)
Theorem image_subset A B (f: A -> B) P1 P2:
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
Theorem image_cup A B (f: A -> B) P1 P2:
  Image f (P1 \cup P2) = Image f P1 \cup Image f P2.
Proof.
apply eq_split.
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
Theorem image_cap A B (f: A -> B) P1 P2:
  Image f (P1 \cap P2) \subset Image f P1 \cap Image f P2.
Proof.
apply subsets_cap.
- apply image_subset.
  by apply cap_subset_l.
- apply image_subset.
  by apply cap_subset_r.
Qed.

(* 4.4 *)
Theorem image_sub A B (f: A -> B) P:
  Image f FullSet - Image f P \subset Image f (FullSet - P).
Proof.
move=> b.
rewrite image_defrange_eq_valuerange.
case => b'.
rewrite valuerange_map_as_corr.
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
Theorem invimage_subset A B (f: A -> B) Q1 Q2:
  Q1 \subset Q2 -> InvImage f Q1 \subset InvImage f Q2.
Proof.
move=> Hsubset a Hinv.
by apply Hsubset.
Qed.

(* 4.2' *)
Theorem invimage_cup A B (f: A -> B) Q1 Q2:
  InvImage f (Q1 \cup Q2) = InvImage f Q1 \cup InvImage f Q2.
Proof.
apply eq_split.
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
Theorem invimage_cap A B (f: A -> B) Q1 Q2:
  InvImage f (Q1 \cap Q2) = InvImage f Q1 \cap InvImage f Q2.
Proof.
apply eq_split.
- apply subsets_cap => a;
    rewrite /In /InvImage;
    rewrite -cap_and;
    by case.
- move=> a'.
  case => a HQ1 HQ2.
  by split.
Qed.

(* 4.4' *)
Theorem invimage_sub A B (f: A -> B) Q:
  InvImage f (FullSet - Q) = FullSet - InvImage f Q.
Proof.
rewrite 2!fullset_sub.
apply eq_split.
- rewrite /InvImage => a Hin.
  rewrite compset_in => Hout.
  by rewrite {1}/In compset_in in Hin.
- rewrite /InvImage => a.
  rewrite compset_in => Hout.
  by rewrite {1}/In compset_in => Hin.
Qed.

(* 4.5 *)
Theorem invimage_image A B (f: A -> B) P:
  P \subset InvImage f (Image f P).
Proof.
move=> a H.
by exists a.
Qed.

(* 4.5' *)
Theorem image_invimage A B (f: A -> B) Q:
  Image f (InvImage f Q) \subset Q.
Proof.
move=> b.
case => a.
case => H Heq.
by rewrite -Heq.
Qed.

Definition Surjective A B (f: A -> B) := Image f FullSet = FullSet.

Definition Injective A B (f: A -> B) := forall a a', f a = f a' -> a = a'.

Definition Bijective A B (f: A -> B) := Surjective f /\ Injective f.

Lemma surjective_valuerange A B (f: A -> B):
  Surjective f <-> forall b, b \in ValueRange (MapAsCorr f).
Proof.
rewrite /Surjective.
rewrite -eq_fullset.
by rewrite image_defrange_eq_valuerange.
Qed.

Theorem surjective_exists A B (f: A -> B):
  Surjective f <-> forall b, exists a, f a = b.
Proof.
rewrite surjective_valuerange.
split;
  move=> H b;
  by [rewrite -valuerange_map_as_corr | rewrite valuerange_map_as_corr].
    (* 方向が違うだけ *)
Qed.

Theorem injective_uniqueness A B (f: A -> B):
  Injective f <-> forall b, b \in ValueRange (MapAsCorr f) -> uniqueness (fun a => f a = b).
Proof.
split.
- move=> Hinj b Hb.
  rewrite valuerange_map_as_corr in Hb.
  rewrite /uniqueness => a a' Heqa Heqa'.
  apply Hinj.
  by rewrite Heqa Heqa'.
- move=> Hb a a' Heq.
  apply (Hb (f a)) => //.
  rewrite valuerange_map_as_corr.
  by exists a.
Qed.

Theorem injective_exists_unique A B (f: A -> B):
  Injective f <-> forall b, b \in ValueRange (MapAsCorr f) -> exists! a, f a = b.
Proof.
split.
- move=> Hinj b Hexi.
  rewrite -unique_existence.
  split.
  + by rewrite valuerange_map_as_corr in Hexi.
  + apply injective_uniqueness => //.
- rewrite injective_uniqueness.
  move=> H1 b H2.
  case (H1 b H2) => a Huniq.
  case Huniq => Heq H.
  move=> a1 a2 Ha1 Ha2.
  apply eq_stepl with (x := a);
    by apply H.
Qed.

(* 標準的単射についての話が出てくるけれど、正直当たり前にしか見えないので一旦飛ばす。p33に書いてある。 *)

Lemma invcorr_map_as_corr A B (f: A -> B) (g: B -> A):
  InvCorr (MapAsCorr f) = MapAsCorr g -> forall a, g (f a) = a.
Proof.
move=> Heq a.
suff: forall b, b \in \{f a} -> a \in \{g b} => [| b Hbeq ].
  by apply.
suff: a \in MapAsCorr g b => [ H |].
  rewrite /MapAsCorr /In in H.
  by rewrite H.
by rewrite -Heq.
Qed.

Lemma invcorr_map_as_corr' A B (f: A -> B) (g: B -> A):
  InvCorr (MapAsCorr f) = MapAsCorr g -> forall b, f (g b) = b.
Proof.
move=> Heq b.
suff: forall a, a \in \{g b} -> b \in \{f a} => [| a Haeq ].
  by apply.
suff: b \in MapAsCorr f a => [ H |].
  rewrite /MapAsCorr /In in H.
  by rewrite H.
rewrite -[MapAsCorr f]invcorr_twice.
by rewrite Heq.
Qed.

Lemma corr_eq A B (f g: A ->c B):
  (forall a b, b \in f a <-> b \in g a) -> f = g.
Proof.
move=> H.
apply functional_extensionality => a.
apply functional_extensionality => b.
apply propositional_extensionality.
by suff: b \in f a <-> b \in g a.
Qed.

(* S4 定理4 前半 *)
Theorem invcorr_is_map_iff_bijective A B (f: A -> B):
  Bijective f <-> (forall gcorr: B ->c A, gcorr = InvCorr (MapAsCorr f) -> exists g, gcorr = MapAsCorr g).
Proof.
split => [| Hg ].
- case => Hsur Hinj g Hgeq.
  have: forall b : B, {x : A | f x = b} => [ b | Hsig ].
    move: (iffLR (surjective_valuerange _) Hsur b) => H1.
    move: (iffLR (injective_exists_unique _) Hinj b H1) => H2.
    apply (constructive_definite_description _ H2).
  exists (fun b => get_value (Hsig b)).
  subst.
  apply corr_eq => b a.
  split => [ Hinv | Hmap ].
  + rewrite /InvCorr /MapAsCorr /In in Hinv.
    rewrite /MapAsCorr /In.
    suff: uniqueness (fun a: A => f a = b).
      move: (get_proof (Hsig b)) => H.
      by apply.
    apply injective_uniqueness => //.
    rewrite valuerange_map_as_corr.
    by exists a.
  + rewrite /MapAsCorr /In in Hmap.
    rewrite /InvCorr /MapAsCorr /In.
    rewrite Hmap.
    by rewrite (get_proof (Hsig b)).
- move: (Hg (InvCorr (MapAsCorr f))).
  case => // g Hinveq.
  move: (invcorr_map_as_corr Hinveq) => Hforall.
  move: (invcorr_map_as_corr' Hinveq) => Hforall'.
  split.
  + rewrite surjective_exists => b.
    by exists (g b).
  + rewrite injective_exists_unique => b Hval.
    exists (g b).
    split => // a Haeq.
    by rewrite -Haeq.
Qed.

(* S4 定理4 後半 *)
Theorem invcorr_bijective A B P (f: A -> B | Bijective f /\ P f):
  {g: B -> A | Bijective g /\ MapAsCorr g = InvCorr (MapAsCorr (get_value f))}.
Proof.
apply constructive_indefinite_description.
case (get_proof f) => Hbij _.
rewrite invcorr_is_map_iff_bijective in Hbij.
case (Hbij (InvCorr (MapAsCorr (get_value f))) eq_refl) => g Hg.
exists g.
split => //.
rewrite invcorr_is_map_iff_bijective => fcorr Hf.
exists (get_value f).
by rewrite -Hg invcorr_twice in Hf.
Qed.

(* InvMapの設計については
https://github.com/itleigns/CoqLibrary/blob/de210b755ab010e835e3777b9b47351972bbb577/Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn1.v#L1268
を参考にした *)

Definition InvMap A B {P} (f: A -> B | Bijective f /\ P f):
  {g: B -> A | Bijective g /\ MapAsCorr g = InvCorr (MapAsCorr (get_value f))}
  := (invcorr_bijective _ f).
Notation "f ^-1" := (InvMap f) (at level 30).

Theorem invmap_eq A B {P} (f: A -> B | Bijective f /\ P f):
  forall a b, get_value (f^-1) b = a <-> (get_value f) a = b.
Proof.
move=> a b.
suff: InvCorr (MapAsCorr (get_value f)) = MapAsCorr (get_value (InvMap f)) => [ H |].
  split => Heq;
  rewrite -Heq;
  by [ apply invcorr_map_as_corr' | apply invcorr_map_as_corr ].
by case (get_proof (invcorr_bijective _ f)).
Qed.

Lemma invmap_bijective A B {P} (f: A -> B | Bijective f /\ P f):
  Bijective (get_value (f^-1)).
Proof.
rewrite /InvMap.
move: (invcorr_bijective _ f) => g.
move: (get_proof g).
by case.
Qed.


Definition Composite A B C (f: A -> B) (g: B -> C): (A -> C) := fun a => g (f a).
Notation "f \comp g" := (Composite g f) (at level 50).

(* S4 定理5a *)
Theorem composite_surjective A B C (f: A -> B) (g: B -> C):
  Surjective f -> Surjective g -> Surjective (g \comp f).
Proof.
rewrite !surjective_exists => Hf Hg c.
case (Hg c) => b Heqc.
case (Hf b) => a Heqb.
exists a.
rewrite /Composite.
by rewrite Heqb.
Qed.

(* S4 定理5b *)
Theorem composite_injective A B C (f: A -> B) (g: B -> C):
  Injective f -> Injective g -> Injective (g \comp f).
Proof.
move=> Hf Hg.
rewrite injective_exists_unique => c Hc.
rewrite valuerange_map_as_corr in Hc.
case Hc => a Ha.
exists a.
split => // a' Ha'.
apply /Hf /Hg.
rewrite /Composite in Ha Ha'.
by rewrite Ha Ha'.
Qed.

(* S4 定理5c *)
Theorem composite_bijective A B C (f: A -> B) (g: B -> C):
  Bijective f -> Bijective g -> Bijective (g \comp f).
Proof.
rewrite /Bijective.
case => Hsurf Hinf.
case => Hsurg Hing.
split.
- by apply composite_surjective.
- by apply composite_injective.
Qed.

(* S4 定理6(1) *)
Theorem composite_assoc A B C D (f: A -> B) (g: B -> C) (h: C -> D):
  (h \comp g) \comp f = h \comp (g \comp f).
Proof. by []. Qed.

(* S4 定理6(2)-1 *)
Theorem composite_identity A B (f: A -> B):
  f \comp \I A = f.
Proof. by []. Qed.

(* S4 定理6(2)-2 *)
Theorem identity_composite A B (f: A -> B):
  \I B \comp f = f.
Proof. by []. Qed.

(* S4 定理6(3)-1 *)
Theorem invmap_composite_identity A B {P} (f: A -> B | Bijective f /\ P f):
  get_value (f^-1) \comp get_value f = \I A.
Proof.
rewrite /Composite /Identity.
apply functional_extensionality => a.
by rewrite invmap_eq.
Qed.

(* S4 定理6(3)-2 *)
Theorem composite_invmap_identity A B P (f: A -> B | Bijective f /\ P f):
  get_value f \comp get_value (f^-1) = \I B.
Proof.
rewrite /Composite /Identity.
apply functional_extensionality => b.
by rewrite -invmap_eq.
Qed.

(* 写像の拡大と縮小についてはいまいちイメージがわかないので後回し *)

(* 特徴関数(CharacteristicFunction)あるいは定義関数(IndicatorFunction)、略してCharにする *)
Definition Char X (A: Ensemble X) (x: X): nat :=
  match excluded_middle_informative (x \in A) with
  | left a => 1
  | right b => 0
  end.

Lemma in_char X (A: Ensemble X) (a: X):
  a \in A <-> Char A a = 1.
Proof.
split;
  rewrite /Char;
  by case excluded_middle_informative.
Qed.

Lemma not_in_char X (A: Ensemble X) (a: X):
  a \notin A <-> Char A a = 0.
Proof.
split;
  rewrite /Char;
  by case excluded_middle_informative.
Qed.

Fact char_fullset X (x: X):
  x \in FullSet -> Char FullSet x = 1.
Proof. by rewrite -in_char. Qed.

Fact char_emptyset X (x: X):
  x \in FullSet -> Char EmptySet x = 0.
Proof. by rewrite -not_in_char not_emptyset. Qed.

Fact char_neq X (A A': Ensemble X):
  A \in PowerSet FullSet -> A' \in PowerSet FullSet -> A <> A'
 -> Char A <> Char A'.
Proof.
move=> HP HP' Hneq Hceq.
apply Hneq.
rewrite -eq_iff => x.
split;
  move=> H;
  rewrite in_char in H;
  [ rewrite Hceq in H | rewrite -Hceq in H ];
  by rewrite -in_char in H.
Qed.

Fact char_eq_func X (f: X -> nat):
  (forall x, f x = 0 \/ f x = 1) ->
  forall A: Ensemble X, A = (fun x => f x = 1) -> Char A = f.
Proof.
move=> Hfor A HAeq.
apply functional_extensionality => x.
case (Hfor x) => H;
  rewrite H;
  [ rewrite -not_in_char | rewrite -in_char ];
  rewrite HAeq.
- rewrite /In => H1.
  by rewrite H1 in H.
- by rewrite /In.
Qed.

(* S4 問題3-1 *)
Theorem invimage_image_injective A B (f: A -> B):
  Injective f -> forall P, P = InvImage f (Image f P).
Proof.
move=> Hinj P.
apply eq_split.
- by apply invimage_image.
- move=> a.
  rewrite {1}/In /InvImage.
  case => a'.
  case => Ha' Heqf.
  suff: a = a' => [ Heq |].
    by rewrite Heq.
  by apply Hinj.
Qed.

(* S4 問題3-2 *)
Theorem image_invimage_surjective A B (f: A -> B):
  Surjective f -> forall Q, Image f (InvImage f Q) = Q.
Proof.
move=> Hsur Q.
apply eq_split.
- by apply image_invimage.
- move=> b Hb.
  rewrite surjective_exists in Hsur.
  case (Hsur b) => a Heq.
  exists a.
  split => //.
  by rewrite -Heq in Hb.
Qed.

(* S4 問題4 *)
Theorem image_cap_injective A B (f: A -> B) (P1 P2: Ensemble A):
  Injective f -> Image f (P1 \cap P2) = Image f P1 \cap Image f P2.
Proof.
move=> Hinj.
apply eq_split.
- by apply image_cap.
- move=> b_.
  case => b HP1 HP2.
  rewrite /In /Image.
  case HP1 => a1.
  case => Ha1 Heq1.
  case HP2 => a2.
  case => Ha2 Heq2.
  suff: a1 = a2 => [ Heq |].
    exists a1.
    split => //.
    split => //.
    by rewrite Heq.
  apply Hinj.
  by rewrite Heq1 Heq2.
Qed.

Lemma func_eq_invmap A B {Q} (f: A -> B) (g: A -> B | Bijective g /\ Q g):
  f = get_value g <-> f \comp get_value (g^-1) = \I B.
Proof.
split => [ Heq | Hi ].
- rewrite Heq.
  by apply composite_invmap_identity.
- suff: f = \I B \comp get_value g => //.
  rewrite -Hi.
  rewrite composite_assoc.
  by rewrite invmap_composite_identity.
Qed.

Lemma invmap_twice A B {P} (f: A -> B | Bijective f /\ P f):
  get_value (f ^-1 ^-1) = get_value f.
Proof.
move: (invmap_bijective f) => Hg.
apply functional_extensionality => a.
rewrite invmap_eq.
by rewrite invmap_eq.
Qed.

Lemma composite_sig A B C {P Q} (f: A -> B | Bijective f /\ P f) (g: B -> C | Bijective g /\ Q g):
  {c: A -> C | Bijective c /\ get_value g \comp get_value f = c}.
Proof.
apply constructive_indefinite_description.
exists (get_value g \comp get_value f).
split => //.
- apply composite_bijective.
  + by case (get_proof f).
  + by case (get_proof g).
Qed.

Lemma get_composite_sig_value A B C {P Q} (f: A -> B | Bijective f /\ P f) (g: B -> C | Bijective g /\ Q g):
  get_value (composite_sig f g) = get_value g \comp get_value f.
Proof.
case (get_proof (composite_sig f g)) => _ Heq.
fold get_value in Heq.
by rewrite -Heq.
Qed.

(* S4 問題8 *)
(* (f . g)^-1 = f^-1 . g^-1 *)
Theorem inv_composite_bijective A B C {P Q} (f: A -> B | Bijective f /\ P f) (g: B -> C | Bijective g /\ Q g):
  get_value ((composite_sig f g)^-1) = get_value (f^-1) \comp get_value (g^-1).
Proof.
symmetry.
rewrite func_eq_invmap.
rewrite invmap_twice.
rewrite composite_assoc.
rewrite get_composite_sig_value.
rewrite -[get_value (InvMap g) \comp _]composite_assoc.
rewrite invmap_composite_identity.
rewrite identity_composite.
by rewrite invmap_composite_identity.
Qed.

(* S4 問題9(a) *)
Theorem composite_image A B C (f: A -> B) (g: B -> C) (P: Ensemble A):
  Image (g \comp f) P = Image g (Image f P).
Proof.
apply eq_split => [ c H | c H ].
- case H => a.
  case => H1 H2.
  exists (f a).
  split => //.
  by exists a.
- case H => b.
  case => H1 H2.
  case H1 => a.
  case => H3 H4.
  exists a.
  split => //.
  rewrite /Composite.
  by rewrite H4.
Qed.

(* S4 問題9(b) *)
(* (f . g)^-1 (R) = f^-1 (g^-1 (R)) *)
Theorem composite_inv_image A B C {P Q} (f: A -> B | Bijective f /\ P f) (g: B -> C | Bijective g /\ Q g) (R: Ensemble C):
  Image (get_value ((composite_sig f g)^-1)) R = Image (get_value (f^-1)) (Image (get_value (g^-1)) R).
Proof.
rewrite inv_composite_bijective.
by rewrite composite_image.
Qed.

(* S4 問題10(a) *)
Theorem surjective_composite_surjective A B C (f: A -> B) (g: B -> C):
  Surjective (g \comp f) -> Surjective g.
Proof.
move=> Hsur.
rewrite surjective_exists in Hsur.
rewrite surjective_exists => b.
case (Hsur b) => a Heq.
exists (f a).
by rewrite -Heq.
Qed.

(* S4 問題10(b) *)
Theorem injective_composite_injective A B C (f: A -> B) (g: B -> C):
  Injective (g \comp f) -> Injective f.
Proof.
move=> Hinj.
move=> a1 a2 Heq.
apply Hinj.
rewrite /Composite.
by rewrite Heq.
Qed.

Lemma comp_eq_iff A B C (f: A -> B) (g: B -> C) (h: A -> C):
  g \comp f = h
  -> forall a c, g (f a) = c <-> h a = c.
Proof.
move=> Heq a c.
suff: (g \comp f) a = c <-> h a = c => //.
by rewrite Heq.
Qed.

(* S4 問題11 *)
Theorem surjective_composite_eq A B C (f: A -> B) (Hf: Surjective f) (g g': B -> C):
  g \comp f = g' \comp f -> g = g'.
Proof.
move=> Heq.
rewrite surjective_exists in Hf.
apply functional_extensionality => b.
case (Hf b) => a H.
rewrite -H.
by rewrite (comp_eq_iff Heq).
Qed.

(* S4 問題12 *)
Theorem injective_composite_eq A B C (f f': A -> B) (g: B -> C) (Hg: Injective g):
  g \comp f = g \comp f' -> f = f'.
Proof.
move=> Heq.
apply functional_extensionality => a.
apply Hg.
by rewrite (comp_eq_iff Heq).
Qed.

(* S4 問題13(a) *)
Theorem composite_surjective_to_surjective A B C (f: A -> B) (g: B -> C):
  Surjective (g \comp f) -> Injective g -> Surjective f.
Proof.
move=> Hsur Hinj.
rewrite surjective_exists => b.
rewrite surjective_exists in Hsur.
case (Hsur (g b)) => a Ha.
exists a.
apply Hinj.
by rewrite -Ha.
Qed.

(* S4 問題13(b) *)
Theorem composite_injective_to_injective A B C (f: A -> B) (g: B -> C):
  Injective (g \comp f) -> Surjective f -> Injective g.
Proof.
move=> Hinj Hsur b1 b2 Heq.
rewrite surjective_exists in Hsur.
case (Hsur b1) => a1 Ha1.
case (Hsur b2) => a2 Ha2.
subst.
move: (Hinj _ _ Heq) => Ha.
by subst.
Qed.

Section Problem14.

Variable A B: Type.
Variable f: A -> B.
Variable g g': B -> A.

Hypothesis H1: g \comp f = \I A.
Hypothesis H2: f \comp g' = \I B.

(* S4 問題14-1 *)
Theorem identity_to_bijective:
  Bijective f.
Proof.
split.
- rewrite surjective_exists => b.
  exists (g b).
  suff: f \comp g = \I B => [ H3 |].
    by rewrite (comp_eq_iff H3).
  

  admit.
- move=> a1 a2 Ha.
  have: g (f a1) = g (f a2) => [| H ].
    by rewrite Ha.
  rewrite (comp_eq_iff H1) in H.
  symmetry in H.
  by rewrite (comp_eq_iff H1) in H.
Admitted.

(* S4 問題14-2 *)
Theorem identity_to_eq:
  g = g'.
Admitted.

Lemma bijective_sig (H: Bijective f): {f: A -> B | Bijective f /\ (fun _ => True) f}.
Proof.
apply constructive_indefinite_description.
exists f.
by split.
Qed.

(* S4 問題14-3 *)
Theorem identity_to_invmap:
  g = get_value ((bijective_sig identity_to_bijective)^-1).
Admitted.

End Problem14.

Lemma char_return_or X (A: Ensemble X) x:
  Char A x = 1 \/ Char A x = 0.
Proof.
rewrite /Char.
case (excluded_middle_informative) => H;
  by [left | right].
Qed.

Section Problem15.

Lemma char_cap_notin X (A B: Ensemble X) x:
  Char A x = 0
  -> Char (A \cap B) x = Char A x * Char B x.
Proof.
move=> Ha.
rewrite Ha.
case (char_return_or B x) => Hb;
  rewrite Hb.
- suff: Char (A \cap B) x = 0 => [ H |].
    by [ rewrite H | ].
  rewrite -not_in_char -cap_and => Hab.
  rewrite -not_in_char -in_char in Ha Hb.
  by case Hab.
- rewrite -2!not_in_char in Ha Hb.
  rewrite -not_in_char -cap_and => Hab.
  apply Ha.
  by case Hab.
Qed.

Lemma sub_not X (A B: Ensemble X):
  (A - B)^c = A^c \cup (A \cap B).
Proof.
rewrite -eq_iff => x.
rewrite compset_in sub_iff.
rewrite Classical.not_and_or.
rewrite cup_comm cap_cup_distrib.
rewrite compset_cup fullset_cap.
rewrite -cup_or [x \in B \/ _]or_comm.
rewrite -3!compset_in.
by rewrite compset_twice.
Qed.

Open Scope nat_scope.

Lemma char_cup_lemma X (A B: Ensemble X) x:
  x \in A -> x \notin B
  -> Char (A \cup B) x = Char A x + Char B x - Char A x * Char B x.
Proof.
move=> Ha Hb.
have: x \in A \cup B => [| Hcup ].
  by left.
rewrite 2!in_char not_in_char in Ha Hcup Hb.
by rewrite Ha Hb Hcup.
Qed.

Variable X: Type.
Variable A B: Ensemble X.

(* S4 問題15-1 *)
Theorem char_le_subset:
  (forall x, Char A x <= Char B x) <-> A \subset B.
Proof.
split => [ Hle y | Hsubset x ].
- rewrite 2!in_char => Hy.
  move: (Hle y).
  rewrite Hy => Hla.
  case (char_return_or B y) => // Hb.
  rewrite Hb in Hla.
  by move: (PeanoNat.Nat.nle_succ_0 _ Hla).
- case (char_return_or B x) => Hb.
  + rewrite Hb.
    case (char_return_or A x) => H;
      rewrite H;
      by auto.
  + rewrite Hb.
    rewrite -not_in_char in Hb.
    suff: x \notin A.
      rewrite not_in_char => Ha.
      by rewrite Ha.
    move=> Ha.
    apply Hb.
    by apply Hsubset.
Qed.

Variable x: X.

(* S4 問題15(a) *)
Theorem char_cap:
  Char (A \cap B) x = Char A x * Char B x.
Proof.
case (char_return_or A x) => Ha.
case (char_return_or B x) => Hb. (* ここで3パターンに場合分けされる *)
- rewrite Ha Hb.
  suff: Char (A \cap B) x = 1 => //.
  rewrite -in_char.
  rewrite -2!in_char in Ha Hb.
  by split.
- rewrite cap_comm PeanoNat.Nat.mul_comm.
  by apply char_cap_notin.
- by apply char_cap_notin.
Qed.

Open Scope nat_scope.

(* S4 問題15(b) *)
Theorem char_cup:
  Char (A \cup B) x = Char A x + Char B x - Char (A \cap B) x.
Proof.
rewrite char_cap.
case (char_return_or A x) => Ha;
case (char_return_or B x) => Hb. (* ここで4パターンに場合分けされる *)
- suff: Char (A \cup B) x = 1 => [ Hcup |].
    by rewrite Ha Hb Hcup.
  rewrite -in_char.
  rewrite -in_char in Ha.
  by left.
- rewrite -in_char in Ha.
  rewrite -not_in_char in Hb.
  by apply char_cup_lemma.
- rewrite -not_in_char in Ha.
  rewrite -in_char in Hb.
  rewrite cup_comm.
  rewrite PeanoNat.Nat.mul_comm.
  rewrite PeanoNat.Nat.add_comm.
  by apply char_cup_lemma.
- suff: Char (A \cup B) x = 0 => [ Hcup |].
    by rewrite Ha Hb Hcup.
  rewrite -not_in_char => Hcup.
  rewrite -2!not_in_char in Ha Hb.
  move: Ha Hb.
  by case Hcup.
Qed.

(* S4 問題15(c) *)
Theorem char_comp:
  Char (A^c) x = 1 - Char A x.
Proof.
case (char_return_or A x) => Ha.
- suff: x \notin A^c => [ Hcomp |].
    rewrite not_in_char in Hcomp.
    by rewrite Ha Hcomp.
  rewrite -in_char in Ha.
  by rewrite compset_in.
- suff: x \in A^c => [ Hcomp |].
    rewrite in_char in Hcomp.
    by rewrite Ha Hcomp.
  rewrite -not_in_char in Ha.
  by rewrite compset_in.
Qed.

(* S4 問題15(d) *)
Theorem char_sub:
  Char (Sub A B) x = Char A x * (1 - Char B x).
Proof.
case (char_return_or A x) => Ha.
- case (char_return_or B x) => Hb.
  + suff: x \notin (Sub A B) => [ Hsub |].
      rewrite not_in_char in Hsub.
      by rewrite Ha Hb Hsub.
    rewrite -2!in_char in Ha Hb.
    rewrite -compset_in sub_not.
    by right.
  + suff: x \in (Sub A B) => [ Hsub |].
      rewrite in_char in Hsub.
      by rewrite Ha Hb Hsub.
    by rewrite -in_char -not_in_char in Ha Hb.
- suff: x \notin (Sub A B) => [ Hsub |].
    rewrite not_in_char in Hsub.
    by rewrite Ha Hsub.
  rewrite -not_in_char in Ha.
  rewrite -compset_in sub_not.
  by left.
Qed.


End Problem15.

End Section4.

End Ensembles.
