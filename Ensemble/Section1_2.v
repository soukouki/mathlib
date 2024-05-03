(* 集合・位相入門(松坂)1 をCoqで証明しつつ読んでいく *)

Set Implicit Arguments.

From mathcomp Require Import ssreflect.

Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Arith.PeanoNat.

Add LoadPath "." as Local.
Require Import Local.Classical.
Require Import Local.Ensemble.Section1_1.
Open Scope ensemble_scope.

Module Ensemble.

Import Section1_1.Ensemble.

Section Section1_2.

Variable T: Type.

Inductive Cup A B: Ensemble T :=
  | Cup_introl: forall x: T, x ∈ A -> x ∈ Cup A B
  | Cup_intror: forall x: T, x ∈ B -> x ∈ Cup A B.
Notation "A ∪ B" := (Cup A B) (at level 50).

(* (2.2.1) *)
Theorem subset_cup_l A B: A ⊂ A ∪ B.
Proof. by left. Qed.

(* (2.2.2) *)
Theorem subset_cup_r A B: B ⊂ A ∪ B.
Proof. by right. Qed.

Lemma cup_or A B x: x ∈ A \/ x ∈ B <-> x ∈ A ∪ B.
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
Theorem subsets_cup A B C: A ⊂ C -> B ⊂ C -> A ∪ B ⊂ C.
Proof.
move=> HA_subset_C HB_subset_C.
rewrite /Subset => x1.
case => x2.
- by apply HA_subset_C.
- by apply HB_subset_C.
Qed.

(* (2.4) *)
Theorem cup_diag A: A ∪ A = A.
Proof.
apply eq_split.
- by apply subsets_cup.
- by apply subset_cup_l.
Qed.

(* (2.5) *)
Theorem cup_comm A B: A ∪ B = B ∪ A.
Proof.
apply eq_split => x;
  rewrite -2!cup_or;
  by rewrite or_comm.
Qed.

(* (2.6) *)
Theorem cup_assoc A B C: (A ∪ B) ∪ C = A ∪ (B ∪ C).
Proof.
apply eq_split => x;
  rewrite -4!cup_or;
  by rewrite or_assoc.
Qed.

(* (2.7) *)
Theorem subset_cup_eq A B: A ⊂ B <-> A ∪ B = B.
Proof.
split.
- move=> HA_subset_B.
  apply eq_split.
  + by apply subsets_cup.
  + by apply subset_cup_r.
- move=> H; rewrite -H.
  by apply subset_cup_l.
Qed.

(* (2.8) *)
Theorem subset_cups_subset A B C: A ⊂ B -> A ∪ C ⊂ B ∪ C.
Proof.
move=> HA_subset_B.
apply subsets_cup.
- left.
  by apply HA_subset_B.
- by apply subset_cup_r.
Qed.

(* (2.9) *)
Theorem emptyset_cup A: ∅ ∪ A = A.
Proof. by apply subset_cup_eq. Qed.


Inductive Cap A B: Ensemble T :=
  Cap_intro: forall x: T, x ∈ A -> x ∈ B -> x ∈ (Cap A B).
Notation "A ∩ B" := (Cap A B) (at level 50).

(* (2.2.1)'
   本ではsupsetを使っているが、今回はすべてsubsetで統一する *)
Theorem cap_subset_l A B: A ∩ B ⊂ A.
Proof.
move=> x.
by case.
Qed.

(* (2.2.2)' *)
Theorem cap_subset_r A B: A ∩ B ⊂ B.
Proof.
move=> x.
by case.
Qed.

Lemma cap_and A B x: x ∈ A /\ x ∈ B <-> x ∈ A ∩ B.
Proof.
split;
  by case.
Qed.

(* (2.3)' *)
Theorem subsets_cap A B C: C ⊂ A -> C ⊂ B -> C ⊂ A ∩ B.
Proof.
move=> HC_subset_A HC_subset_B x HC.
split.
- by apply HC_subset_A.
- by apply HC_subset_B.
Qed.

(* (2.4)' *)
Theorem cap_diag A: A ∩ A = A.
Proof.
apply eq_split => x;
  rewrite -cap_and.
- by case.
- by split.
Qed.

(* (2.5)' *)
Theorem cap_comm A B: A ∩ B = B ∩ A.
Proof.
apply eq_split => x;
  rewrite -2!cap_and.
- by rewrite and_comm.
- by case.
Qed.

(* (2.6)' *)
Theorem cap_assoc A B C: (A ∩ B) ∩ C = A ∩ (B ∩ C).
Proof.
apply eq_split => x;
  rewrite -4!cap_and;
  by rewrite and_assoc.
Qed.

(* (2.7)' *)
Theorem subset_cap_eq A B: A ⊂ B <-> A ∩ B = A.
Proof.
split.
- move=> HA_subset_B.
  apply eq_split.
  + by apply cap_subset_l.
  + by apply subsets_cap.
- move=> H; rewrite -H.
  by apply cap_subset_r.
Qed.

(* (2.8)' *)
Theorem subset_caps_subset A B C: A ⊂ B -> A ∩ C ⊂ B ∩ C.
Proof.
move=> HA_subset_B.
apply subsets_cap => x1.
- case => x2 HA HC.
  by apply HA_subset_B.
- by apply cap_subset_r.
Qed.

(* (2.9)' *)
Theorem emptyset_cap A: ∅ ∩ A = ∅.
Proof. by apply subset_cap_eq. Qed.

(* (2.10) *)
Theorem cup_cap_distrib A B C: (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C).
Proof.
apply eq_split => x1.
- case => x2.
  by case => x3 H HC;
    [left | right];
    split.
- case => x2;
    case => x3;
    [move=> HA | move=> HB];
    split => //;
    by [left | right].
Qed.

(* (2.11) *)
Theorem cap_cup_distrib A B C: (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C).
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
      by split.
    * by right.
  + by right.
Qed.

(* (2.11) *)
Theorem cup_absorption A B: (A ∪ B) ∩ A = A.
Proof.
rewrite cap_comm.
apply subset_cap_eq.
by apply subset_cup_l.
Qed.

(* (2.11)' *)
Theorem cap_absorption A B: (A ∩ B) ∪ A = A.
Proof.
apply subset_cup_eq.
by apply cap_subset_l.
Qed.


Inductive Sub A B: Ensemble T :=
  | Sub_intro: forall x: T, x ∈ A -> x ∉ B -> x ∈ Sub A B.
Notation "A - B" := (Sub A B). (* at level 50 *)

Lemma sub_iff A B x: x ∈ A - B <-> x ∈ A /\ x ∉ B.
Proof.
split.
- case => x1.
  by split.
- case.
  by apply Sub_intro.
Qed.

Lemma sub_emptyset A: A - ∅ = A.
Proof.
apply eq_split => x.
- by case.
- by split.
Qed.

Lemma emptyset_sub A: ∅ - A = ∅.
Proof.
apply eq_split => x //.
by case.
Qed.

Lemma sub_sim_emptyset A: A - A = ∅.
Proof.
apply eq_split => x //.
rewrite sub_iff.
by case.
Qed.


Inductive FullSet: Ensemble T :=
  | FullSet_intro: forall x: T, x ∈ FullSet.

Lemma fullset_cap A: FullSet ∩ A = A.
Proof. by rewrite cap_comm -subset_cap_eq. Qed.

Lemma fullset_cup A: FullSet ∪ A = FullSet.
Proof. by rewrite cup_comm -subset_cup_eq. Qed.

Lemma eq_fullset A: (forall x, x ∈ A) <-> A = FullSet.
Proof.
split.
- move=> H.
  apply eq_subset.
  by split.
- move=> H x.
  by rewrite H.
Qed.

Lemma not_emptyset x: x ∉ ∅ <-> x ∈ FullSet.
Proof.
split => // Hf.
case.
Qed.

Inductive ComplementarySet (A: Ensemble T): Ensemble T :=
  | ComplementarySet_intro: forall x, x ∈ FullSet - A -> x ∈ ComplementarySet A.
Notation "A ^ 'c'" := (ComplementarySet A) (at level 30).

Lemma compset_in A x: x ∈ A^c <-> x ∉ A.
Proof.
split.
- move=> H1.
  case H1 => x1 H2.
  by case H2.
- move=> H1.
  split.
  by split.
Qed.

(* (2.12.1) *)
Theorem compset_cup A: A ∪ A^c = FullSet.
Proof.
apply eq_split => x // _.
rewrite -cup_or.
rewrite compset_in.
by apply classic. (* ここで古典論理を使い始めた *)
Qed.

(* (2.12.2) *)
Theorem compset_cap A: A ∩ A^c = EmptySet.
Proof.
apply eq_split => x1 //.
case => x2.
by rewrite compset_in.
Qed.

(* (2.13) *)
Theorem compset_twice A: A^c^c = A.
Proof.
apply eq_split => x;
  rewrite 2!compset_in.
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
Theorem compset_subset A B: A ⊂ B <-> B^c ⊂ A^c.
Proof.
split.
- move=> HA_subset_B x.
  rewrite 2!compset_in => HB HA.
  by apply /HB /HA_subset_B.
- move=> HB_subset_A.
  rewrite -[A]compset_twice -[B]compset_twice => x.
  rewrite 2!(compset_in (_^c) _) => HA HB.
  by apply /HA /HB_subset_A.
Qed.


(* (2.16) *)
Theorem de_morgan_cup A B: (A ∪ B)^c = A^c ∩ B^c.
Proof.
apply eq_split => x1.
- rewrite compset_in => HA_cup_B.
  split;
    rewrite compset_in => H;
    apply HA_cup_B;
    by [left | right].
- case => x2.
  rewrite 3!compset_in => HA HB HAB.
  move: HAB HA HB.
  by case => x3.
Qed.

(* (2.16)' *)
Theorem de_morgan_cap A B: (A ∩ B)^c = A^c ∪ B^c.
Proof.
apply eq_split => x1.
- rewrite compset_in => HA_cap_B.
  rewrite -cup_or 2!compset_in.
  apply not_and_or => HA_and_B.
  apply HA_cap_B.
  by case HA_and_B.
- rewrite compset_in.
  case => x2;
    rewrite compset_in => H1 H2;
    apply H1;
    by case H2.
Qed.

Lemma sub_fullset A: A - FullSet = ∅.
Proof.
apply ensemble_extensionality => x.
rewrite sub_iff.
rewrite -compset_in compset_fullset.
rewrite cap_and.
by rewrite cap_comm emptyset_cap.
Qed.

Lemma fullset_sub A: FullSet - A = A^c.
Proof.
apply ensemble_extensionality => x.
rewrite sub_iff.
rewrite -compset_in.
rewrite cap_and.
by rewrite fullset_cap.
Qed.

Lemma sub_compset A: A - A^c = A.
Proof.
apply ensemble_extensionality => x.
rewrite sub_iff.
rewrite -compset_in.
rewrite compset_twice.
split => //.
by case.
Qed.

Definition FamilyEnsemble T := (Ensemble (Ensemble T)).
Implicit Types AA BB: FamilyEnsemble T.

Definition PowerSet {T} (X: Ensemble T): FamilyEnsemble T := fun A: Ensemble T => A ⊂ X.

(* p.18の定理を証明するには、個数を定義する必要がありややこしいので、練習問題の後で解く *)

(* ドイツ文字の変数は、AA, BBのように2文字つなげて区別することにする *)
(* ΛはL、λはlと略記する *)
(* ここではp.19(S2 F)の定義ではなく、より一般的なp.45(S5 C)を参考にした定義をする *)
Definition BigCup (L: Type) (f: L -> Ensemble T) (lam: Ensemble L): Ensemble T :=
  fun x => exists l, l ∈ lam /\ x ∈ f l.
Notation "\bigcup AA" := (BigCup (fun A => A) AA) (at level 50).

Definition BigCap (L: Type) (f: L -> Ensemble T) (lam: Ensemble L): Ensemble T :=
  fun x => forall l, l ∈ lam -> x ∈ f l.
Notation "\bigcap AA" := (BigCap (fun A => A) AA) (at level 50).

(* p.19の定義と等しいことの確認 *)
Fact bigcup_definition_eq AA: \bigcup AA = (fun x => exists A, A ∈ AA /\ x ∈ A).
Proof. by []. Qed.
Fact bigcap_definition_eq AA: \bigcap AA = (fun x => forall A, A ∈ AA -> x ∈ A).
Proof. by []. Qed.

(* (2.17) *)
Theorem bigcup_in AA A: A ∈ AA -> A ⊂ \bigcup AA.
Proof.
move=> HA_in_AA.
by exists A.
Qed.

(* (2.18) *)
Theorem bigcup_subset AA C: (forall A, A ∈ AA -> A ⊂ C) -> \bigcup AA ⊂ C.
Proof.
move=> H1 x.
case => A H2.
case H2 => H3 H4.
move: (H1 A H3).
by apply.
Qed.

(* (2.17)' *)
Theorem bigcap_in AA A: A ∈ AA -> \bigcap AA ⊂ A.
Proof.
move=> H1 x.
by apply.
Qed.

(* (2.18)' *)
Theorem bigcap_subset AA C: (forall A, A ∈ AA -> C ⊂ A) -> C ⊂ \bigcap AA.
Proof.
move=> H1 x H2 A H3.
apply H1 in H3.
by apply H3.
Qed.


(* S2 問題1a *)
Theorem cup_cap_cup_compset A B: (A ∪ B) ∩ (A ∪ B^c) = A.
Proof.
rewrite cup_cap_distrib.
rewrite cap_comm cup_absorption.
rewrite cap_comm cup_cap_distrib.
rewrite [_^c ∩ _]cap_comm compset_cap.
rewrite [_ ∪ ∅]cup_comm emptyset_cup.
by rewrite cup_comm cap_absorption.
Qed.

(* S2 問題1b *)
Theorem cup_cap_compset_cup_cap_cup_compset A B: (A ∪ B) ∩ (A^c ∪ B) ∩ (A ∪ B^c) = A ∩ B.
Proof.
rewrite cap_assoc [(A^c ∪ B) ∩ _]cap_comm -cap_assoc.
rewrite cup_cap_cup_compset.
rewrite cap_comm cup_cap_distrib.
rewrite cap_comm compset_cap.
by rewrite emptyset_cup cap_comm.
Qed.

Lemma emptyset_not_in A: A = ∅ <-> forall x: T, x ∉ A.
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
Theorem cap_eq_emptyset A B: A ∩ B = ∅ <-> A ⊂ B^c.
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
  move: (HA_subset_Bc _ HA).
  by rewrite compset_in.
Qed.

(* S2 問題3a 本ではA=B=C=Dと4つの式を等号でつないでいるが、今回はA=D, A=B, A=Cの3つの定理として順番に証明していく *)

(* S2 問題3a-1 (A=D) *)
Theorem sub_cap_compset A B: A - B = A ∩ B^c.
Proof.
apply ensemble_extensionality => x.
by rewrite sub_iff -cap_and -compset_in.
Qed.

(* S2 問題3a-2 (A=B) *)
Theorem sub_cup_sub A B: A - B = (A ∪ B) - B.
Proof.
apply ensemble_extensionality => x.
rewrite 2!sub_cap_compset.
rewrite cup_cap_distrib.
rewrite compset_cap.
by rewrite cup_comm emptyset_cup.
Qed.

(* S2 問題3a-3 (A=C) *)
Theorem sub_cap_sub A B: A - B = A - (A ∩ B).
Proof.
rewrite 2!sub_cap_compset.
rewrite de_morgan_cap.
rewrite [A ∩ (_ ∪ _)]cap_comm cup_cap_distrib.
rewrite [A^c ∩ A]cap_comm compset_cap emptyset_cup.
by rewrite cap_comm.
Qed.

(* S2 問題3b *)
Theorem sub_cap_empty A B: A - B = A <-> A ∩ B = ∅.
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
Theorem sub_eq_emptyset A B: A - B = ∅ <-> A ⊂ B.
Proof.
rewrite sub_cap_compset.
rewrite cap_eq_emptyset.
by rewrite compset_twice.
Qed.

(* S2 問題4a *)
Theorem sub_cup A B C: A - (B ∪ C) = (A - B) ∩ (A - C).
Proof.
rewrite sub_cap_compset.
rewrite de_morgan_cup.
rewrite -{1}[A]cap_diag.
rewrite cap_assoc.
rewrite [A ∩ (B^c ∩ C^c)]cap_comm.
rewrite cap_assoc.
rewrite -[A ∩ _]cap_assoc.
rewrite [C^c ∩ A]cap_comm.
by rewrite -2!sub_cap_compset.
Qed.

(* S2 問題4b *)
Theorem sub_cap A B C: A - (B ∩ C) = (A - B) ∪ (A - C).
Proof.
rewrite sub_cap_compset.
rewrite de_morgan_cap.
rewrite cap_comm.
rewrite cup_cap_distrib.
rewrite 2![_ ∩ A]cap_comm.
by rewrite -2!sub_cap_compset.
Qed.

(* S2 問題4c *)
Theorem cup_sub A B C: (A ∪ B) - C = (A - C) ∪ (B - C).
Proof.
rewrite sub_cap_compset.
rewrite cup_cap_distrib.
by rewrite -2!sub_cap_compset.
Qed.

(* S2 問題4d *)
Theorem cap_sub A B C: (A ∩ B) - C = (A - C) ∩ (B - C).
Proof.
rewrite sub_cap_compset.
rewrite -[C^c]cap_diag.
rewrite -cap_assoc.
rewrite [(A ∩ B) ∩ C^c]cap_comm.
rewrite -cap_assoc.
rewrite cap_assoc.
rewrite [C^c ∩ A]cap_comm.
by rewrite -2!sub_cap_compset.
Qed.

(* S2 問題4e *)
Theorem cap_sub' A B C: A ∩ (B - C) = (A ∩ B) - (A ∩ C).
Proof.
rewrite [(A ∩ B) - (A ∩ C)]sub_cap_compset.
rewrite de_morgan_cap.
rewrite [(A ∩ B) ∩ _]cap_comm.
rewrite cup_cap_distrib.
rewrite -cap_assoc.
rewrite [A^c ∩ A]cap_comm.
rewrite compset_cap.
rewrite emptyset_cap emptyset_cup.
rewrite [C^c ∩ _]cap_comm.
rewrite cap_assoc.
by rewrite -sub_cap_compset.
Qed.

(* S2 問題5a *)
Theorem sub_sub_eq_sub_cup A B C: (A - B) - C = A - (B ∪ C).
Proof.
apply ensemble_extensionality => x.
rewrite 2!sub_cap_compset -2!cap_and.
rewrite and_assoc.
rewrite 2!cap_and.
rewrite -de_morgan_cup.
by rewrite -sub_cap_compset.
Qed.

(* S2 問題5b *)
Theorem sub_sub_eq_cup A B C: A - (B - C) = (A - B) ∪ (A ∩ C).
Proof.
rewrite [B-C]sub_cap_compset.
rewrite sub_cap.
rewrite [A - C^c]sub_cap_compset.
by rewrite compset_twice.
Qed.

(* S2 問題6 *)
Theorem cup_cap_eq_cup_cap A C: A ⊂ C -> forall B, A ∪ (B ∩ C) = (A ∪ B) ∩ C.
Proof.
move=> HA_subset_C B.
rewrite cup_comm.
rewrite cap_cup_distrib.
rewrite [B ∪ A]cup_comm [C ∪ A]cup_comm.
have: A ∪ C = C => [| H ].
  by rewrite -subset_cup_eq.
by rewrite H.
Qed.

Definition SymmetricDifference A B := (A - B) ∪ (B - A).
Notation "A △ B" := (SymmetricDifference A B) (at level 50).

(* もう一つの等式 *)
Lemma sym_diff_compset A B: A △ B = (A ∩ B^c) ∪ (A^c ∩ B).
Proof.
rewrite /SymmetricDifference.
rewrite 2!sub_cap_compset.
by rewrite [B ∩ A^c]cap_comm.
Qed.

(* S2 問題7a *)
Theorem sym_diff_comm A B: A △ B = B △ A.
Proof.
rewrite 2!sym_diff_compset.
rewrite [B ∩ A^c]cap_comm [B^c ∩ A]cap_comm.
by rewrite cup_comm.
Qed.

(* S2 問題7b *)
Theorem sym_diff_sub A B: A △ B = (A ∪ B) - (A ∩ B).
Proof.
rewrite /SymmetricDifference.
rewrite cup_sub.
rewrite 2!sub_cap.
rewrite 2!sub_sim_emptyset.
by rewrite [_ ∪ ∅]cup_comm 2!emptyset_cup.
Qed.

Lemma sub_comm A B C: (A - B) - C = (A - C) - B.
Proof.
apply ensemble_extensionality => x.
by rewrite !sub_iff !and_assoc [_ ∉ _ /\ _ ∉ _]and_comm.
Qed.

(* きれいな解法を思いつかなかった *)
Lemma sub_merge A B C: (A - C) - (B - C) = A - B - C.
Proof.
rewrite !sub_cap_compset.
rewrite de_morgan_cap.
rewrite compset_twice.
rewrite 2!cap_assoc.
rewrite [C^c ∩ _]cap_comm.
rewrite cup_cap_distrib.
rewrite compset_cap.
rewrite [_ ∪ ∅]cup_comm emptyset_cup.
by rewrite [B^c ∩ C^c]cap_comm.
Qed.

Lemma sub_sub_cap A B C: A - (B - C) ∩ B = A ∩ B ∩ C.
Proof.
rewrite !sub_cap_compset.
rewrite de_morgan_cap.
rewrite compset_twice.
rewrite cap_assoc.
rewrite cup_cap_distrib.
rewrite [B^c ∩ B]cap_comm compset_cap.
rewrite emptyset_cup.
by rewrite [C ∩ B]cap_comm cap_assoc.
Qed.

Lemma sym_diff_assoc_help A B C:
  (A - ((B - C) ∪ (C - B))) = ((A - B) - C) ∪ (A ∩ B ∩ C).
Proof.
rewrite -sub_sub_eq_sub_cup.
rewrite sub_sub_eq_cup.
rewrite sub_comm.
rewrite sub_merge.
by rewrite sub_sub_cap.
Qed.

(* S2 問題7c *)
Theorem sym_diff_assoc A B C:
  (A △ B) △ C = A △ (B △ C).
Proof.
apply eq_trans_r with
  (y := (A - B - C) ∪ (B - C - A) ∪ (C - A - B) ∪ (A ∩ B ∩ C)).
- rewrite /SymmetricDifference.
  rewrite cup_sub.
  rewrite [B - A - C]sub_comm.
  rewrite sym_diff_assoc_help.
  rewrite [C ∩ A]cap_comm cap_assoc [C ∩ B]cap_comm cap_assoc.
  by rewrite !cup_assoc.
- rewrite /SymmetricDifference.
  rewrite cup_sub.
  rewrite [C - B - A]sub_comm.
  rewrite sym_diff_assoc_help.
  rewrite cup_assoc [(_ ∩ _) ∪ _]cup_comm.
  by rewrite !cup_assoc.
Qed.

(* S2 問題7d *)
Theorem sym_diff_cap_distrib A B C:
  A ∩ (B △ C) = (A ∩ B) △ (A ∩ C).
Proof.
apply eq_trans_r with
  (y := (A ∩ B ∩ C^c) ∪ (A ∩ C ∩ B^c)).
- rewrite sym_diff_compset.
  rewrite cap_comm cup_cap_distrib.
  rewrite [B ∩ C^c]cap_comm [(C^c ∩ B) ∩ A]cap_assoc.
  rewrite [C^c ∩ (B ∩ A)]cap_comm [B ∩ A]cap_comm.
  rewrite [(B^c ∩ C) ∩ A]cap_assoc.
  by rewrite [B^c ∩ (C ∩ A)]cap_comm [C ∩ A]cap_comm.
- rewrite sym_diff_compset.
  rewrite 2!de_morgan_cap.
  rewrite [(A ∩ B) ∩ (A^c ∪ C^c)]cap_comm 2!cup_cap_distrib.
  rewrite -2![A^c ∩ (A ∩ _)]cap_assoc.
  rewrite [A^c ∩ A]cap_comm compset_cap 2!emptyset_cap 2!emptyset_cup.
  by rewrite 2![_^c ∩ _]cap_comm.
Qed.

(* S2 問題8a *)
Theorem sym_diff_emptyset_l A: A △ EmptySet = A.
Proof.
rewrite /SymmetricDifference.
rewrite sub_emptyset emptyset_sub.
by rewrite cup_comm emptyset_cup.
Qed.

(* S2 問題8b *)
Theorem sym_diff_fullset A: A △ FullSet = A^c.
Proof.
rewrite /SymmetricDifference.
rewrite sub_fullset fullset_sub.
by rewrite emptyset_cup.
Qed.

(* S2 問題8c *)
Theorem sym_diff_emptyset_r A: A △ A = EmptySet.
Proof.
rewrite /SymmetricDifference.
rewrite sub_sim_emptyset.
by rewrite cup_diag.
Qed.

(* S2 問題8d *)
Theorem sym_diff_compset_fullset A: A △ A^c = FullSet.
Proof.
rewrite sym_diff_compset.
rewrite compset_twice.
rewrite 2!cap_diag.
by rewrite compset_cup.
Qed.

Lemma sym_diff_not_in_from_in A B x: x ∈ A -> x ∈ B -> x ∉ A △ B.
Proof.
move=> HA HB H.
move: H HA HB.
case => x';
  rewrite sub_iff;
  by case.
Qed.

Lemma sub_sym_diff A1 A2 B1 B2 x:
  x ∈ A1 - B1 ->
  A1 △ A2 = B1 △ B2 ->
  x ∈ A2 △ B2.
Proof.
case => x2 => HA1 HB1 Htriangle.
case: (classic (x2 ∈ A2)).
- move=> HA2.
  left.
  split => //.
  have: x2 ∉ A1 △ A2.
    by apply sym_diff_not_in_from_in.
  rewrite Htriangle => HBnotin HB2.
  apply /HBnotin.
  rewrite sym_diff_comm.
  left.
  by split.
- move=> HA2.
  right.
  split => //.
  have: x2 ∈ A1 △ A2.
    left.
    by split.
  rewrite Htriangle => H.
  move: HB1.
  case H => x3;
    by case.
Qed.

(* S2 問題9 *)
Theorem sym_diff_shakeup A1 A2 B1 B2: A1 △ A2 = B1 △ B2 -> A1 △ B1 = A2 △ B2.
Proof.
move=> Htriangle.
rewrite -eq_iff => x0.
split.
- rewrite {1}/SymmetricDifference.
  case => x1 Hsub.
  + by apply (sub_sym_diff Hsub).
  + rewrite sym_diff_comm.
    by apply (sub_sym_diff Hsub).
- have: (A2 △ A1 = B2 △ B1) => [| Htriangle' ].
    symmetry.
    by rewrite [B2 △ B1]sym_diff_comm [A2 △ A1]sym_diff_comm.
  rewrite {1}/SymmetricDifference.
  case => x1 Hsub.
  + by apply (sub_sym_diff Hsub).
  + rewrite sym_diff_comm.
    by apply (sub_sym_diff Hsub).
Qed.

End Section1_2.


Notation "A ∪ B" := (Cup A B) (at level 50): ensemble_scope.
Notation "A ∩ B" := (Cap A B) (at level 50): ensemble_scope.
Notation "A - B" := (Sub A B) (* at level 50 *): ensemble_scope.
Notation "A ^ 'c'" := (ComplementarySet A) (at level 30): ensemble_scope.
Notation "A △ B" := (SymmetricDifference A B) (at level 50): ensemble_scope.

Arguments FullSet {_}.

Notation "\bigcup AA" := (BigCup (fun A => A) AA) (at level 50): ensemble_scope.
Notation "\bigcap AA" := (BigCap (fun A => A) AA) (at level 50): ensemble_scope.

End Ensemble.

