(* 集合・位相入門(松坂)1 をCoqで証明しつつ読んでいく *)

Set Implicit Arguments.

From mathcomp Require Import ssreflect.

Require Import PeanoNat.

Add LoadPath "." as Local.
Require Import Local.Classical.
Require Import Local.Ensemble.Section1.
Open Scope ensemble_scope.

Module Ensemble.

Include Section1.Ensemble.

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

(* 個数の定義はCoq.Sets.Finite_setsを持ってきた *)
Inductive Cardinal: Ensemble T -> nat -> Prop :=
  | cardinal_empty: Cardinal \emptyset 0
  | cardinal_add: forall (A: Ensemble T) (n: nat),
      Cardinal A n -> forall x, x \notin A -> Cardinal (A \cup \{ x }) (S n).

Lemma cardinal_invert (A: Ensemble T) (n: nat) (HA: Cardinal A n):
    match n with
      | O => A = \emptyset
      | S n => exists A' x, A = A' \cup \{ x } /\ x \notin A' /\ Cardinal A' n
    end.
Proof.
induction HA => //.
exists A.
by exists x.
Qed.

Lemma emptyset_cardinal A: Cardinal A 0 <-> A = \emptyset.
Proof.
split => [ HA | Heq ].
- by apply (cardinal_invert HA).
- rewrite Heq.
  by apply cardinal_empty.
Qed.

Lemma emptyset_notin A: A = \emptyset <-> forall x: T, x \notin A.
Proof.
split => [ Heq x | H ].
- by rewrite Heq.
- apply eq_split.
  + move=> x HA.
    apply NNPP => Hnot.
    by apply (H x).
  + by apply emptyset_subset.
Qed.

Lemma emptyset_cardinal_n n: Cardinal \emptyset n <-> n = 0.
Proof.
split => [ H | Heq ].
- move: (cardinal_invert H).
  case_eq n => // n' Hn.
  subst.
  case => A.
  case => x.
  case => Hcup.
  symmetry in Hcup.
  rewrite emptyset_notin in Hcup.
  case (Hcup x).
  by right.
- rewrite Heq.
  by apply cardinal_empty.
Qed.

Lemma singleton_cardinal A: Cardinal A 1 <-> exists x, A = \{ x }.
split => [ HA | Hexi ].
- case (cardinal_invert HA) => A'.
  case => x.
  case => HAeq.
  case => Hx' HA'.
  exists x.
  subst.
  suff: A' = \emptyset => [ H |].
    by rewrite H emptyset_cup.
  by rewrite emptyset_cardinal in HA'.
- case Hexi => x Heq.
  rewrite Heq.
  rewrite -(emptyset_cup \{ x }).
  apply cardinal_add => //.
  by apply emptyset_cardinal.
Qed.

Lemma subset_emptyset (A: Ensemble T): A \subset \emptyset <-> A = \emptyset.
Proof.
split => H.
- by apply eq_split.
- by rewrite H.
Qed.

Lemma subset_cardinal A B: A \subset B -> forall n m, Cardinal A n -> Cardinal B m -> n <= m.
Proof.
move=> Hsubset n m Ha Hb.
move: m Hb.
induction m => Hb.
- rewrite Nat.le_0_r.
  move: (cardinal_invert Hb) => Heqb.
  rewrite Heqb in Hsubset.
  suff: A = \emptyset => [ Heqa |].
    rewrite Heqa in Ha.
    by rewrite emptyset_cardinal_n in Ha.
  by rewrite -subset_emptyset.
- 


  (* どうにかしてx \in Bを作り出して、Hsubsetを使う形 *)
  move: (cardinal_invert Hm).
  case => B'.
  case => x.
  case => HB'.
  case => Hx' Hc.
  

  move: (cardinal_invert Hn).
  



    使いづれーーーーー！
    cardinalがnatを引数にする形で定義されてるからとても扱いづらい
    でも、Ensembleは有限集合か無限集合かはわからないから、任意の集合からその個数を取得することはできない














(* ドイツ文字の変数は、AA, BBのように2文字つなげて区別することにする *)

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
Notation "A \triangle B" := (SymmetricDifference A B) (at level 50): ensemble_scope.

Arguments FullSet {_}.
Arguments BigCup {_} _ _.
Arguments BigCap {_} _ _.

Notation "\bigcup AA" := (BigCup AA) (at level 50): ensemble_scope.
Notation "\bigcap AA" := (BigCap AA) (at level 50): ensemble_scope.

End Ensemble.

