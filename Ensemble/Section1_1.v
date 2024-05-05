(* 集合・位相入門(松坂)1 をCoqで証明しつつ読んでいく *)

Set Implicit Arguments.

Require Import ssreflect.
Require Import Coq.Setoids.Setoid.

Module Ensemble.

Section Section1_1.

Variable T: Type.

Definition Ensemble := T -> Prop.

Definition In a (A: Ensemble): Prop := A a.
Notation "a ∈ A" := (In a A) (at level 55).

Notation "a ∉ A" := (~ In a A) (at level 55).

Definition Singleton (a: T): Ensemble := fun a' => a = a'.
Notation "\{ a }" := (Singleton a).

Definition EmptySet: Ensemble := fun _ => False.
Notation "∅" := EmptySet.

(* 外延性の公理 *)
Axiom ensemble_extensionality: forall (A B: Ensemble),
  (forall (x: T), (x ∈ A <-> x ∈ B)) -> A = B.

Lemma eq_iff A B:
  (forall (x: T), (x ∈ A <-> x ∈ B)) <-> A = B.
Proof.
split.
- by apply ensemble_extensionality.
- move=> HAB x.
  by rewrite HAB.
Qed.

Definition Subset A B: Prop := forall x, x ∈ A -> x ∈ B.
Notation "A ⊂ B" := (Subset A B) (at level 55).

(* (1.3) *)
Theorem eq_subset A B: A = B <-> A ⊂ B /\ B ⊂ A.
Proof.
split.
- move=> HA_eq_B.
  rewrite HA_eq_B.
  by rewrite /Subset.
- case.
  move=> HA_subset_B HB_subset_A.
  apply ensemble_extensionality => x.
  split.
  + by apply HA_subset_B.
  + by apply HB_subset_A.
Qed.

Lemma eq_split A B: A ⊂ B -> B ⊂ A -> A = B.
Proof.
move=> HAB HBA.
by apply eq_subset.
Qed.

(* (1.4)
   本にあるのは A ⊂ B /\ B ⊂ C だけれど、明らかに同等な上にこちらのほうがCoq的に扱いやすいのでこう書いた
   今後も同じような例が出てくるが、同様に行う *)
Theorem subset_trans A B C: A ⊂ B -> B ⊂ C -> A ⊂ C.
Proof.
move=> HA_subset_B HB_subset_C.
rewrite /Subset => x Hx_in_A.
by apply /HB_subset_C /HA_subset_B.
Qed.

(* (1.5) *)
Theorem emptyset_subset A: ∅ ⊂ A.
Proof. by []. Qed.

Lemma singleton_eq a a': a ∈ \{a'} <-> a = a'.
Proof. by []. Qed.

(* S1 問題1 *)
Theorem singleton_subset a A: a ∈ A <-> \{a} ⊂ A.
Proof.
split.
- move=> HA a' Heq.
  rewrite singleton_eq in Heq.
  by rewrite Heq.
- by apply.
Qed.

(* 問題2から問題5は飛ばす *)

End Section1_1.

Declare Scope ensemble_scope.

Notation "a ∈ A" := (In a A) (at level 55): ensemble_scope.
Notation "a ∉ A" := (~ In a A) (at level 55): ensemble_scope.
Notation "\{ a }" := (Singleton a).
Notation "∅" := (EmptySet): ensemble_scope.
Arguments EmptySet {_}.
Notation "A ⊂ B" := (Subset A B) (at level 55): ensemble_scope.

End Ensemble.


