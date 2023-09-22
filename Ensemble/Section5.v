(* 集合・位相入門(松坂)1 をCoqで証明しつつ読んでいく *)

Set Implicit Arguments.

From mathcomp Require Import ssreflect.

Require Import Coq.Logic.IndefiniteDescription.
Require Import Coq.Logic.FunctionalExtensionality.
Add LoadPath "." as Local.
Require Import Local.Classical.
Require Local.Ensemble.Section4.

Open Scope ensemble_scope.

Module Ensemble.

Import Section1.Ensemble Section2.Ensemble Section3.Ensemble Section4.Ensemble.

Section Section5.

Definition IndexedEnsemble T L := L -> Ensemble T.

Fact bigcup_fun_eq_in_indexed_family T L (A: IndexedEnsemble T L) lam:
  BigCup (fun l => A l) lam = BigCup A lam.
Proof. by []. Qed.

Fact bigcap_fun_eq_in_indexed_family T L (A: IndexedEnsemble T L) lam:
  BigCap (fun l => A l) lam = BigCap A lam.
Proof. by []. Qed.

(* p.45 *)
Theorem bigcup_min T L (A: IndexedEnsemble T L) B lam:
  (forall l, l \in lam -> A l \subset B) ->
  BigCup A lam \subset B.
Proof.
move=> H1 x H2.
case H2 => l [H3 H4].
by apply (H1 l).
Qed.

(* p.45 *)
Theorem bigcap_max T L (A: IndexedEnsemble T L) B lam:
  (forall l, l \in lam -> B \subset A l) ->
  B \subset BigCap A lam.
Proof.
move=> H1 x H2 l H3.
by apply H1.
Qed.

(* 5.1 *)
Theorem bigcup_cap_distrib T L (A: IndexedEnsemble T L) B lam:
  BigCup A lam \cap B = BigCup (fun l => A l \cap B) lam.
Proof.
apply eq_split.
- move=> _ [x [l [H1 H2] H3]].
  by exists l.
- move=> x [l [H1 [H2 H3]]].
  split => //.
  by exists l.
Qed.

(* 5.1' *)
Theorem bigcap_cup_distrib T L (A: IndexedEnsemble T L) B lam:
  BigCap A lam \cup B = BigCap (fun l => A l \cup B) lam.
Proof.
apply eq_split.
- move=> _ [x H1|x H1] l H2;
  by [ left; by apply H1 | right ].
- move=> x H1.
  case (classic (x \in B)) => H2; [ by right |].
  left => l H3.
  move: H2.
  by case (H1 l H3).
Qed.

(* 5.2 *)
Theorem bigcup_compset T L (A: IndexedEnsemble T L) lam:
  (BigCup A lam)^c = BigCap (fun l => (A l)^c) lam.
Proof.
apply eq_split => x.
- move=> H1 l H2.
  rewrite compset_in => H3.
  rewrite compset_in in H1.
  apply H1.
  exists l.
  by split.
- move=> H1.
  rewrite compset_in.
  case => l [H2].
  move: (H1 l).
  rewrite compset_in.
  by apply.
Qed.

(* 5.2' *)
Theorem bigcap_compset T L (A: IndexedEnsemble T L) lam:
  (BigCap A lam)^c = BigCup (fun l => (A l)^c) lam.
Proof.
apply eq_split => x.
- move=> H1.
  rewrite compset_in /In /BigCap in H1.
  rewrite [forall l, _ -> _]forall_iff_not_exists_not in H1.
  apply NNPP in H1.
  case H1 => l H2.
  rewrite not_imply in H2.
  exists l.
  by rewrite compset_in.
- move=> H1.
  rewrite compset_in => H2.
  case H1 => l [H3 H4].
  rewrite compset_in in H4.
  by move: (H2 l H3).
Qed.

(* 5.3 *)
Theorem image_bigcup L A B (f: A -> B) (P: IndexedEnsemble A L) lam:
  Image f (BigCup P lam) = BigCup (fun l => Image f (P l)) lam.
Proof.
apply eq_split => [b [a [[l [H1 H2] <-]]]|b [l [H1 [a [H2 <-]]]]].
- exists l.
  split => //.
  by exists a.
- exists a.
  split => //.
  by exists l.
Qed.

(* 5.4 *)
Theorem image_bigcap L A B (f: A -> B) (P: IndexedEnsemble A L) lam:
  Image f (BigCap P lam) \subset BigCap (fun l => Image f (P l)) lam.
Proof.
move=> b [a [H1 <-]].
exists a.
split => //.
by apply H1.
Qed.

(* 5.3' *)
Theorem invimage_bigcup L A B (f: A -> B) (Q: IndexedEnsemble B L) lam:
  InvImage f (BigCup Q lam) = BigCup (fun l => InvImage f (Q l)) lam.
Proof.
apply eq_split => [a [l [H1 H2]]|a [l [H1 H2]]];
  exists l;
  by split.
Qed.

(* 5.4' *)
Theorem invimage_bigcap L A B (f: A -> B) (Q: IndexedEnsemble B L) lam:
  InvImage f (BigCap Q lam) = BigCap (fun l => InvImage f (Q l)) lam.
Proof. apply eq_split => a H1 l H2; by apply H1. Qed.


Inductive Product (T L: Type) (A: IndexedEnsemble T L)
  : Ensemble (L -> T) :=
  | Product_intro: forall (a: forall l: L, T),
      (forall (l: L), a l \in A l) -> (fun l => a l) \in Product A.

(* p.47 *)
Theorem exists_emptyset_to_product_emptyset T L (A: IndexedEnsemble T L):
  (exists l, A l = \emptyset) -> Product A = \emptyset.
Proof.
move=> [l H1].
rewrite emptyset_not_in => _ [a H2].
suff: a l \in A l.
  by rewrite H1.
by apply H2.
Qed.

Axiom choice: forall (T L: Type) (A: IndexedEnsemble T L),
  (forall (l: L), A l <> \emptyset) -> Product A <> \emptyset.


Lemma not_emptyset_exists T A: A <> \emptyset <-> exists a: T, a \in A.
Proof.
rewrite emptyset_not_in.
split => [ Hneq | Hexi ].
- by rewrite exists_iff_not_forall_not.
- case Hexi => x H1 H2.
  by apply H2 in H1.
Qed.

(* S5 定理7(a) *)
Theorem hoge A B (f: A -> B): Surjective f <-> exists s, f \comp s = \I B.
Proof.
split.
- move=> Hsurj.
  have: forall b: B, exists a, a \in InvImage f \{ b } => [b | H1].
    rewrite surjective_exists in Hsurj.
    case (Hsurj b) => a H1.
    subst.
    by exists a.
  have: exists Ab: IndexedEnsemble A B,
    (forall (b: B), Ab b = InvImage f \{ b }) /\ (forall (b: B), Ab b <> \emptyset) => [| H2].
    exists (fun b => InvImage f \{ b }).
    split => // b.
    rewrite emptyset_not_in => H2.
    case (constructive_indefinite_description _ (H1 b)) => a.
    by apply H2.
  case H2 => Ab [H2'1 H2'2].
  apply choice in H2'2 as H3.
  rewrite not_emptyset_exists in H3.
  case H3 => _ [s H3'].
  exists s.
  apply functional_extensionality => b.
  rewrite /Composite /Identity.
  move: (H3' b).
  by rewrite H2'1.
- case => g H1.
  apply surjective_composite_surjective with (f := g).
  rewrite H1.
  apply identity_surjective.
Qed.

(* S5 定理7(b) *)
Theorem huga A B (f: A -> B): Injective f <-> exists r, r \comp f = \I A.
Proof.
Admitted.








End Section5.

End Ensemble.