(* 集合・位相入門(松坂)1 をCoqで証明しつつ読んでいく *)

Set Implicit Arguments.

From mathcomp Require Import ssreflect.

Add LoadPath "." as Local.
Require Import Local.Classical.
Require Local.Ensemble.Section4.

Open Scope ensemble_scope.

Module Ensemble.

Import Section1.Ensemble Section2.Ensemble Section3.Ensemble Section4.Ensemble.

Section Section5.

Variable L: Type.

Definition IndexedFamily T := L -> Ensemble T.

Fact bigcup_fun_eq_in_indexed_family T (A: IndexedFamily T) lam:
  BigCup (fun l => A l) lam = BigCup A lam.
Proof. by []. Qed.

Fact bigcap_fun_eq_in_indexed_family T (A: IndexedFamily T) lam:
  BigCap (fun l => A l) lam = BigCap A lam.
Proof. by []. Qed.

(* p.45 *)
Theorem bigcup_min T (A: IndexedFamily T) B lam:
  (forall l, l \in lam -> A l \subset B) ->
  BigCup A lam \subset B.
Proof.
move=> H1 x H2.
case H2 => l [H3 H4].
by apply (H1 l).
Qed.

(* p.45 *)
Theorem bigcap_max T (A: IndexedFamily T) B lam:
  (forall l, l \in lam -> B \subset A l) ->
  B \subset BigCap A lam.
Proof.
move=> H1 x H2 l H3.
by apply H1.
Qed.

(* 5.1 *)
Theorem bigcup_cap_distrib T (A: IndexedFamily T) B lam:
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
Theorem bigcap_cup_distrib T (A: IndexedFamily T) B lam:
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
Theorem bigcup_compset T (A: IndexedFamily T) lam:
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
Theorem bigcap_compset T (A: IndexedFamily T) lam:
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
Theorem image_bigcup A B (f: A -> B) (P: IndexedFamily A) lam:
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







End Section5.

End Ensemble.