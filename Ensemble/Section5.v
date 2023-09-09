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

Variables L T: Type.

Definition IndexedFamily := L -> Ensemble T.

(* p.45 *)
Theorem bigcup_min (A: IndexedFamily) B lam:
  (forall l, l \in lam -> A l \subset B) ->
  BigCup (fun l => A l) lam \subset B.
Proof.
move=> H1 x H2.
case H2 => l [H3 H4].
by apply (H1 l).
Qed.

(* p.45 *)
Theorem bigcap_max (A: IndexedFamily) B lam:
  (forall l, l \in lam -> B \subset A l) ->
  B \subset BigCap (fun l => A l) lam.
Proof.
move=> H1 x H2 l H3.
by apply H1.
Qed.

(* 5.1 *)
Theorem bigcup_cap_distrib (A: IndexedFamily) B lam:
  BigCup (fun l => A l) lam \cap B = BigCup (fun l => A l \cap B) lam.
Proof.
apply eq_split.
- move=> _ [x [l [H1 H2] H3]].
  by exists l.
- move=> x [l [H1 [H2 H3]]].
  split => //.
  by exists l.
Qed.

(* 5.1' *)
Theorem bigcap_cup_distrib (A: IndexedFamily) B lam:
  BigCap (fun l => A l) lam \cup B = BigCap (fun l => A l \cup B) lam.
Proof.
apply eq_split.
- move=> _ [x H1|x H1] l H2;
  by [ left; by apply H1 | right ].
- move=> x H1.
  rewrite /BigCap.
  rewrite /In /BigCap in H1.
  








End Section5.

End Ensemble.