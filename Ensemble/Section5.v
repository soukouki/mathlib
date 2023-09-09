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

End Section5.

End Ensemble.