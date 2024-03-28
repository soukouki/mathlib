(* 集合・位相入門(松坂)1 をCoqで証明しつつ読んでいく *)

Set Implicit Arguments.

From mathcomp Require Import ssreflect.

Add LoadPath "." as Local.
Require Import Local.Classical.
Require Local.Ensemble.Section1_5.

Open Scope ensemble_scope.

Module Ensemble.

Import Section1_1.Ensemble Section1_2.Ensemble Section1_3.Ensemble Section1_4.Ensemble Section1_5.Ensemble.

Section Section1_6.

Definition Relation A := A -> A -> Prop.

Class Equivalence A (R: Relation A) := {
  reflexive: forall a: A, R a a;
  symmetric: forall a b: A, R a b -> R b a;
  transitive: forall a b c: A, R a b -> R b c -> R a c;
}.

Instance EqEquivalence A: Equivalence (A := A) eq :=
{
  reflexive := fun a => eq_refl a;
  symmetric := fun _ _ H => eq_sym H;
  transitive := eq_trans (A := A);
}.

Instance TrivialEquivalence A: Equivalence (A := A) (fun _ _ => True) :=
{
  reflexive := fun _ => I;
  symmetric := fun _ _ _ => I;
  transitive := fun _ _ _ _ _ => I;
}.

(* 例2の合同については、写像に付随する同値関係の系として簡単に表せられる *)

Definition func_equiv A B (f: A -> B) x y := f x = f y.

Lemma func_equivalence_transitive A B (f: A -> B) a b c:
  func_equiv f a b -> func_equiv f b c -> func_equiv f a c.
Proof.
move=> H1 H2.
rewrite /func_equiv.
by rewrite H1.
Qed.

Instance FuncEquivalence A B (f: A -> B): Equivalence (func_equiv f) :=
{
  reflexive := fun a => eq_refl;
  symmetric := fun _ _ H => eq_sym H;
  transitive := func_equivalence_transitive (f := f);
}.

Definition mod_equiv mod a b := Nat.modulo a mod = Nat.modulo b mod.

Definition ModEquivalence mod: Equivalence (mod_equiv mod) := FuncEquivalence _.

(* 直和分割 *)
Class Partition A (M: FamilyEnsemble A) :=
{
  cover: \bigcup M = FullSet;
  disjoint: forall C C', C \in M -> C' \in M -> C <> C' -> C \cup C' = \emptyset;
}.

Definition partition_equiv A (M: FamilyEnsemble A) (P: Partition M) x y :=
  exists C: Ensemble A, C \in M /\ x \in C /\ y \in C.

Lemma partition_equivalence_reflexive A (M: FamilyEnsemble A) (P: Partition M) a:
  partition_equiv P a a.
Proof.
rewrite /partition_equiv.
case P => H1 H2.
rewrite -eq_fullset /BigCup {1}/In in H1.
case (H1 a) => C [H3 H4].
by exists C.
Qed.

Lemma partition_equivalence_symmetric A (M: FamilyEnsemble A) (P: Partition M) a b:
  partition_equiv P a b -> partition_equiv P b a.
Proof.
case => C [H1 H2].
exists C.
split => //.
by rewrite and_comm.
Qed.

Lemma partition_in_eq A (M: FamilyEnsemble A) (P: Partition M) C1 C2 (x: A):
  (* 直感的にはx \in C2もないとおかしいので、なんで証明できてるのか謎 *)
  C1 \in M -> C2 \in M -> x \in C1 -> C1 = C2.
Proof.
move=> HC1M HC2M HxC1.
apply NNPP => Hneq.
case P => H1 H2.
move: (H2 C1 C2 HC1M HC2M Hneq).
rewrite emptyset_not_in => H3.
move: (H3 x).
apply.
by left.
Qed.

Lemma partition_equivalence_transitive A (M: FamilyEnsemble A) (P: Partition M) a b c:
  partition_equiv P a b -> partition_equiv P b c -> partition_equiv P a c.
Proof.
case => C [HCM [HaC HbC]].
case => C' [HC'M [HaC' HbC']].
have: C = C' => [| Heq].
  by apply partition_in_eq with (M := M) (x := b).
subst.
by exists C'.
Qed.











