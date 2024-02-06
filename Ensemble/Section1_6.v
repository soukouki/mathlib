(* 集合・位相入門(松坂)1 をCoqで証明しつつ読んでいく *)

Set Implicit Arguments.

From mathcomp Require Import ssreflect.

Add LoadPath "." as Local.
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
  transitive := fun _ _ _ _  _=> I;
}.

Section ModEquivalence.

Variable mod: nat.

Definition mod_equiv a b := Nat.modulo a mod = Nat.modulo b mod.

Lemma mod_equivalence_transitive a b c: mod_equiv a b -> mod_equiv b c -> mod_equiv a c.
Proof.
move=> H1 H2.
rewrite /mod_equiv.
by rewrite H1.
Qed.

Instance ModEquivalence: Equivalence mod_equiv :=
{
  reflexive := fun a => eq_refl;
  symmetric := fun _ _ H => eq_sym H;
  transitive := mod_equivalence_transitive;
}.

End ModEquivalence.
