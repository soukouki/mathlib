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
  transitive := fun _ _ _ _ _ => I;
}.

Definition mod_equiv mod a b := Nat.modulo a mod = Nat.modulo b mod.

Lemma mod_equivalence_transitive mod a b c:
  mod_equiv mod a b -> mod_equiv mod b c -> mod_equiv mod a c.
Proof.
move=> H1 H2.
rewrite /mod_equiv.
by rewrite H1.
Qed.

Instance ModEquivalence mod: Equivalence (mod_equiv mod) :=
{
  reflexive := fun a => eq_refl;
  symmetric := fun _ _ H => eq_sym H;
  transitive := mod_equivalence_transitive (mod := mod);
}.

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










