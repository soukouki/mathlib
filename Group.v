Set Implicit Arguments.

From mathcomp Require Import ssreflect.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.IndefiniteDescription.

Module Algebra.


Section Monoid.

Class Monoid (A : Type) : Type :=
{
  op : A -> A -> A;
  e : A;
  monoid_assoc : forall x y z : A, op x (op y z) = op (op x y) z;
  monoid_e_left : forall x : A, op e x = x;
  monoid_e_right : forall x : A, op x e = x
}.

(* BoolとXorのモノイド。次に群にするために定義 *)
Instance BoolXorMonoid : Monoid bool :=
{
  op := xorb;
  e := false;
  monoid_assoc := fun a b c => eq_sym (xorb_assoc a b c);
  monoid_e_left := xorb_false_l;
  monoid_e_right := xorb_false_r
}.

Theorem monoid_exists_unique_e A (M : Monoid A) : forall e', (forall x, op e' x = x) -> e' = e.
Proof.
move=> e' H1.
rewrite -(monoid_e_right e').
by rewrite -{2}(H1 e).
Qed.

End Monoid.


Section Group.

Class Group A (M : Monoid A) : Type :=
{
  group_inv : forall x : A, exists xi : A, op xi x = e /\ op x xi = e;
}.

Lemma xorb_inv : forall x, exists xi, xorb xi x = false /\ xorb x xi = false.
Proof.
move=> x.
exists x.
split;
  apply xorb_nilpotent.
Qed.

(* BoolとXorの群 *)
Instance BoolXorGroup : Group BoolXorMonoid :=
{
  group_inv := xorb_inv
}.

Theorem group_exists_unique_inv A (M : Monoid A) (G : Group M) : forall x, exists! xi, op xi x = e /\ op x xi = e.
Proof.
move=> x.
rewrite -(unique_existence _).
split.
- case (group_inv x) => xi [Hxil Hxir].
  exists xi.
  by split.
- move=> a b [Hal Har] [Hbl Hbr].
  rewrite -(monoid_e_right a) -Hbr.
  rewrite monoid_assoc.
  by rewrite Hal monoid_e_left.
Qed.

Definition inv A (M : Monoid A) (G : Group M) : A -> A :=
  fun x => proj1_sig (constructive_indefinite_description _ (group_exists_unique_inv G x)).

Lemma inv_sort A (M : Monoid A) (G : Group M) : forall x xi, xi = inv G x <-> op xi x = e /\ op x xi = e.
Proof.
move=> x xi.
unfold inv.
move: (constructive_indefinite_description _ (group_exists_unique_inv G x)) => He.
split.
- case (proj2_sig He) => [[Hel Her] _] ->.
  by split.
- move => Hxe.
  move: (group_exists_unique_inv G x).
  rewrite -unique_existence => [[_ Huniq]].
  apply Huniq => //.
  by apply (proj2_sig He).
Qed.

Lemma op_inv_left A (M : Monoid A) (G : Group M) : forall x, op (inv G x) x = e.
Proof. move=> x. by apply (inv_sort G x (inv G x)). Qed.

Lemma op_inv_right A (M : Monoid A) (G : Group M) : forall x, op x (inv G x) = e.
Proof. move=> x. by apply (inv_sort G x (inv G x)). Qed.

Theorem a_b_inv_eq_b_inv_a_inv A (M : Monoid A) (G : Group M) : forall a b, inv G (op a b) = op (inv G b) (inv G a).
Proof.
move=> a b.
symmetry.
rewrite inv_sort.
split.
- rewrite -monoid_assoc [op (inv G a) _]monoid_assoc.
  by rewrite op_inv_left monoid_e_left op_inv_left.
- rewrite -monoid_assoc [op b _]monoid_assoc.
  by rewrite op_inv_right monoid_e_left op_inv_right.
Qed.





End Group.


End Algebra.

