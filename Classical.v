(* Classical関連の切り出し *)

From mathcomp Require Import ssreflect.

Require Export Classical_Prop.

Lemma not_or_and: forall P Q, ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof.
move=> P Q.
split.
- by apply not_or_and.
- by apply and_not_or.
Qed.

Lemma not_and_or: forall P Q, ~ (P /\ Q) <-> ~ P \/ ~Q.
Proof.
move=> P Q.
split.
- by apply not_and_or.
- by apply or_not_and.
Qed.
