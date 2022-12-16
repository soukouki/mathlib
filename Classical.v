(* Classical関連の切り出し *)

(* 古典論理における書き換えをiffにして、rewriteで使えるようにしている *)

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

Lemma not_imply: forall P Q: Prop, ~ (P -> Q) <-> P /\ ~Q.
Proof.
move=> P Q.
split => H.
- by apply imply_to_and.
- inversion H => HPQ.
  by apply /H1 /HPQ.
Qed.

Lemma not_iff: forall P Q, ~ (P <-> Q) <-> (~P /\ Q) \/ (P /\ ~Q).
Proof.
move=> P Q.
rewrite {2}/iff.
rewrite not_and_or.
rewrite 2!not_imply.
by rewrite or_comm {1}and_comm.
Qed.










