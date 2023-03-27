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

Lemma forall_iff_not_exists_not: forall {A} (F: A -> Prop),
  (forall x: A, F x) <-> ~ (exists x: A, ~ F x).
Proof.
move=> A F.
split.
- move=> Hforall.
  case => x Hnot.
  by move: (Hforall x).
- move=> Hexists x.
  apply NNPP => Hnot.
  apply Hexists.
  by exists x.
Qed.

Lemma exists_iff_not_forall_not: forall {A} (F: A -> Prop),
  (exists x: A, F x) <-> ~ (forall x: A, ~ F x).
Proof.
move=> A F.
split.
- move=> Hexists Hforall.
  move: Hexists.
  case => x HF.
  by move: (Hforall x).
- move=> Hforall.
  apply NNPP => Hexists.
  apply Hforall => x HF.
  apply Hexists.
  by exists x.
Qed.





