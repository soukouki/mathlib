(* 集合・位相入門(松坂)1 をCoqで証明しつつ読んでいく *)

Set Implicit Arguments.

From mathcomp Require Import ssreflect.

Require Import Coq.Logic.IndefiniteDescription.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Setoid.
Add LoadPath "." as Local.
Require Import Local.Classical.
Require Local.Ensemble.Section2.
Open Scope ensemble_scope.

Module Ensemble.

Import Section1.Ensemble Section2.Ensemble.

Section Section3.

Implicit Types A B: Type.

Inductive EnsembleProd TA TB (A: Ensemble TA) (B: Ensemble TB)
  : Ensemble (TA * TB) :=
  | EnsembleProd_pair x: fst x \in A -> snd x \in B -> x \in EnsembleProd A B.
Notation "A * B" := (EnsembleProd A B).

(* Corr = Correspondence *)
Definition Corr A B := A -> Ensemble B.
Notation "A ->c B" := (Corr A B) (at level 99).

Lemma corr_extensionality A B (f g: A ->c B):
  (forall a b, b \in f a <-> b \in g a) -> f = g.
Proof.
move=> H.
apply functional_extensionality => a.
apply functional_extensionality => b.
apply propositional_extensionality.
by apply H.
Qed.

Definition Graph A B (C: A ->c B): Ensemble (A * B) := (fun x: (A * B) => (snd x) \in C (fst x)).

(* (3.1) *)
Theorem graph_pair A B C (a: A):
  C a = ((fun b => (Graph C) (pair a b)): Ensemble B).
Proof. by []. Qed.

(* S3 定理1 *)
Theorem exists_one_corr_from_graph A B (X: Ensemble (A * B)): exists! (G: A ->c B), X = Graph G.
Proof.
exists (fun a b => X (pair a b)).
split.
- rewrite /Graph.
  apply ensemble_extensionality => x.
  by rewrite /In -surjective_pairing.
- move=> C HX.
  by rewrite HX.
Qed.

Definition DefRange   A B (C: A ->c B): Ensemble A := fun a: A => exists b: B, (a, b) \in Graph(C).
Definition ValueRange A B (C: A ->c B): Ensemble B := fun b: B => exists a: A, (a, b) \in Graph(C).

Definition InvCorr A B (C: A->c B): B ->c A := fun (b: B) (a: A) => b \in C a.

Theorem defrange_ne_empty_set A B (C: A ->c B): DefRange C = fun a: A => C a <> \emptyset.
Proof.
apply eq_split => a.
- rewrite /In /DefRange.
  case => b HinG.
  rewrite emptyset_not_in => H.
  by apply (H b).
- rewrite /In /DefRange.
  rewrite emptyset_not_in.
  rewrite -exists_iff_not_forall_not.
  case => b Hin.
  by exists b.
Qed.

Lemma defrange_exists A B (C: A ->c B): DefRange C = fun a: A => exists b, b \in C a.
Proof. by []. Qed.

(* (3.2) *)
Theorem in_invcorr A B (C: A ->c B) a b: b \in C a <-> a \in (InvCorr C) b.
Proof. by []. Qed.

(* (3.3) *)
Theorem defrange_invcorr_to_valuerange A B (C: A ->c B): DefRange(InvCorr C) = ValueRange C.
Proof. by []. Qed.

(* (3.3)' *)
Theorem valuerange_invcorr_to_defrange A B (C: A ->c B): ValueRange(InvCorr C) = DefRange C.
Proof. by []. Qed.

(* 3.4 *)
Theorem invcorr_twice A B (C: A ->c B): InvCorr (InvCorr C) = C.
Proof. by []. Qed.

Lemma in_emptyset A (x: A): x \in \emptyset <-> False.
Proof. by []. Qed.

(* p.27 *)
Theorem invcorr_is_not_empty_iff_in_valuerange A B b (C: A ->c B):
  (InvCorr C b <> \emptyset) <-> b \in ValueRange C.
Proof.
split.
- move=> Hneq.
  apply NNPP => Hnot_in.
  apply Hneq.
  apply eq_split => // x Hin_inv.
  rewrite in_emptyset.
  apply Hnot_in.
  exists x.
  by apply Hin_inv.
- move=> Hb Hneq.
  move: Hb.
  case => a Hgraph.
  suff: a \notin (InvCorr C b) => //.
  by rewrite Hneq.
Qed.

(* 
(* Map = Mapping *)
Definition Map (A B: Type) := A -> B.
Notation "A -> B" := (Map A B) (at level 90).

これは関数と等しいので、今回は定義しない。
 *)

Definition MapAsCorr A B (f: A -> B): A ->c B := 
  fun a b => b = f a.

Definition Identity {A}: A -> A := fun a: A => a.
Notation "\I A" := (Identity: A -> A) (at level 30).


(* 分かりづらいので別名を定義 *)
Definition get_value := proj1_sig.
Definition get_proof := proj2_sig.

(* 関数が、本での定義とCoqの定義で等しいことを確認する *)
Lemma map_def A B (C: A ->c B):
  (forall a: A, exists! b: B, C a = \{ b }) <-> exists! f, C = MapAsCorr f.
Proof.
split => [H1 | [f H1 a]].
- move: (fun a => constructive_definite_description _ (H1 a)) => H1sig.
  exists (fun a => get_value (H1sig a)).
  split.
  + apply corr_extensionality => a b.
    by rewrite (get_proof (H1sig a)) singleton_eq.
  + move=> f H2.
    subst.
    apply functional_extensionality => a.
    move: (get_proof (H1sig a)) => H3.
    symmetry.
    rewrite -singleton_eq.
    by rewrite -H3.
- exists (f a).
  case H1 => H2 _.
  split.
  + rewrite H2.
    by apply ensemble_extensionality.
  + move=> b H3.
    by rewrite -singleton_eq -H3 H2.
Qed.

(* S3 定理2 *)
Theorem exist_one_map_equivalent_to_graphs A B (G: Ensemble (A * B)):
  (exists f: A -> B, G = Graph (MapAsCorr f)) <-> (forall a, exists! b, (a, b) \in G).
Proof.
split.
- case => f HG a.
  exists (f a).
  rewrite HG.
  by split.
- move=> HinG.
  move: (fun a => constructive_definite_description _ (HinG a)) => Sigb.
  exists (fun a => get_value (Sigb a)).
  apply eq_split.
  + move=> x Hx.
    rewrite /Graph /MapAsCorr /In.
    (* bからグラフ上の(a, b)は一意に求められることを示す。
       uniqueness = forall x y: A, P x -> P y -> x = y という定義で、_ = _ を処理するのに使える *)
    have: (uniqueness (fun b: B => (fst x, b) \in G)).
      by apply unique_existence.
    apply.
    * by rewrite -surjective_pairing.
    * by apply get_proof.
  + move=> x Hx.
    rewrite /MapAsCorr /Graph /In in Hx.
    rewrite (surjective_pairing x).
    rewrite Hx.
    by apply get_proof.
Qed.

Lemma singleton_unique_eq A a (P: Ensemble A):
  a \in P -> uniqueness (fun a' => a' \in P) -> P = \{a}.
Proof.
move=> Hin Huniq.
apply eq_split.
- move=> a' HA'.
  rewrite singleton_eq.
  by apply Huniq.
- move=> a' HA'.
  rewrite singleton_eq in HA'.
  by rewrite HA'.
Qed.

Lemma invcorr_cap_emptyset_unique A B (C: A ->c B):
  (forall b b', b <> b' -> InvCorr C b \cap InvCorr C b' = \emptyset) ->
  forall a, uniqueness (fun b => b \in C a).
Proof.
move=> Hinv a b1 b2 Hb1 Hb2.
apply NNPP => H1.
move: (Hinv _ _ H1).
rewrite cap_eq_emptyset => H2.
move: (H2 a).
rewrite compset_in.
by apply.
Qed.

(* 問題1から問題2は飛ばす *)

Lemma corr_to_map A B {C: A ->c B}:
  (forall b, exists a, C b = \{ a }) ->
  {f: A -> B | forall a, \{ f a } = C a}.
Proof.
move=> H1.
move: (fun a => constructive_indefinite_description _ (H1 a)) => Hsigb.
exists (fun a => get_value (Hsigb a)) => a.
by move: (get_proof (Hsigb a)) => H2.
Qed.

(* S3 問題3 *)
Theorem map_as_corr_invcorr A B (C: A ->c B):
  (exists! f: A -> B, MapAsCorr f = C) <->
  (DefRange C = FullSet /\ (forall b b', b <> b' -> InvCorr C b \cap InvCorr C b' = \emptyset)).
Proof.
rewrite -eq_fullset.
split.
- move=> Hf.
  move: (constructive_definite_description _ Hf).
  clear Hf => Hf.
  split.
  + move=> a.
    case Hf => f Hfeq.
    exists (f a).
    by rewrite -Hfeq.
  + move=> b b' HB.
    rewrite cap_eq_emptyset.
    case Hf => f Hf' a.
    rewrite -Hf' => Heq.
    rewrite compset_in => Heq'.
    rewrite /InvCorr /MapAsCorr /In in Heq.
    rewrite /InvCorr /MapAsCorr /In in Heq'.
    by rewrite Heq' in HB. (* ここまでは古い証明と同じ *)
- case => Hdef Hinv.
  move: (invcorr_cap_emptyset_unique Hinv) => Huniq.
  have: forall a: A, exists b, C a = \{ b } => [ a | Hsig ].
    rewrite /In defrange_exists in Hdef.
    move: (constructive_indefinite_description _ (Hdef a)) => Bsig.
    exists (get_value Bsig).
    apply singleton_unique_eq => //.
    by apply (get_proof Bsig).
  move: (corr_to_map Hsig) => Hf.
  rewrite -unique_existence.
  split.
  + exists (fun a => get_value Hf a).
    apply functional_extensionality => a.
    case (Hsig a) => b HB.
    rewrite HB.
    apply singleton_unique_eq.
    * rewrite /MapAsCorr /In.
      apply (Huniq a).
      - by rewrite HB.
      - move: (get_proof Hf a) => H.
        rewrite -eq_iff in H.
        by rewrite -H.
    * rewrite /MapAsCorr /In => b1 b2 HB1 HB2.
      by subst.
  + move=> f f' Hfeq Hfeq'.
    apply functional_extensionality => a.
    apply (Huniq a);
      by [ rewrite -Hfeq | rewrite -Hfeq' ].
Qed.

(* 別証明 *)
Goal forall A B (C: A ->c B),
  (exists! f: A -> B, MapAsCorr f = C) <->
  (DefRange C = FullSet /\ (forall b b', b <> b' -> InvCorr C b \cap InvCorr C b' = \emptyset)).
Proof.
split.
- move=> Hf.
  move: (constructive_definite_description _ Hf).
  clear Hf => Hf.
  split.
  + rewrite -eq_fullset => a.
    case Hf => f Hfeq.
    exists (f a).
    by rewrite -Hfeq.
  + move=> b b' HB.
    rewrite cap_eq_emptyset.
    case Hf => f Hf' a.
    rewrite -Hf' => Heq.
    rewrite compset_in => Heq'.
    rewrite /InvCorr /MapAsCorr /In in Heq.
    rewrite /InvCorr /MapAsCorr /In in Heq'.
    by rewrite Heq' in HB.
- case.
  rewrite -eq_fullset.
  rewrite /In defrange_exists => Hdef Hinv.
  move: (invcorr_cap_emptyset_unique Hinv) => Huniq.
  rewrite -unique_existence.
  split.
  + have: { f: A -> B | forall a b, f a = b -> b \in C a } => [| F ].
      apply constructive_indefinite_description.
      move: (fun a => constructive_indefinite_description _ (Hdef a)) => sigB.
      exists (fun a => get_value (sigB a)) => a b Heq.
      rewrite -Heq.
      by apply (get_proof (sigB a)).
    exists (get_value F).
    apply functional_extensionality => a.
    have: get_value F a \in C a => [| Hin ].
      by apply (get_proof F a (get_value F a)).
    apply eq_split => b H.
    + rewrite /In /MapAsCorr in H.
      by rewrite H.
    + rewrite /In /MapAsCorr.
      by apply (Huniq a).
  + move=> f1 f2 Heq1 Heq2.
    apply functional_extensionality => a.
    apply (Huniq a);
      by [ rewrite -Heq1 | rewrite -Heq2 ].
Qed.

Lemma defrange_map_as_corr A B (f: A -> B) a:
  a \in DefRange (MapAsCorr f) <-> exists b, f a = b.
Proof.
split;
  case => b H;
  by exists b.
Qed.

Lemma valuerange_map_as_corr A B (f: A -> B) b:
  b \in ValueRange (MapAsCorr f) <-> exists a, f a = b.
Proof.
split;
  case => a H;
  by exists a.
Qed.

(* S3 問題4 *)
Theorem identity_graph A:
  Graph (MapAsCorr (\I A)) = fun x => fst x = snd x.
Proof. by apply eq_split. Qed.

End Section3.


Notation "A * B" := (EnsembleProd A B): ensemble_scope.
Notation "A ->c B" := (Corr A B) (at level 99): ensemble_scope.
Notation "\I A" := (Identity: A -> A) (at level 30): ensemble_scope.


End Ensemble.

