(* 集合・位相入門(松坂)1 をCoqで証明しつつ読んでいく *)

Set Implicit Arguments.

From mathcomp Require Import ssreflect.

Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.IndefiniteDescription.
Require Import Coq.Logic.FunctionalExtensionality.
Add LoadPath "." as Local.
Require Import Local.Classical.
Require Local.Ensemble.Section1_4.

Open Scope ensemble_scope.

Module Ensemble.

Import Section1_1.Ensemble Section1_2.Ensemble Section1_3.Ensemble Section1_4.Ensemble.

Section Section1_5.

Definition IndexedEnsemble T L := L -> Ensemble T.

Fact bigcup_fun_eq_in_indexed_family T L (A: IndexedEnsemble T L) lam:
  BigCup (fun l => A l) lam = BigCup A lam.
Proof. by []. Qed.

Fact bigcap_fun_eq_in_indexed_family T L (A: IndexedEnsemble T L) lam:
  BigCap (fun l => A l) lam = BigCap A lam.
Proof. by []. Qed.

(* p.45 *)
Theorem bigcup_min T L (A: IndexedEnsemble T L) B lam:
  (forall l, l \in lam -> A l \subset B) ->
  BigCup A lam \subset B.
Proof.
move=> H1 x [l [H2 H3]].
by apply (H1 l).
Qed.

(* p.45 *)
Theorem bigcap_max T L (A: IndexedEnsemble T L) B lam:
  (forall l, l \in lam -> B \subset A l) ->
  B \subset BigCap A lam.
Proof.
move=> H1 x H2 l H3.
by apply H1.
Qed.

(* 5.1 *)
Theorem bigcup_cap_distrib T L (A: IndexedEnsemble T L) B lam:
  BigCup A lam \cap B = BigCup (fun l => A l \cap B) lam.
Proof.
apply eq_split.
- move=> _ [x [l [H1 H2] H3]].
  by exists l.
- move=> x [l [H1 [H2 H3]]].
  split => //.
  by exists l.
Qed.

(* 5.1' *)
Theorem bigcap_cup_distrib T L (A: IndexedEnsemble T L) B lam:
  BigCap A lam \cup B = BigCap (fun l => A l \cup B) lam.
Proof.
apply eq_split.
- move=> _ [x H1|x H1] l H2;
  by [ left; by apply H1 | right ].
- move=> x H1.
  case (classic (x \in B)) => H2.
  + by right.
  + left => l H3.
    move: H2.
    by case (H1 l H3).
Qed.

(* 5.2 *)
Theorem bigcup_compset T L (A: IndexedEnsemble T L) lam:
  (BigCup A lam)^c = BigCap (fun l => (A l)^c) lam.
Proof.
apply eq_split => x.
- rewrite compset_in => H1 l H2.
  rewrite compset_in => H3.
  apply H1.
  by exists l.
- move=> H1.
  rewrite compset_in => [[l [H2 H3]]].
  move: (H1 l).
  rewrite compset_in.
  by apply.
Qed.

(* 5.2' *)
Theorem bigcap_compset T L (A: IndexedEnsemble T L) lam:
  (BigCap A lam)^c = BigCup (fun l => (A l)^c) lam.
Proof.
apply eq_split => x.
- move=> H1.
  rewrite compset_in /In /BigCap in H1.
  rewrite [forall l, _ -> _]forall_iff_not_exists_not in H1.
  apply NNPP in H1.
  case H1 => l H2.
  rewrite not_imply -compset_in in H2.
  by exists l.
- move=> [l [H1 /compset_in H2]].
  rewrite compset_in => H3.
  by apply /H2 /H3.
Qed.

(* 5.3 *)
Theorem image_bigcup L A B (f: A -> B) (P: IndexedEnsemble A L) lam:
  Image f (BigCup P lam) = BigCup (fun l => Image f (P l)) lam.
Proof.
apply eq_split => [b [a [[l [H1 H2] <-]]]|b [l [H1 [a [H2 <-]]]]].
- exists l.
  split => //.
  by exists a.
- exists a.
  split => //.
  by exists l.
Qed.

(* 5.4 *)
Theorem image_bigcap L A B (f: A -> B) (P: IndexedEnsemble A L) lam:
  Image f (BigCap P lam) \subset BigCap (fun l => Image f (P l)) lam.
Proof.
move=> b [a [H1 <-]].
exists a.
split => //.
by apply H1.
Qed.

(* 5.3' *)
Theorem invimage_bigcup L A B (f: A -> B) (Q: IndexedEnsemble B L) lam:
  InvImage f (BigCup Q lam) = BigCup (fun l => InvImage f (Q l)) lam.
Proof.
apply eq_split => [a [l [H1 H2]]|a [l [H1 H2]]];
  exists l;
  by split.
Qed.

(* 5.4' *)
Theorem invimage_bigcap L A B (f: A -> B) (Q: IndexedEnsemble B L) lam:
  InvImage f (BigCap Q lam) = BigCap (fun l => InvImage f (Q l)) lam.
Proof. apply eq_split => a H1 l H2; by apply H1. Qed.


Inductive Product (T L: Type) (A: IndexedEnsemble T L)
  : Ensemble (L -> T) :=
  | Product_intro: forall (a: forall l: L, T),
      (forall (l: L), a l \in A l) -> (fun l => a l) \in Product A.

(* p.47 *)
Theorem exists_emptyset_to_product_emptyset T L (A: IndexedEnsemble T L):
  (exists l, A l = \emptyset) -> Product A = \emptyset.
Proof.
move=> [l H1].
rewrite emptyset_not_in => _ [a H2].
move: (H2 l).
by rewrite H1.
Qed.

Axiom choice: forall (T L: Type) (A: IndexedEnsemble T L),
  (forall (l: L), A l <> \emptyset) -> Product A <> \emptyset.

Definition Proj T L (l: L): (L -> T) -> T := fun f => f l.


Lemma not_emptyset_exists T A: A <> \emptyset <-> exists a: T, a \in A.
Proof.
rewrite emptyset_not_in.
split => [ Hneq | Hexi ].
- by rewrite exists_iff_not_forall_not.
- case Hexi => x H1 H2.
  by apply H2 in H1.
Qed.

(* S5 定理7(a) *)
Theorem surjective_exists_right_invmap A B (f: A -> B): Surjective f <-> exists s, f \comp s = \I B.
Proof.
split.
- move=> Hsurj.
  have: forall b: B, exists a, a \in InvImage f \{ b } => [b | H1].
    rewrite surjective_exists in Hsurj.
    case (Hsurj b) => a <-.
    by exists a.
  have: exists Ab: IndexedEnsemble A B,
    (forall (b: B), Ab b = InvImage f \{ b }) /\ (forall (b: B), Ab b <> \emptyset) => [| H2].
    exists (fun b => InvImage f \{ b }).
    split => // b.
    rewrite emptyset_not_in => H2.
    case (H1 b) => a.
    by apply H2.
  case H2 => Ab [H2'1 H3].
  apply choice in H3.
  rewrite not_emptyset_exists in H3.
  case H3 => _ [s H3'].
  exists s.
  apply functional_extensionality => b.
  rewrite /Composite /Identity.
  move: (H3' b).
  by rewrite H2'1.
- case => g H.
  apply surjective_composite_surjective with (f := g).
  rewrite H.
  by apply identity_surjective.
Qed.

(* S5 定理7(b) *)
Theorem injective_exists_left_invmap A B (f: A -> B): Injective f <-> exists r, r \comp f = \I A.
Proof.
split.
- move=> Hinj.
  case (classic (exists a: A, True)).
  - case => a _.
    admit.
  - rewrite exists_iff_not_forall_not.
    move=> HA.
    apply NNPP in HA.
    rewrite /Injective in Hinj.
    

  case (classic (A = Empty_set)).
  + move=> Heq.
    subst.
    admit.
  + move=> Hneq.
    Search Empty_set.
    

  have: A => [| a0]. admit.


  (* DateTypesの方のempty_setを使って、更にinversionタクティックを使えば良いらしい？ *)
  move: (iffLR (injective_exists_unique _) Hinj) => Hinj'.
  move: (fun b H => constructive_definite_description _ (Hinj' b H)) => Hsig.
  rewrite /Composite /Identity.
  (* 矛盾させるために仮定を入れたいが、そもそもゴールがB -> Aで仮定を入れられない・・・ *)
  exists (fun b: B =>
    match excluded_middle_informative (b \in ValueRange(MapAsCorr f)) with
    | left H => get_value (Hsig b H)
    | right H => a0
    end).
  rewrite /Composite /Identity.
  apply functional_extensionality => a.
  case excluded_middle_informative.
  + move=> H1.
    apply Hinj.
    by apply get_proof.
  + move=> /valuerange_map_as_corr /exists_iff_not_forall_not /NNPP H2.
    by move: (H2 a).
- case => r H.
  apply injective_composite_injective with (g := r).
  rewrite H.
  by apply identity_injective.
Admitted.

(* S5 系 *)
Corollary injective_surjective A B: (exists f: A -> B, Injective f) <-> (exists g: B -> A, Surjective g).
Proof.
split => [[f Hf] | [g Hg]].
- rewrite injective_exists_left_invmap in Hf.
  case Hf => g Hg.
  exists g.
  rewrite surjective_exists_right_invmap.
  by exists f.
- rewrite surjective_exists_right_invmap in Hg.
  case Hg => f Hf.
  exists f.
  rewrite injective_exists_left_invmap.
  by exists g.
Qed.

(* 問題1は飛ばす。問題2-4はすでに証明済み *)

(* S5 問題5(a) *)
Theorem bigcups_cap_distrib T LA LB (A: IndexedEnsemble T LA) (B: IndexedEnsemble T LB) lamA lamB:
  BigCup A lamA \cap BigCup B lamB = BigCup (fun l => A (fst l) \cap B (snd l)) (lamA * lamB).
Proof.
apply eq_split.
- move=> _ [x [la [HA1 HA2]] [lb [HB1 HB2]]].
  by exists (pair la lb).
- move=> _ [_ [[l HLA HLB] [x HA HB]]].
  split;
    [ exists (fst l) | exists (snd l) ];
    by split.
Qed.

(* S5 問題5(b) *)
Theorem bigcaps_cup_distrib T LA LB (A: IndexedEnsemble T LA) (B: IndexedEnsemble T LB) lamA lamB:
  BigCap A lamA \cup BigCap B lamB = BigCap (fun l => A (fst l) \cup B (snd l)) (lamA * lamB).
Proof.
apply eq_split.
- move=> _ [] x H1 [_ _ [l HA HB]];
    [ left | right ];
    by apply H1.
- move=> x H1.
  rewrite /BigCap /In in H1.
  rewrite bigcap_cup_distrib => la HLA.
  rewrite cup_comm.
  rewrite bigcap_cup_distrib => lb HLB.
  case (H1 (pair la lb)) => // x' H;
    by [ right | left ].
Qed.

(* S5 問題5(c) *)
Theorem bigcups_prod_distrib TA TB LA LB (A: IndexedEnsemble TA LA) (B: IndexedEnsemble TB LB) lamA lamB:
  BigCup A lamA * BigCup B lamB = BigCup (fun l => A (fst l) * B (snd l)) (lamA * lamB).
Proof.
apply eq_split.
- move=> _ [x [la [HLA1 HLA2]] [lb [HLB1 HLB2]]].
  by exists (pair la lb).
- move=> _ [_ [[[la lb] HLA HLB] [x HXA HXB]]].
  split;
    by [ exists la | exists lb ].
Qed.

(* S5 問題5(d) *)
Theorem bigcaps_prod_distrib TA TB LA LB (A: IndexedEnsemble TA LA) (B: IndexedEnsemble TB LB) lamA lamB:
  BigCap A lamA * BigCap B lamB = BigCap (fun l => A (fst l) * B (snd l)) (lamA * lamB).
Proof.
apply eq_split.
- move=> _ [[a b] HA HB] _ [[la lb] HLA HLB].
  split;
    by [ apply HA | apply HB ].
- move=> x H1.
  rewrite /In /BigCap in H1.
  case (classic ((exists la lb, la \in lamA /\ lb \in lamB))) => H2.
  + case H2 => la.
    case => lb.
    case => HLA HLB.
    move: (H1 (pair la lb)).
    move=> H3.
    case H3 => // x' H4 H5.
    clear H1 H3 x.
    split.
    * move=> la' HLA'.
      

  have: x \in BigCap (fun l => A (fst l) * B (snd l)) (lamA * lamB) -> x \in (\bigcap A) lamA * (\bigcap B) lamB.
    clear H1 => H2.
    rewrite /In /BigCap in H2.
    admit.
  apply.
  by rewrite /In /BigCap.

(* 
1. bの存在で場合分け => 失敗
aどうするねん
2. aの存在/\bの存在で場合分け => 失敗
case (classic ((exists la, la \in lamA) /\ (exists lb, lb \in lamB))) => H2. も
case (classic ((exists la lb, la \in lamA /\ lb \in lamB))) => H2. もうまく行かない
3. EnsembleProdの定義を->から/\に => 失敗
 *)


Admitted.

(* 問題6は関数の拡大が必要なので飛ばす *)

(* S5 問題7 *)
Theorem proj_surjective T L (A: IndexedEnsemble T L):
  (forall l: L, A l <> \emptyset)
  -> forall l: L, Surjective (B := T) (Proj l).
Proof.
move=> /choice /not_emptyset_exists [_ [f Hf]] l.
rewrite surjective_exists => b.
by exists (fun _ => b).
Qed.

(* S5 問題8 *)
Theorem product_subset_iff_forall_subset T L (A B: IndexedEnsemble T L):
  (forall l, A l <> \emptyset)
  -> Product A \subset Product B <-> (forall l, A l \subset B l).
Proof.
move=> /choice /not_emptyset_exists [_ [f Hf]].
split.
Admitted.

(* S5 問題9 *)
Theorem product_cap_product T L (A B: IndexedEnsemble T L):
  Product A \cap Product B = Product (fun l => A l \cap B l).
Proof.
apply eq_split.
- move=> _ [x HA HB].
  split => l.
  split.
  + by case HA.
  + by case HB.
- move=> _ [f] H.
  split;
    split => l;
    by case (H l).
Qed.

(* 
S5 問題10はfを定義することが難しそう
Ensemble TA -> Ensemble TBみたいな型が求められる？
 *)

(* S5 問題11 *)
Theorem right_invmap_valuerange_subset_valuerange A B (f: A -> B) (s s': B -> A):
  Surjective f ->
  f \comp s = \I B ->
  f \comp s' = \I B ->
  ValueRange (MapAsCorr s) \subset ValueRange (MapAsCorr s') \/ ValueRange (MapAsCorr s') \subset ValueRange (MapAsCorr s)
  <-> s = s'.
Proof.
move=> Hsurj HI HI'.
split.
- admit.
- move=> H.
  subst.
  by left.


move=> Hsurj HI HI'.
split.
(* wlogとかなんかなかったっけ。それ使いたい *)
- move=> [] Hsubset.
  + apply identity_to_eq with f => //.
    apply functional_extensionality => a.
    rewrite /Identity /Composite.
    move: (Hsubset a).
    case.
    * admit.
    * move=> b.
      rewrite /In /Graph /MapAsCorr /In /fst /snd => H.
      rewrite H.
      s (f (s' b) = s' b
      s b = s' b
      ???????????



  + rewrite surjective_exists in Hsurj.
    apply functional_extensionality => b.
    case (Hsurj b) => a <-.
    clear Hsurj b.
    have: Injective s => [| Hsinj ].
      admit.
    move: (Hsubset a).
    rewrite 2!valuerange_map_as_corr.
    case.
    * exists (f a).
      Search Composite (_ (_ _)) eq.
      admit.
    * move=> b Ha.
      rewrite -Ha.
      Search Composite.
      









Admitted.






End Section1_5.

End Ensemble.