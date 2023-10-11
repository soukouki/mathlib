(* 集合・位相入門(松坂)1 をCoqで証明しつつ読んでいく *)

Set Implicit Arguments.

From mathcomp Require Import ssreflect.

Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.IndefiniteDescription.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import PeanoNat BinIntDef BinInt.
Add LoadPath "." as Local.
Require Import Local.Classical.
Require Local.Ensemble.Section3.
Open Scope ensemble_scope.

Module Ensemble.

Import Section1.Ensemble Section2.Ensemble Section3.Ensemble.

Section Section4.

Implicit Types A B: Type.

(* メモ: Imageが来たら先でexists *)
Definition Image A B (f: A -> B) (P: Ensemble A): Ensemble B :=
  fun b: B => exists a, a \in P /\ f a = b.

(* p.30 *)
Theorem image_defrange_eq_valuerange A B (f: A -> B):
  Image f (FullSet: Ensemble A) = ValueRange (MapAsCorr f).
Proof.
apply eq_split => b.
- case => a.
  case => _ Heq.
  by exists a.
- case => a Hb.
  by exists a.
Qed.

(* p.30 *)
Theorem image_emptyset_iff A B (f: A -> B) P:
  Image f P = \emptyset <-> P = \emptyset.
Proof.
split.
- rewrite emptyset_not_in.
  move=> Himg.
  rewrite emptyset_not_in => a HP.
  apply (Himg (f a)).
  by exists a.
- move=> HP.
  rewrite emptyset_not_in => b.
  case => a.
  case.
  by rewrite HP.
Qed.

Definition InvImage A B (f: A -> B) (Q: Ensemble B): Ensemble A :=
  fun a: A => f a \in Q.

(* p.31 *)
Theorem invimage_fullset A B f:
  InvImage f (FullSet: Ensemble B) = (FullSet: Ensemble A).
Proof.
by apply eq_split => //.
Qed.

(* 4.1 *)
Theorem image_subset A B (f: A -> B) P1 P2:
  P1 \subset P2 -> Image f P1 \subset Image f P2.
Proof.
move=> Hsub b.
case => a.
case => HP1 Heq.
exists a.
split => //.
by apply Hsub.
Qed.

(* 4.2 *)
Theorem image_cup A B (f: A -> B) P1 P2:
  Image f (P1 \cup P2) = Image f P1 \cup Image f P2.
Proof.
apply eq_split.
- move=> b H.
  case H => a'.
  case.
  case => a HP Heq;
    [left | right];
    exists a;
    by split.
- apply subsets_cup;
  apply /image_subset;
  by [apply subset_cup_l | apply subset_cup_r].
Qed.

(* 4.3 *)
Theorem image_cap A B (f: A -> B) P1 P2:
  Image f (P1 \cap P2) \subset Image f P1 \cap Image f P2.
Proof.
apply subsets_cap;
  apply image_subset;
  by [apply cap_subset_l | apply cap_subset_r].
Qed.

(* 4.4 *)
Theorem image_sub A B (f: A -> B) P:
  Image f FullSet - Image f P \subset Image f (FullSet - P).
Proof.
move=> b.
rewrite image_defrange_eq_valuerange.
rewrite sub_iff.
case.
rewrite valuerange_map_as_corr.
case => a.
move=> Heq Hex.
rewrite fullset_sub.
exists a.
split => //.
rewrite compset_in.
move=> Hin.
apply Hex.
exists a.
by split.
Qed.

(* 4.1' *)
Theorem invimage_subset A B (f: A -> B) Q1 Q2:
  Q1 \subset Q2 -> InvImage f Q1 \subset InvImage f Q2.
Proof.
move=> Hsubset a Hinv.
by apply Hsubset.
Qed.

(* 4.2' *)
Theorem invimage_cup A B (f: A -> B) Q1 Q2:
  InvImage f (Q1 \cup Q2) = InvImage f Q1 \cup InvImage f Q2.
Proof.
apply eq_split.
- move=> a H.
  rewrite /InvImage [a \in _]/In in H.
  rewrite -cup_or in H.
  case H => Ha;
    by [left | right].
- apply subsets_cup;
    by [left | right].
Qed.

(* こっちのほうは=で繋がれてて綺麗 *)
(* 4.3' *)
Theorem invimage_cap A B (f: A -> B) Q1 Q2:
  InvImage f (Q1 \cap Q2) = InvImage f Q1 \cap InvImage f Q2.
Proof.
apply eq_split.
- apply subsets_cap => a;
    rewrite /In /InvImage;
    rewrite -cap_and;
    by case.
- move=> a'.
  case => a HQ1 HQ2.
  by split.
Qed.

(* 4.4' *)
Theorem invimage_sub A B (f: A -> B) Q:
  InvImage f (FullSet - Q) = FullSet - InvImage f Q.
Proof.
rewrite 2!fullset_sub.
apply eq_split.
- rewrite /InvImage => a Hin.
  rewrite compset_in => Hout.
  by rewrite {1}/In compset_in in Hin.
- rewrite /InvImage => a.
  rewrite compset_in => Hout.
  by rewrite {1}/In compset_in => Hin.
Qed.

(* 4.5 *)
Theorem invimage_image A B (f: A -> B) P:
  P \subset InvImage f (Image f P).
Proof.
move=> a H.
by exists a.
Qed.

(* 4.5' *)
Theorem image_invimage A B (f: A -> B) Q:
  Image f (InvImage f Q) \subset Q.
Proof.
move=> b.
case => a.
case => H Heq.
by rewrite -Heq.
Qed.

Definition Surjective A B (f: A -> B) := Image f FullSet = FullSet.

Definition Injective A B (f: A -> B) := forall a a', f a = f a' -> a = a'.

Definition Bijective A B (f: A -> B) := Surjective f /\ Injective f.

Lemma surjective_valuerange A B (f: A -> B):
  Surjective f <-> forall b, b \in ValueRange (MapAsCorr f).
Proof.
rewrite /Surjective.
rewrite -eq_fullset.
by rewrite image_defrange_eq_valuerange.
Qed.

(* p.33 *)
Theorem surjective_exists A B (f: A -> B):
  Surjective f <-> forall b, exists a, f a = b.
Proof.
rewrite surjective_valuerange.
split;
  move=> H b;
  by [rewrite -valuerange_map_as_corr | rewrite valuerange_map_as_corr].
    (* 方向が違うだけ *)
Qed.

Lemma injective_uniqueness A B (f: A -> B):
  Injective f <-> forall b, b \in ValueRange (MapAsCorr f) -> uniqueness (fun a => f a = b).
Proof.
split.
- move=> Hinj b Hb.
  rewrite valuerange_map_as_corr in Hb.
  rewrite /uniqueness => a a' Heqa Heqa'.
  apply Hinj.
  by rewrite Heqa Heqa'.
- move=> Hb a a' Heq.
  apply (Hb (f a)) => //.
  rewrite valuerange_map_as_corr.
  by exists a.
Qed.

(* p.33 *)
Theorem injective_exists_unique A B (f: A -> B):
  Injective f <-> forall b, b \in ValueRange (MapAsCorr f) -> exists! a, f a = b.
Proof.
split.
- move=> Hinj b Hexi.
  rewrite -unique_existence.
  split.
  + by rewrite valuerange_map_as_corr in Hexi.
  + apply injective_uniqueness => //.
- rewrite injective_uniqueness.
  move=> H1 b H2.
  case (H1 b H2) => a Huniq.
  case Huniq => Heq H.
  move=> a1 a2 Ha1 Ha2.
  apply eq_stepl with (x := a);
    by apply H.
Qed.

Lemma map_as_corr_injective A B:
  Injective (fun f: A -> B => MapAsCorr f).
Proof.
move=> f f' Hfeq.
apply functional_extensionality => a.
suff: f a \in MapAsCorr f' a.
  move=> H.
  by rewrite /MapAsCorr /In in H.
by rewrite -Hfeq.
Qed.

(* 標準的単射についての話が出てくるけれど、正直当たり前にしか見えないので一旦飛ばす。p33に書いてある。 *)

Lemma invcorr_map_as_corr A B (f: A -> B) (g: B -> A):
  InvCorr (MapAsCorr f) = MapAsCorr g -> forall a, g (f a) = a.
Proof.
move=> Heq a.
remember (f a).
suff: a \in MapAsCorr g b => //.
by rewrite -Heq.
Qed.

Lemma invcorr_map_as_corr' A B (f: A -> B) (g: B -> A):
  InvCorr (MapAsCorr f) = MapAsCorr g -> forall b, f (g b) = b.
Proof.
move=> Heq b.
remember (g b).
suff: b \in MapAsCorr f a => //.
rewrite -[MapAsCorr f]invcorr_twice.
by rewrite Heq.
Qed.

Lemma corr_eq A B (f g: A ->c B):
  (forall a b, b \in f a <-> b \in g a) -> f = g.
Proof.
move=> H.
apply functional_extensionality => a.
apply functional_extensionality => b.
apply propositional_extensionality.
by apply H.
Qed.

(* S4 定理4 前半 *)
Theorem invcorr_is_map_iff_bijective A B (f: A -> B):
  Bijective f <-> (forall gcorr: B ->c A, gcorr = InvCorr (MapAsCorr f) -> exists g, gcorr = MapAsCorr g).
Proof.
split => [| Hg ].
- case => Hsur Hinj g Hgeq.
  have: forall b : B, {x : A | f x = b} => [ b | Hsig ].
    move: (iffLR (surjective_valuerange _) Hsur b) => H1.
    move: (iffLR (injective_exists_unique _) Hinj b H1) => H2.
    apply (constructive_definite_description _ H2).
  exists (fun b => get_value (Hsig b)).
  subst.
  apply corr_eq => b a.
  split => [ Hinv | Hmap ].
  + rewrite /InvCorr /MapAsCorr /In in Hinv.
    rewrite /MapAsCorr /In.
    suff: uniqueness (fun a: A => f a = b).
      move: (get_proof (Hsig b)) => H.
      by apply.
    apply injective_uniqueness => //.
    rewrite valuerange_map_as_corr.
    by exists a.
  + rewrite /MapAsCorr /In in Hmap.
    rewrite /InvCorr /MapAsCorr /In.
    rewrite Hmap.
    by rewrite (get_proof (Hsig b)).
- move: (Hg (InvCorr (MapAsCorr f))).
  case => // g Hinveq.
  move: (invcorr_map_as_corr Hinveq) => Hforall.
  move: (invcorr_map_as_corr' Hinveq) => Hforall'.
  split.
  + rewrite surjective_exists => b.
    by exists (g b).
  + rewrite injective_exists_unique => b Hval.
    exists (g b).
    split => // a Haeq.
    by rewrite -Haeq.
Qed.

(* S4 定理4 後半 *)
Theorem invcorr_bijective A B P (f: A -> B | Bijective f /\ P f):
  {g: B -> A | Bijective g /\ MapAsCorr g = InvCorr (MapAsCorr (get_value f))}.
Proof.
apply constructive_indefinite_description.
case (get_proof f) => Hbij _.
rewrite invcorr_is_map_iff_bijective in Hbij.
case (Hbij (InvCorr (MapAsCorr (get_value f))) eq_refl) => g Hg.
exists g.
split => //.
rewrite invcorr_is_map_iff_bijective => fcorr Hf.
exists (get_value f).
by rewrite -Hg invcorr_twice in Hf.
Qed.

(* InvMapの設計については
https://github.com/itleigns/CoqLibrary/blob/de210b755ab010e835e3777b9b47351972bbb577/Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn1.v#L1268
を参考にした *)

Definition InvMap A B {P} (f: A -> B | Bijective f /\ P f):
  {g: B -> A | Bijective g /\ MapAsCorr g = InvCorr (MapAsCorr (get_value f))}
  := (invcorr_bijective _ f).
Notation "f ^-1" := (InvMap f) (at level 30).

Theorem invmap_eq A B {P} (f: A -> B | Bijective f /\ P f):
  forall a b, get_value (f^-1) b = a <-> (get_value f) a = b.
Proof.
move=> a b.
suff: InvCorr (MapAsCorr (get_value f)) = MapAsCorr (get_value (InvMap f)) => [ H |].
  split => Heq;
  rewrite -Heq;
  by [ apply invcorr_map_as_corr' | apply invcorr_map_as_corr ].
by case (get_proof (invcorr_bijective _ f)).
Qed.

Lemma invmap_bijective A B {P} (f: A -> B | Bijective f /\ P f):
  Bijective (get_value (f^-1)).
Proof.
move: (f^-1) => g.
move: (get_proof g).
by case.
Qed.


Definition Composite A B C (f: A -> B) (g: B -> C): (A -> C) := fun a => g (f a).
Notation "f \comp g" := (Composite g f) (at level 50).

(* S4 定理5a *)
Theorem composite_surjective A B C (f: A -> B) (g: B -> C):
  Surjective f -> Surjective g -> Surjective (g \comp f).
Proof.
rewrite !surjective_exists => Hf Hg c.
case (Hg c) => b Heqc.
case (Hf b) => a Heqb.
exists a.
rewrite /Composite.
by rewrite Heqb.
Qed.

(* S4 定理5b *)
Theorem composite_injective A B C (f: A -> B) (g: B -> C):
  Injective f -> Injective g -> Injective (g \comp f).
Proof.
move=> Hf Hg.
rewrite injective_exists_unique => c Hc.
rewrite valuerange_map_as_corr in Hc.
case Hc => a Ha.
exists a.
split => // a' Ha'.
apply /Hf /Hg.
rewrite /Composite in Ha Ha'.
by rewrite Ha Ha'.
Qed.

(* S4 定理5c *)
Theorem composite_bijective A B C (f: A -> B) (g: B -> C):
  Bijective f -> Bijective g -> Bijective (g \comp f).
Proof.
rewrite /Bijective.
case => Hsurf Hinf.
case => Hsurg Hing.
split.
- by apply composite_surjective.
- by apply composite_injective.
Qed.

(* S4 定理6(1) *)
Theorem composite_assoc A B C D (f: A -> B) (g: B -> C) (h: C -> D):
  (h \comp g) \comp f = h \comp (g \comp f).
Proof. by []. Qed.

(* S4 定理6(2)-1 *)
Theorem composite_identity A B (f: A -> B):
  f \comp \I A = f.
Proof. by []. Qed.

(* S4 定理6(2)-2 *)
Theorem identity_composite A B (f: A -> B):
  \I B \comp f = f.
Proof. by []. Qed.

(* S4 定理6(3)-1 *)
Theorem invmap_composite_identity A B {P} (f: A -> B | Bijective f /\ P f):
  get_value (f^-1) \comp get_value f = \I A.
Proof.
rewrite /Composite /Identity.
apply functional_extensionality => a.
by rewrite invmap_eq.
Qed.

(* S4 定理6(3)-2 *)
Theorem composite_invmap_identity A B P (f: A -> B | Bijective f /\ P f):
  get_value f \comp get_value (f^-1) = \I B.
Proof.
rewrite /Composite /Identity.
apply functional_extensionality => b.
by rewrite -invmap_eq.
Qed.

(* 写像の拡大と縮小についてはいまいちイメージがわかないので後回し *)

(* 特徴関数(CharacteristicFunction)あるいは定義関数(IndicatorFunction)、略してCharにする *)
Definition Char X (A: Ensemble X) (x: X): nat :=
  match excluded_middle_informative (x \in A) with
  | left a => 1
  | right b => 0
  end.

Lemma in_char X (A: Ensemble X) (a: X):
  a \in A <-> Char A a = 1.
Proof.
split;
  rewrite /Char;
  by case excluded_middle_informative.
Qed.

Lemma not_in_char X (A: Ensemble X) (a: X):
  a \notin A <-> Char A a = 0.
Proof.
split;
  rewrite /Char;
  by case excluded_middle_informative.
Qed.

Fact char_fullset X (x: X):
  x \in FullSet -> Char FullSet x = 1.
Proof. by rewrite -in_char. Qed.

Fact char_emptyset X (x: X):
  x \in FullSet -> Char EmptySet x = 0.
Proof. by rewrite -not_in_char not_emptyset. Qed.

Fact char_neq X (A A': Ensemble X):
  A \in PowerSet FullSet -> A' \in PowerSet FullSet -> A <> A'
 -> Char A <> Char A'.
Proof.
move=> HP HP' Hneq Hceq.
apply Hneq.
rewrite -eq_iff => x.
split;
  move=> H;
  rewrite in_char in H;
  [ rewrite Hceq in H | rewrite -Hceq in H ];
  by rewrite -in_char in H.
Qed.

Fact char_eq_func X (f: X -> nat):
  (forall x, f x = 0 \/ f x = 1) ->
  forall A: Ensemble X, A = (fun x => f x = 1) -> Char A = f.
Proof.
move=> Hfor A HAeq.
apply functional_extensionality => x.
case (Hfor x) => H;
  rewrite H;
  [ rewrite -not_in_char | rewrite -in_char ];
  rewrite HAeq.
- rewrite /In => H1.
  by rewrite H1 in H.
- by rewrite /In.
Qed.


(* 問題1、問題2はすでに証明済み *)

(* S4 問題3-1 *)
Theorem invimage_image_injective A B (f: A -> B):
  Injective f -> forall P, P = InvImage f (Image f P).
Proof.
move=> Hinj P.
apply eq_split.
- by apply invimage_image.
- move=> a.
  rewrite {1}/In /InvImage.
  case => a'.
  case => Ha' Heqf.
  suff: a = a' => [ Heq |].
    by rewrite Heq.
  by apply Hinj.
Qed.

(* S4 問題3-2 *)
Theorem image_invimage_surjective A B (f: A -> B):
  Surjective f -> forall Q, Image f (InvImage f Q) = Q.
Proof.
move=> Hsur Q.
apply eq_split.
- by apply image_invimage.
- move=> b Hb.
  rewrite surjective_exists in Hsur.
  case (Hsur b) => a Heq.
  exists a.
  split => //.
  by rewrite -Heq in Hb.
Qed.

(* S4 問題4 *)
Theorem image_cap_injective A B (f: A -> B) (P1 P2: Ensemble A):
  Injective f -> Image f (P1 \cap P2) = Image f P1 \cap Image f P2.
Proof.
move=> Hinj.
apply eq_split.
- by apply image_cap.
- move=> b_.
  case => b HP1 HP2.
  rewrite /In /Image.
  case HP1 => a1.
  case => Ha1 Heq1.
  case HP2 => a2.
  case => Ha2 Heq2.
  suff: a1 = a2 => [ Heq |].
    exists a1.
    split => //.
    split => //.
    by rewrite Heq.
  apply Hinj.
  by rewrite Heq1 Heq2.
Qed.

Lemma func_eq_invmap A B {Q} (f: A -> B) (g: A -> B | Bijective g /\ Q g):
  f = get_value g <-> f \comp get_value (g^-1) = \I B.
Proof.
split => [ Heq | Hi ].
- rewrite Heq.
  by apply composite_invmap_identity.
- rewrite -[get_value g]identity_composite.
  rewrite -Hi.
  rewrite composite_assoc.
  by rewrite invmap_composite_identity.
Qed.

Lemma invmap_twice A B {P} (f: A -> B | Bijective f /\ P f):
  get_value (f ^-1 ^-1) = get_value f.
Proof.
move: (invmap_bijective f) => Hg.
apply functional_extensionality => a.
rewrite invmap_eq.
by rewrite invmap_eq.
Qed.

Lemma composite_sig A B C {P Q} (f: A -> B | Bijective f /\ P f) (g: B -> C | Bijective g /\ Q g):
  {c: A -> C | Bijective c /\ get_value g \comp get_value f = c}.
Proof.
apply constructive_indefinite_description.
exists (get_value g \comp get_value f).
split => //.
- apply composite_bijective.
  + by case (get_proof f).
  + by case (get_proof g).
Qed.

Lemma get_composite_sig_value A B C {P Q} (f: A -> B | Bijective f /\ P f) (g: B -> C | Bijective g /\ Q g):
  get_value (composite_sig f g) = get_value g \comp get_value f.
Proof.
case (get_proof (composite_sig f g)) => _ Heq.
fold get_value in Heq.
by rewrite -Heq.
Qed.

(* S4 問題8 *)
(* (f . g)^-1 = f^-1 . g^-1 *)
Theorem inv_composite_bijective A B C {P Q} (f: A -> B | Bijective f /\ P f) (g: B -> C | Bijective g /\ Q g):
  get_value ((composite_sig f g)^-1) = get_value (f^-1) \comp get_value (g^-1).
Proof.
symmetry.
rewrite func_eq_invmap.
rewrite invmap_twice.
rewrite composite_assoc.
rewrite get_composite_sig_value.
rewrite -[get_value (InvMap g) \comp _]composite_assoc.
rewrite invmap_composite_identity.
rewrite identity_composite.
by rewrite invmap_composite_identity.
Qed.

(* S4 問題9(a) *)
Theorem composite_image A B C (f: A -> B) (g: B -> C) (P: Ensemble A):
  Image (g \comp f) P = Image g (Image f P).
Proof.
apply eq_split => [ c H | c H ].
- case H => a.
  case => H1 H2.
  exists (f a).
  split => //.
  by exists a.
- case H => b.
  case => H1 H2.
  case H1 => a.
  case => H3 H4.
  exists a.
  split => //.
  rewrite /Composite.
  by rewrite H4.
Qed.

(* S4 問題9(b) *)
(* (f . g)^-1 (R) = f^-1 (g^-1 (R)) *)
Theorem composite_inv_image A B C {P Q} (f: A -> B | Bijective f /\ P f) (g: B -> C | Bijective g /\ Q g) (R: Ensemble C):
  Image (get_value ((composite_sig f g)^-1)) R = Image (get_value (f^-1)) (Image (get_value (g^-1)) R).
Proof.
rewrite inv_composite_bijective.
by rewrite composite_image.
Qed.

(* S4 問題10(a) *)
Theorem surjective_composite_surjective A B C (f: A -> B) (g: B -> C):
  Surjective (g \comp f) -> Surjective g.
Proof.
move=> Hsur.
rewrite surjective_exists in Hsur.
rewrite surjective_exists => b.
case (Hsur b) => a Heq.
exists (f a).
by rewrite -Heq.
Qed.

(* S4 問題10(b) *)
Theorem injective_composite_injective A B C (f: A -> B) (g: B -> C):
  Injective (g \comp f) -> Injective f.
Proof.
move=> Hinj.
move=> a1 a2 Heq.
apply Hinj.
rewrite /Composite.
by rewrite Heq.
Qed.

Lemma comp_eq_iff A B C (f: A -> B) (g: B -> C) (h: A -> C):
  g \comp f = h
  -> forall a c, g (f a) = c <-> h a = c.
Proof.
move=> Heq.
by rewrite -Heq.
Qed.

(* S4 問題11 *)
Theorem surjective_composite_eq A B C (f: A -> B) (Hf: Surjective f) (g g': B -> C):
  g \comp f = g' \comp f -> g = g'.
Proof.
move=> Heq.
rewrite surjective_exists in Hf.
apply functional_extensionality => b.
case (Hf b) => a H.
rewrite -H.
by rewrite (comp_eq_iff Heq).
Qed.

(* S4 問題12 *)
Theorem injective_composite_eq A B C (f f': A -> B) (g: B -> C) (Hg: Injective g):
  g \comp f = g \comp f' -> f = f'.
Proof.
move=> Heq.
apply functional_extensionality => a.
apply Hg.
by rewrite (comp_eq_iff Heq).
Qed.

(* S4 問題13(a) *)
Theorem composite_surjective_to_surjective A B C (f: A -> B) (g: B -> C):
  Surjective (g \comp f) -> Injective g -> Surjective f.
Proof.
move=> Hsur Hinj.
rewrite surjective_exists => b.
rewrite surjective_exists in Hsur.
case (Hsur (g b)) => a Ha.
exists a.
apply Hinj.
by rewrite -Ha.
Qed.

(* S4 問題13(b) *)
Theorem composite_injective_to_injective A B C (f: A -> B) (g: B -> C):
  Injective (g \comp f) -> Surjective f -> Injective g.
Proof.
move=> Hinj Hsur b1 b2 Heq.
rewrite surjective_exists in Hsur.
case (Hsur b1) => a1 Ha1.
case (Hsur b2) => a2 Ha2.
subst.
move: (Hinj _ _ Heq) => Ha.
by subst.
Qed.

Section Problem14.

Lemma identity_surjective A: Surjective (\I A).
Proof. rewrite surjective_exists => a; by exists a. Qed.

Lemma identity_injective A: Injective (\I A).
Proof. by []. Qed.

Variable A B: Type.
Variable f: A -> B.
Variable g g': B -> A.

Hypothesis H1: g \comp f = \I A.
Hypothesis H2: f \comp g' = \I B.

(* S4 問題14-1 *)
Theorem identity_to_bijective:
  Bijective f.
Proof.
split.
- apply (surjective_composite_surjective (f := g')).
  rewrite H2.
  apply identity_surjective.
- apply (injective_composite_injective (g := g)).
  by rewrite H1.
Qed.

(* S4 問題14-2 *)
Theorem identity_to_eq:
  g = g'.
Proof.
apply functional_extensionality => b.
case identity_to_bijective => Hfsur Hfinj.
apply Hfinj.
symmetry.
rewrite (comp_eq_iff H2).
have: Injective g => [| Hg ].
  apply (composite_injective_to_injective (f := f)) => //.
  by rewrite H1.
apply Hg.
symmetry.
by rewrite (comp_eq_iff H1).
Qed.

Lemma identity_to_bijective_sig:
  {f': A -> B | Bijective f' /\ f' = f}.
Proof.
exists f.
split => //.
by apply identity_to_bijective.
Qed.

(* S4 問題14-3 *)
(* g = f^-1 *)
Theorem identity_to_invmap:
  g = get_value (identity_to_bijective_sig^-1).
Proof.
case (get_proof (identity_to_bijective_sig^-1)) => _ Heq.
apply map_as_corr_injective.
rewrite Heq.
case (get_proof (identity_to_bijective_sig)) => _ Heq'.
fold get_value in Heq'.
rewrite Heq'.
clear Heq Heq'.
apply corr_eq => b a.
rewrite -in_invcorr.
split => H;
  rewrite H;
  rewrite /In /MapAsCorr;
  symmetry.
- move: H2 => H2'.
  rewrite -identity_to_eq in H2'.
  by rewrite (comp_eq_iff H2').
- by rewrite (comp_eq_iff H1).
Qed.

End Problem14.

Lemma char_return_or X (A: Ensemble X) x:
  Char A x = 1 \/ Char A x = 0.
Proof.
rewrite /Char.
case (excluded_middle_informative) => H;
  by [left | right].
Qed.

Section Problem15.

Lemma sub_not X (A B: Ensemble X):
  (A - B)^c = A^c \cup (A \cap B).
Proof.
rewrite -eq_iff => x.
rewrite compset_in sub_iff.
rewrite Classical.not_and_or.
rewrite cup_comm cap_cup_distrib.
rewrite compset_cup fullset_cap.
rewrite -cup_or [x \in B \/ _]or_comm.
rewrite -3!compset_in.
by rewrite compset_twice.
Qed.

Open Scope nat_scope.

Variable X: Type.

Lemma char_le_1 (A: Ensemble X) x:
  Char A x <= 1.
Proof. case (char_return_or A x) => H; rewrite H; auto. Qed.

(* S4 問題15-1 *)
Theorem char_le_subset (A B: Ensemble X):
  (forall x, Char A x <= Char B x) <-> A \subset B.
Proof.
split => [ Hle x | Hsubset x ].
- rewrite 2!in_char => Hy.
  apply Nat.le_antisymm.
  + apply char_le_1.
  + move: (Hle x).
    by rewrite Hy.
- case (char_return_or B x) => Hb.
  + rewrite Hb.
    by apply char_le_1.
  + rewrite Hb.
    rewrite Nat.le_0_r.
    rewrite -not_in_char in Hb.
    rewrite -not_in_char => Ha.
    by apply /Hb /Hsubset.
Qed.

Variable x: X.

(* S4 問題15(a) *)
Theorem char_cap (A B: Ensemble X):
  Char (A \cap B) x = Char A x * Char B x.
Proof.
case (char_return_or A x) => Ha.
- rewrite Ha Nat.mul_1_l.
  case (char_return_or B x) => Hb.
  + rewrite Hb -in_char.
    rewrite -2!in_char in Ha Hb.
    by split.
  + rewrite Hb -not_in_char => Hcap.
    rewrite -not_in_char in Hb.
    move: Hb.
    by case Hcap.
- rewrite Ha Nat.mul_0_l.
  rewrite -not_in_char => Hcap.
  rewrite -not_in_char in Ha.
  apply Ha.
  by case Hcap.
Qed.

Open Scope nat_scope.

(* S4 問題15(b) *)
Theorem char_cup (A B: Ensemble X):
  Char (A \cup B) x = Char A x + Char B x - Char (A \cap B) x.
Proof.
rewrite char_cap.
case (char_return_or A x) => Ha.
- rewrite Ha Nat.mul_1_l Nat.add_sub.
  rewrite -in_char.
  rewrite -in_char in Ha.
  by left.
- rewrite Ha Nat.add_0_l.
  rewrite Nat.mul_0_l Nat.sub_0_r.
  case (char_return_or B x) => Hb.
  + rewrite Hb.
    rewrite -in_char.
    rewrite -in_char in Hb.
    by right.
  + suff: Char (A \cup B) x = 0 => [ Hcup |].
      by rewrite Hb Hcup.
    rewrite -not_in_char => Hcup.
    rewrite -2!not_in_char in Ha Hb.
    move: Ha Hb.
    by case Hcup.
Qed.

(* S4 問題15(c) *)
Theorem char_comp (A: Ensemble X):
  Char (A^c) x = 1 - Char A x.
Proof.
case (char_return_or A x) => Ha.
- suff: x \notin A^c => [ Hcomp |].
    rewrite not_in_char in Hcomp.
    by rewrite Ha Hcomp.
  rewrite -in_char in Ha.
  by rewrite compset_in.
- suff: x \in A^c => [ Hcomp |].
    rewrite in_char in Hcomp.
    by rewrite Ha Hcomp.
  rewrite -not_in_char in Ha.
  by rewrite compset_in.
Qed.

(* S4 問題15(d) *)
Theorem char_sub (A B: Ensemble X):
  Char (Sub A B) x = Char A x * (1 - Char B x).
Proof.
case (char_return_or A x) => Ha.
- rewrite sub_cap_compset.
  rewrite char_cap.
  rewrite Ha 2!Nat.mul_1_l.
  by rewrite char_comp.
- suff: x \notin (Sub A B) => [ Hsub |].
    rewrite not_in_char in Hsub.
    by rewrite Ha Hsub.
  rewrite -not_in_char in Ha.
  rewrite -compset_in sub_not.
  by left.
Qed.

Open Scope Z_scope.

(* S4 問題15(e) *)
Theorem char_sym_diff (A B: Ensemble X):
  Z.of_nat (Char (A \triangle B) x) = Z.abs (Z.of_nat (Char A x) - Z.of_nat (Char B x)).
Proof.
rewrite /SymmetricDifference.
rewrite char_cup char_cap !char_sub.
case (char_return_or A x) => Ha;
case (char_return_or B x) => Hb; (* 全部展開して4通りに分けて解く *)
by rewrite Ha Hb.
Qed.

End Problem15.

(* 問題16から19はすべて個数が必要なので、Cardinalの定義をするまで一旦飛ばす *)

End Section4.

Notation "f ^-1" := (InvMap f) (at level 30): ensemble_scope.
Notation "f \comp g" := (Composite g f) (at level 50): ensemble_scope.

End Ensemble.

