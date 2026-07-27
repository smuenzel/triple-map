From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Structures.Orders.
From Stdlib Require Import Structures.OrdersFacts.
From Stdlib Require Import Program.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Recdef.
Require Import Program.Tactics.
Require Import Stdlib.Logic.PropExtensionality.
From Equations Require Import Equations.

Module Make ( K : UsualOrderedTypeFull).

Module KFacts := OrderedTypeFacts K.

Inductive t :=
  | Bottom
  | Key (k : K.t)
  | Top
.

Definition compare_k (b : t) (k : K.t) : comparison :=
  match b with
  | Bottom => Lt
  | Key k' => K.compare k' k
  | Top => Gt
  end.

Arguments compare_k !b /.

Definition compare (b1 : t) (b2 : t) : comparison :=
  match b1, b2 with
  | Key k1, b2 => CompOpp (compare_k b2 k1)
  | b1, Key k2 => compare_k b1 k2
  | Bottom, Bottom => Eq
  | Bottom, _ => Lt
  | _, Bottom => Gt
  | Top, Top => Eq
  end.

Arguments compare !b1 !b2 /.

Definition lt (b1 : t) (b2 : t) : Prop := compare b1 b2 = Lt.

Arguments lt !b1 !b2 /.

Definition ValidBounds (lo : t) (hi : t) : Prop :=
  match compare lo hi with
  | Lt => True
  | Eq => True
  | Gt => False
  end.

Ltac compare_smash :=
  match goal with
  | [|- context [ K.compare ?a ?b ] ] =>
    destruct (K.compare_spec a b);
    try trivial; try contradiction; try KFacts.order
  | [ H : context [ K.compare ?a ?b ] |- _ ] =>
    destruct (K.compare_spec a b);
    try trivial; try contradiction; try KFacts.order
end.

Ltac compare_smash' :=
  unfold compare, compare_k in *; compare_smash.


Lemma ValidBoundsTrans (lo1 : t) (hi1 : t) (lo2 : t) (hi2 : t) :
  ValidBounds lo1 hi1 -> ValidBounds lo2 hi2 -> (compare lo1 lo2 <> Gt) -> (compare hi1 hi2 <> Gt) -> ValidBounds lo1 hi2.
Proof.
  intros.
  unfold ValidBounds in *.
  unfold compare,compare_k in *.
  destruct lo1, lo2, hi1, hi2; auto; try compare_smash; simpl in *; auto.
  repeat compare_smash.
Qed.

Definition Bounded (lo : t) (k : K.t) (hi : t) : Prop :=
  match compare_k lo k, compare_k hi k with
  | Lt, Gt => True
  | _, _ => False
  end.


Lemma compare_k_Key (k1 : K.t) (k2 : K.t) :
  compare_k (Key k1) k2 = K.compare k1 k2.
Proof.
  simpl. auto.
Qed.

Lemma BoundedHi (lo : t) (k : K.t) (kHi : K.t) :
  Bounded lo k (Key kHi) -> K.lt k kHi.
Proof.
  unfold Bounded. unfold compare_k. destruct (K.compare_spec kHi k).
  - destruct lo; intros; try contradiction. destruct (K.compare_spec k0 k); contradiction.
  - destruct lo; intros; try contradiction; destruct (K.compare_spec k0 k); contradiction.
  - destruct lo.
    + auto.
    + destruct (K.compare_spec k0 k); auto.
    + auto.
Qed.

Lemma BoundedLo (kLo : K.t) (k : K.t) (hi : t) :
  Bounded (Key kLo) k hi -> K.lt kLo k.
Proof.
  unfold Bounded. unfold compare_k. destruct (K.compare_spec kLo k).
  - destruct hi; intros; try contradiction.
  - destruct hi; intros; try contradiction; try destruct (K.compare_spec k0 k); try contradiction.
    + KFacts.order.
    + KFacts.order.
  - intros. contradiction.
Qed.

Lemma BoundedIsValid (lo : t) (k : K.t) (hi : t) :
  Bounded lo k hi -> ValidBounds lo hi.
Proof.
  destruct hi eqn:ehi.
  - destruct lo eqn:elo;
    unfold Bounded in *;
    simpl; auto.
    + unfold ValidBounds; simpl; auto.
    + compare_smash.
  - pose proof BoundedHi lo k k0. intros. 
    specialize (H H0) as hiBound.
    destruct lo eqn:elo;
    unfold ValidBounds;
    unfold Bounded in *;
    unfold compare in *;
    simpl in *; auto;
    repeat compare_smash.
  - destruct lo eqn:elo;
    unfold ValidBounds;
    unfold Bounded in *;
    unfold compare in *;
    unfold compare_k in *;
    repeat compare_smash; auto.
Qed.

Definition TBound : Type := option (t * t).

Definition lower (b : TBound) := match b with Some (lo, _) => Some lo | None => None end.
Definition upper (b : TBound) := match b with Some (_, hi) => Some hi | None => None end.

Definition ValidTBound (b : TBound) : Prop :=
  match b with
  | None => True
  | Some (lo, hi) => ValidBounds lo hi
  end.

Definition MergeT (b1 : TBound) (b2 : TBound) : TBound :=
  match b1, b2 with
  | None, _ => b2
  | _, None => b1
  | Some (lo1, hi1), Some (lo2, hi2) =>
    let lo' := match compare lo1 lo2 with
              | Lt => lo1
              | Gt => lo2
              | Eq => lo1
              end in
    let hi' := match compare hi1 hi2 with
              | Lt => hi2
              | Gt => hi1
              | Eq => hi1
              end in
    Some (lo', hi')
  end.

Lemma MergeTCommutative (b1 : TBound) (b2 : TBound) : MergeT b1 b2 = MergeT b2 b1.
Proof.
  unfold MergeT.
  destruct b1, b2.
  all: auto.
  all: try destruct p.
  - destruct p0. unfold compare. destruct t0, t2, t1, t3; auto.
    all: unfold compare_k; repeat compare_smash; simpl.
    all: unfold ValidBounds in *; unfold compare, compare_k in *; repeat compare_smash.
    all: subst; try easy.
  - easy.
  - easy.
Qed.

Lemma MergeTAssociative (b1 : TBound) (b2 : TBound) (b3 : TBound) : MergeT (MergeT b1 b2) b3 = MergeT b1 (MergeT b2 b3).
Proof.
  unfold MergeT.
  destruct b1, b2, b3.
  all: unfold MergeT in *.
  all:unfold MergeT; try destruct p; try destruct p0; try destruct p1; auto.
  unfold compare, compare_k in *.
  all: destruct t0, t2; try easy.
  all: destruct t1, t3; try easy.
  all: destruct t4, t5; try easy.
  all: repeat compare_smash; simpl.
  all: repeat compare_smash; simpl.
Qed.

Module TB.
(* TBound bundled with proof of validity *)
Record t :=
  { tb : TBound
  ; valid : ValidTBound tb
  }.

Derive NoConfusion for t.

Lemma ext (b1 : t) (b2 : t) (H : tb b1 = tb b2) : b1 = b2.
Proof.
  destruct b1, b2.
  cbn in *. subst. 
  f_equal.
  apply proof_irrelevance.
Qed.

Program Definition empty : t := {| tb := None; valid := _ |}.

Definition is_empty (b : t) : Prop := tb b = None.

Program Definition key (k : K.t) : t := {| tb := Some (Key k, Key k); valid := _ |}.
Final Obligation.
  unfold ValidBounds. simpl. now compare_smash.
Qed.

Program Definition key2 (k1 : K.t) (k2 : K.t) (H : K.le k1 k2) : t := {| tb := Some (Key k1, Key k2); valid := _ |}.
Final Obligation.
  unfold ValidBounds. simpl. compare_smash; simpl; auto. 
  rewrite K.le_lteq in *.
  destruct H; try KFacts.order.
Qed.

Definition lower (b : t) := match tb b with Some (lo, _) => Some lo | None => None end.

Definition upper (b : t) := match tb b with Some (_, hi) => Some hi | None => None end.

Program Definition merge (b1 : t) (b2 : t) : t :=
  {| tb := MergeT (tb b1) (tb b2); valid := _ |}.
Final Obligation.
  epose proof (TB.valid b1).
  epose proof (TB.valid b2).
  unfold ValidTBound, MergeT in *.
  destruct (tb b1), (tb b2).
  all: auto.
  all: try destruct p.
  - destruct p0. unfold compare. destruct t0, t2, t1, t3; auto.
    all: unfold compare_k; repeat compare_smash; simpl.
    all: unfold ValidBounds in *; unfold compare, compare_k in *; repeat compare_smash.
  - auto.
Qed.

Definition mergeT_valid (b1 b2 : TBound) (H1 : ValidTBound b1) (H2 : ValidTBound b2) :
  ValidTBound (MergeT b1 b2) :=
  valid (merge {| tb := b1; valid := H1 |} {| tb := b2; valid := H2 |}).

Lemma MergeCommutative (b1 : t) (b2 : t) : merge b1 b2 = merge b2 b1.
Proof.
  unfold merge.
  apply ext. simpl.
  destruct (tb b1), (tb b2).
  all:unfold MergeT; try destruct p; try destruct p0; auto.
  unfold compare, compare_k in *.
  destruct t0, t2, t1, t3; auto.
  all: repeat compare_smash; simpl.
  all: now subst.
Qed.

Lemma MergeAssociative (b1 : t) (b2 : t) (b3 : t) : merge (merge b1 b2) b3 = merge b1 (merge b2 b3).
Proof.
  unfold merge.
  apply ext. simpl.
  destruct (tb b1), (tb b2), (tb b3).
  all: unfold MergeT in *.
  all:unfold MergeT; try destruct p; try destruct p0; try destruct p1; auto.
  unfold compare, compare_k in *.
  all: destruct t0, t2; try easy.
  all: destruct t1, t3; try easy.
  all: destruct t4, t5; try easy.
  all: repeat compare_smash; simpl.
  all: repeat compare_smash; simpl.
Qed.

Lemma MergeIdentity (b : t) : merge b empty = b.
Proof.
  unfold merge.
  apply ext. simpl.
  unfold MergeT.
  destruct (tb b).
  now destruct p.
  reflexivity.
Qed.

Definition merge3 (b1 : t) (b2 : t) (b3 : t) : t :=
  merge (merge b1 b2) b3.

Definition lt_with_empty (b1 : t) (b2 : t) : Prop :=
  match tb b1, tb b2 with
  | None, _ => True
  | _, None => True
  | Some (lo1, hi1), Some (lo2, hi2) => lt hi1 lo2
  end.

Definition contained_in (b1 : t) (b2 : t) : Prop :=
  match tb b1, tb b2 with
  | None, _ => True
  | _, None => False
  | Some (lo1, hi1), Some (lo2, hi2) =>
      match compare lo1 lo2, compare hi1 hi2 with
      | Lt, _ => False
      | _, Gt => False
      | _, _ => True
      end
  end.

Definition key_contained_in (k : K.t) (b : t) : Prop :=
  contained_in (key k) b.

Lemma contained_in_Reflexive (b : t) : contained_in b b.
Proof.
  unfold contained_in.
  destruct b. cbn.
  destruct tb0; auto.
  destruct p.
  unfold compare, compare_k in *.
  destruct t0, t1; auto.
  all: repeat compare_smash.
  now simpl.
Qed.

Lemma contained_in_Transitive (b1 : t) (b2 : t) (b3 : t) :
  contained_in b1 b2 -> contained_in b2 b3 -> contained_in b1 b3.
Proof.
  intros.
  unfold contained_in in *.
  destruct b1, b2, b3.
  cbn in *.
  destruct tb0, tb1, tb2; auto.
  all: destruct p.
  all: try destruct p0, p1.
  all: unfold ValidTBound, ValidBounds in *.
  all: unfold compare, compare_k in *.
  all: destruct t0, t1; try easy.
  all: try destruct t2, t3; try easy.
  all: try destruct t4, t5; try easy.
  all: simpl in *.
  all: repeat compare_smash.
  all: try destruct p0; auto.
Qed.

Definition lower_Lower (b : t) (lb : K.t) : 
  forall k : K.t, lower b = Some (Key lb) -> lb <> k -> key_contained_in k b -> K.lt lb k.
Proof.
  intros.
  unfold lower, key_contained_in, contained_in, key, compare, compare_k in *.
  cbn in *.
  destruct b.
  cbn in *.
  destruct tb0; try destruct p;  try destruct t0; try destruct t1.
  all: repeat compare_smash.
  all: simpl in *.
  all: subst; try easy.
  all: inversion H; now subst.
Qed.

Lemma MergeBetween (b1 : t) (b2 : t) (b3 : t) :
  lt_with_empty b1 b2 -> lt_with_empty b2 b3 -> not (is_empty b1) -> not (is_empty b3) -> contained_in b2 (merge b1 b3).
Proof.
  intros.
  unfold is_empty in *.
  unfold contained_in.
  unfold lt_with_empty in *.
  unfold lt in *.
  unfold compare in *.
  unfold compare_k in *.
  destruct b1,b2,b3.
  simpl in *.
  unfold ValidTBound in *.
  unfold ValidBounds in *.
  destruct tb0 eqn:etb0, tb1 eqn:etb1, tb2 eqn:etb2.
  all: try destruct p.
  all: try destruct p0.
  all: try destruct p1.
  all: simpl in *.
  all: try destruct t1, t2, t3.
  all: try easy.
  all: try destruct t4.
  all: try easy.
  all: unfold compare, compare_k in *.
  all: destruct t0; try easy; try destruct t5; try easy.
  all: repeat compare_smash; simpl in *; try easy.
  all: repeat compare_smash.
Qed. 

Lemma containedMerge (bC : t) (b1 : t) (b2 : t) :
  contained_in bC b1 \/ contained_in bC b2 -> contained_in bC (merge b1 b2).
Proof.
  intros.
  destruct H.
  all: unfold contained_in in *.
  all: destruct bC, b1, b2; cbn in *; destruct tb0, tb1, tb2; try destruct p; auto.
  all: try destruct p0; cbn; try destruct p1.
  all: unfold compare, compare_k in *.
  all: destruct t0, t2, t1, t3.
  all: auto.
  all: try destruct t4, t5; auto.
  all: try compare_smash; simpl in *.
  all: try easy.
  all: try compare_smash; simpl in *; try easy.
  all: compare_smash; simpl in *.
  all: compare_smash; simpl in *; try easy.
  all: compare_smash; simpl in *; try easy.
  all: compare_smash; simpl in *; try easy.
Qed.

Lemma containedMerge3 (bC : t) (b1 : t) (b2 : t) (b3 : t) :
   contained_in bC b1 \/ contained_in bC b2 \/ contained_in bC b3 -> contained_in bC (merge3 b1 b2 b3).
Proof.
  intros.
  unfold merge3.
  apply containedMerge. intuition.
  - left. apply containedMerge. now left.
  - left. apply containedMerge. now right.
Qed.

Lemma LtContained1 (b1 : t) (b2 : t) :
  lt_with_empty b1 b2 -> (forall b' : t, contained_in b' b1 -> lt_with_empty b' b2).
Proof.
  intros LT b' C.
  destruct b1, b2, b'.
  unfold lt_with_empty, contained_in in *.
  cbn in *.
  destruct tb0, tb1, tb2; try destruct p; try destruct p0; try destruct p1; auto.
  all: unfold compare, compare_k in *.
  all: destruct t0, t2, t1, t3; cbn; try easy.
  all: destruct t4, t5; try easy.
  all: repeat compare_smash; simpl in *.
  all: repeat compare_smash.
  all: simpl in *; try easy.
Qed.

Lemma LtContained2 (b1 : t) (b2 : t) :
  lt_with_empty b1 b2 -> (forall b' : t, contained_in b' b2 -> lt_with_empty b1 b').
Proof.
  intros LT b' C.
  destruct b1, b2, b'.
  unfold lt_with_empty, contained_in in *.
  cbn in *.
  destruct tb0, tb1, tb2; try destruct p; try destruct p0; try destruct p1; auto.
  all: unfold compare, compare_k in *.
  all: destruct t0, t2, t1, t3; cbn; try easy.
  all: destruct t4, t5; try easy.
  all: repeat compare_smash; simpl in *.
  all: repeat compare_smash.
  all: simpl in *; try easy.
Qed.


End TB.


End Make.

