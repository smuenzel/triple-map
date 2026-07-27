From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Structures.Orders.
From Stdlib Require Import Structures.OrdersFacts.
From Stdlib Require Import Program.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Recdef.
From Stdlib Require Import Decidable.
From Stdlib Require Import Compare_dec.
From Stdlib Require Import List Relations Relations_1 Sorted.
From Stdlib Require Import Logic.PropExtensionality.
Require Import Program.Tactics.
From Stdlib Require Import List.
Import ListNotations.
From Equations Require Import Equations.
From Equations.Prop Require Import Logic.
From Balanced Require Import bound.
From Balanced Require Import triple0.
From Corelib Require Extraction.
From Ltac2 Require Import Ltac2 String.
From stdpp Require Import sorting.
Set Default Proof Mode "Classic".


Set Printing Projections.
Module Balanced ( K : UsualOrderedTypeFull ).

Include triple0.Balanced(K).

Module Bound := bound.Make(K).

Definition notEmpty {V : Type} (T : Tree V) : Prop := T <> Empty.
Definition isNode {V : Type} (T : Tree V) : Prop :=
  match T with
  | Node _ _ _ _ _ => True
  | _ => False
  end.

Fixpoint max_binding {V : Type} (T : Tree V) : option (K.t * V) :=
  match T with
  | Empty => None
  | V1 k v => Some (k, v)
| V2 k11 v11 k1 v1 => Some (k1, v1)
  | V3 k11 v11 k1 v1 k12 v12 => Some (k12, v12)
  | Node _ l k v r => max_binding r
  end.

Definition max_key {V : Type} (T : Tree V) : option K.t :=
  match max_binding T with
  | Some (k, v) => Some k
  | None => None
end.

Fixpoint min_binding {V : Type} (T : Tree V) : option (K.t * V) :=
  match T with
  | Empty => None
  | V1 k v => Some (k, v)
  | V2 k11 v11 k1 v1 => Some (k11, v11)
  | V3 k11 v11 k1 v1 k12 v12 => Some (k11, v11)
  | Node _ l k v r => min_binding l
  end.

Definition min_key {V : Type} (T : Tree V) : option K.t :=
match min_binding T with
  | Some (k, v) => Some k
  | None => None
  end.

Fixpoint TreeBound {V : Type} (T : Tree V) : Bound.TBound :=
match T with
  | Empty => None
  | V1 k v => Some (Bound.Key k, Bound.Key k)
  | V2 k11 v11 k1 v1 => Some (Bound.Key k11, Bound.Key k1)
  | V3 k11 v11 k1 v1 k12 v12 => Some (Bound.Key k11, Bound.Key k12)
  | Node _ l k v r =>
      let lb := TreeBound l in
let rb := TreeBound r in
      Bound.MergeT lb (Bound.MergeT (Some (Bound.Key k, Bound.Key k)) rb)
  end.

Definition Ordered {V : Type} (T : Tree V) : Prop :=
match T with
  | Empty => True
  | V1 _ _ => True
  | V2 k11 v11 k1 v1 => K.lt k11 k1
  | V3 k11 v11 k1 v1 k12 v12 => K.lt k11 k12 /\ K.lt k11 k1 /\ K.lt k1 k12
  | Node _ l k _ r =>
      let key := Bound.Key k in
      let lb := TreeBound l in
      let rb := TreeBound r in
      match lb, rb with
      | None, None => True
      | Some (lb, ub), None => Bound.lt ub key
      | None, Some (lb, ub) => Bound.lt key lb
      | Some (lb1, ub1), Some (lb2, ub2) => Bound.lt ub1 key /\ Bound.lt key lb2
      end
  end.

Definition WellBalancedOrdered {V : Type} :=
  Eval simpl in (WellBalanced (V:=V)) ++ [ Ordered ].  

Definition WellFormedOrdered {V : Type} :=
  Eval simpl in (WellFormedStruct (V:=V)) ++ [ Ordered ].

Lemma OrderedValidTreeBound {V : Type} (T : Tree V) (ord : Property [ Ordered ] T) :
  Bound.ValidTBound (TreeBound T).
Proof.
  epose proof (Property_This' ord) as orT.
  unfold Bound.ValidTBound.
  induction T; inversion ord.
  - now compute.
  - compute. Bound.compare_smash.
  - compute. unfold Ordered in orT. Bound.compare_smash.
  - compute. unfold Ordered in orT.
    destruct_conjs.
    Bound.compare_smash.
  - epose proof (Property_This' Hl) as HordT1.
    epose proof (Property_This' Hr) as HordT2.
    specialize (IHT1 Hl HordT1).
    specialize (IHT2 Hr HordT2).
    simpl.
    exact (Bound.TB.mergeT_valid _ _ IHT1
             (Bound.TB.mergeT_valid _ _
               (Bound.TB.valid (Bound.TB.key t))
               IHT2)).
Qed.

Program Definition TreeTB {V : Type} {Ps : list PropF} {il : InList Ordered Ps }  (T : Tree V) (ord : Property Ps T) : Bound.TB.t :=
  {| Bound.TB.tb := TreeBound T; Bound.TB.valid := _ |}.
Final Obligation. intros. epose proof (Property_In Ordered ord _). now apply OrderedValidTreeBound. Qed.

(*
Lemma TreeBoundNodeOrdered {V : Type} (n : nat) (T1 : Tree V) (k : K.t) (v : V) (T2 : Tree V)
  (ord : Property [Ordered] (Node n T1 k v T2))
  (ord_l : Property [Ordered] T1) (ord_r : Property [Ordered] T2)
  :
  Bound.TB.lt_with_empty (TreeTB T1 ord_l) (TreeTB T2 ord_r).
Proof.
 *)

Inductive BoundedTree {V : Type} (tb : Bound.TB.t) : Tree V -> Prop :=
  | BT_Empty : BoundedTree tb Empty
  | BT_V1 (k : K.t) (v : V)
    :  Bound.TB.key_contained_in k tb
    -> BoundedTree tb (V1 k v)
  | BT_V2 (k11 : K.t) (v11 : V) (k1 : K.t) (v1 : V)
    :  Bound.TB.key_contained_in k11 tb
    -> Bound.TB.key_contained_in k1 tb
    -> BoundedTree tb (V2 k11 v11 k1 v1)
  | BT_V3 (k11 : K.t) (v11 : V) (k1 : K.t) (v1 : V) (k12 : K.t) (v12 : V)
    :  Bound.TB.key_contained_in k11 tb
    -> Bound.TB.key_contained_in k1 tb
    -> Bound.TB.key_contained_in k12 tb
    -> BoundedTree tb (V3 k11 v11 k1 v1 k12 v12)
  | BT_Node (n : nat) (l : Tree V) (tbl : Bound.TB.t) (k : K.t) (v : V) (r : Tree V) (tbr : Bound.TB.t)
    :  Bound.TB.key_contained_in k tb
    -> BoundedTree tbl l
    -> BoundedTree tbr r
    -> (Bound.TB.merge3 tbl (Bound.TB.key k) tbr = tb)
    -> Bound.TB.lt_with_empty tbl (Bound.TB.key k)
    -> Bound.TB.lt_with_empty (Bound.TB.key k) tbr
    -> BoundedTree tb (Node n l k v r)
      .

Inductive BoundedTreeTight {V : Type} : Tree V -> Bound.TB.t -> Prop :=
  | BTT_Empty : BoundedTreeTight Empty Bound.TB.empty
  | BTT_V1 (k : K.t) (v : V)
    : BoundedTreeTight (V1 k v) (Bound.TB.key k)
  | BTT_V2 (k11 : K.t) (v11 : V) (k1 : K.t) (v1 : V)
    : BoundedTreeTight (V2 k11 v11 k1 v1) (Bound.TB.merge (Bound.TB.key k11) (Bound.TB.key k1))
  | BTT_V3 (k11 : K.t) (v11 : V) (k1 : K.t) (v1 : V) (k12 : K.t) (v12 : V)
    : BoundedTreeTight (V3 k11 v11 k1 v1 k12 v12) (Bound.TB.merge3 (Bound.TB.key k11) (Bound.TB.key k1) (Bound.TB.key k12))
  | BTT_Node (n : nat) (l : Tree V) {tbl : Bound.TB.t} (k : K.t) (v : V) (r : Tree V) {tbr : Bound.TB.t}
     (left_bound : BoundedTreeTight l tbl)
     (right_bound : BoundedTreeTight r tbr)
     :  Bound.TB.lt_with_empty tbl (Bound.TB.key k)
     -> Bound.TB.lt_with_empty (Bound.TB.key k) tbr
     -> BoundedTreeTight (Node n l k v r) (Bound.TB.merge3 tbl (Bound.TB.key k) tbr)
.

Lemma BTT_is_TreeTB {V : Type} {Ps : list PropF} {il : InList Ordered Ps } (T : Tree V) (ps : Property Ps T) :
  forall (tb : Bound.TB.t), BoundedTreeTight T tb -> TreeTB T ps = tb.
Proof.
  intros.
  epose proof (Property_In Ordered ps _) as ord.
  induction H.
  - unfold TreeTB, Bound.TB.empty. f_equal; apply proof_irrelevance.
  - unfold TreeTB, Bound.TB.key. f_equal; apply proof_irrelevance.
  - unfold TreeTB, TreeBound, Bound.TB.merge. simpl.
    epose proof (Property_This' ord) as ord'.
    simpl in ord'.
    apply Bound.TB.ext. cbn.
    Bound.compare_smash.
  - unfold TreeTB, TreeBound, Bound.TB.merge3. simpl.
    epose proof (Property_This' ord) as ord'.
    simpl in ord'.
    destruct_conjs.
    apply Bound.TB.ext. cbn.
    repeat (Bound.compare_smash; simpl).
  - inversion ps.
    inversion ord.
    subst.
    specialize (IHBoundedTreeTight1 Hl Hl0).
    specialize (IHBoundedTreeTight2 Hr Hr0).
    rewrite <-IHBoundedTreeTight1.
    rewrite <-IHBoundedTreeTight2.
    unfold TreeTB.
    rewrite <-IHBoundedTreeTight1 in H1.
    rewrite <-IHBoundedTreeTight2 in H2.
    cbn.
    unfold Bound.TB.merge3.
    unfold Bound.TB.merge.
    apply Bound.TB.ext; cbn.
    unfold Bound.TB.lt_with_empty in H1, H2.
    cbn in H2.
    cbn in H1.
    unfold Bound.MergeT.
    unfold Bound.lt, Bound.compare, Bound.compare_k in *.
    
    destruct (TreeBound l) eqn:eTL.
    all: try destruct p.
    all: destruct (TreeBound r) eqn:eTR.
    all: try destruct p.
    all: try destruct t.
    all: try destruct t1.
    all: try destruct t2.
    all: try destruct t0.
    all: cbn; auto.
    all: Bound.compare_smash; cbn; Bound.compare_smash; cbn; Bound.compare_smash; cbn; subst.
    all: try rewrite KFacts.compare_refl.
    all: cbn; auto.
    all: Bound.compare_smash; cbn; try rewrite KFacts.compare_refl; cbn; auto.
    all: Bound.compare_smash; cbn; try rewrite KFacts.compare_refl; cbn; auto.
    all: Bound.compare_smash; cbn; try rewrite KFacts.compare_refl; cbn; auto.
    all: Bound.compare_smash; cbn; try rewrite KFacts.compare_refl; cbn; auto.
    all: Bound.compare_smash; cbn; try rewrite KFacts.compare_refl; cbn; auto.
Qed.
    


Lemma TreeTB_Node {V : Type} {Ps : list PropF} {il : InList Ordered Ps}
  (n : nat) (T1 : Tree V) (k : K.t) (v : V) (T2 : Tree V)
  (ord : Property Ps (Node n T1 k v T2))
  (Hl : Property Ps T1) (Hr : Property Ps T2) :
  TreeTB (Node n T1 k v T2) ord = Bound.TB.merge3 (TreeTB T1 Hl) (Bound.TB.key k) (TreeTB T2 Hr).
Proof.
  unfold Bound.TB.merge3, Bound.TB.merge.
  apply Bound.TB.ext. cbn [Bound.TB.tb].
  unfold TreeTB. cbn [Bound.TB.tb].
  unfold Bound.TB.key. cbn [Bound.TB.tb].
  now rewrite Bound.MergeTAssociative.
Qed.

Definition BoundedOrderedTight {V : Type} (T : Tree V) (ord : Property [ Ordered ] T) : BoundedTreeTight T (TreeTB T ord) .
Proof.
  epose proof (Property_This' ord) as ord'.
  induction T.
  - assert (TreeTB Empty ord = Bound.TB.empty). shelve.
    rewrite H. constructor.
    Unshelve.
    unfold TreeTB, Bound.TB.empty; f_equal; apply proof_irrelevance.
  - assert (TreeTB (V1 t v) ord = Bound.TB.key t). shelve.
    rewrite H. constructor.
    Unshelve.
    unfold TreeTB, Bound.TB.key; f_equal; apply proof_irrelevance.
  - assert (TreeTB (V2 t v t0 v0) ord = Bound.TB.merge (Bound.TB.key t) (Bound.TB.key t0)). shelve.
    rewrite H. constructor.
    Unshelve.
    unfold TreeTB, Bound.TB.merge; cbn.
    unfold Ordered in ord'.
    apply Bound.TB.ext; cbn.
    Bound.compare_smash.
  - assert (TreeTB (V3 t v t0 v0 t1 v1) ord = Bound.TB.merge3 (Bound.TB.key t) (Bound.TB.key t0) (Bound.TB.key t1)). shelve.
    rewrite H. constructor.
    Unshelve.
    unfold TreeTB, Bound.TB.merge3, Bound.TB.merge; cbn.
    apply Bound.TB.ext; cbn.
    unfold Ordered in ord'; destruct_conjs.
    repeat Bound.compare_smash. simpl.
    repeat Bound.compare_smash.
  - inversion ord. subst.
    assert (TreeTB (Node n T1 t v T2) ord = Bound.TB.merge3 (TreeTB T1 Hl) (Bound.TB.key t) (TreeTB T2 Hr)).
    shelve.
    rewrite H. constructor.
    + epose proof (Property_This' Hl) as Hl'.
      epose proof (Property_This' Hr) as Hr'.
      intuition.
    + epose proof (Property_This' Hl) as Hl'.
      epose proof (Property_This' Hr) as Hr'.
      intuition.
    Unshelve.
    exact (TreeTB_Node n T1 t v T2 ord Hl Hr).
    + specialize (Property_This' Hl) as Hl';
      specialize (Property_This' Hr) as Hr';
      specialize (IHT1 Hl Hl');
      specialize (IHT2 Hr Hr');
      unfold Ordered in ord';
      unfold Bound.TB.lt_with_empty;
      unfold TreeTB;
      cbn;
      destruct (TreeBound T1) eqn:TNT1; auto;
      destruct (TreeBound T2) eqn:TNT2; auto;
      destruct p;
      unfold Bound.lt, Bound.compare, Bound.compare_k in *;
      destruct_conjs;
      destruct t1; auto.
    + specialize (Property_This' Hl) as Hl';
      specialize (Property_This' Hr) as Hr'.
      specialize (IHT1 Hl Hl').
      specialize (IHT2 Hr Hr').
      unfold Ordered in ord'.
      unfold Bound.TB.lt_with_empty.
      unfold TreeTB.
      cbn.
      destruct (TreeBound T1) eqn:TNT1; auto.
      destruct (TreeBound T2) eqn:TNT2; auto.
      destruct p.
      unfold Bound.lt, Bound.compare, Bound.compare_k in *.
      destruct_conjs.
      destruct t1; auto.
Defined.

Definition BoundedOrdered {V : Type} (T : Tree V) (ord : Property [ Ordered ] T) : BoundedTree (TreeTB T ord) T.
Proof.
  epose proof (Property_This' ord) as ord'.
  induction T.
  - constructor.
  - constructor. cbn. Bound.compare_smash.
  - constructor; cbn; repeat Bound.compare_smash; simpl in *; auto; KFacts.order.
  - constructor; cbn; repeat Bound.compare_smash; simpl in *; auto; destruct_conjs; KFacts.order.
  - inversion ord. subst.
    epose proof (OrderedValidTreeBound _ ord) as valid_ord.
    epose proof (OrderedValidTreeBound _ Hl) as valid_l.
    epose proof (OrderedValidTreeBound _ Hr) as valid_r.
    epose proof (Property_This' Hl) as Hl'.
    epose proof (Property_This' Hr) as Hr'.
    specialize (IHT1 Hl Hl').
    specialize (IHT2 Hr Hr').
    constructor 5 with (tbl := TreeTB T1 Hl) (tbr := TreeTB T2 Hr).
    all: auto.
    * rewrite (TreeTB_Node n T1 t v T2 ord Hl Hr).
      unfold Bound.TB.key_contained_in.
      apply Bound.TB.containedMerge3. right. left.
      apply Bound.TB.contained_in_Reflexive.
    * symmetry. exact (TreeTB_Node n T1 t v T2 ord Hl Hr).
    * unfold Ordered in ord'.
      unfold Bound.TB.lt_with_empty.
      unfold TreeTB.
      cbn.
      destruct (TreeBound T1) eqn:TNT1; auto.
      destruct p.
      destruct (TreeBound T2) eqn:TNT2; auto.
      destruct p.
      intuition.
    * unfold Ordered in ord'.
      unfold Bound.TB.lt_with_empty.
      unfold TreeTB.
      cbn.
      destruct (TreeBound T1) eqn:TNT1; auto.
      destruct p.
      destruct (TreeBound T2) eqn:TNT2; auto.
      destruct p.
      intuition.
Defined.


Fixpoint find_opt {V: Type} (T : Tree V) (k : K.t) : option V :=
  match T with
  | Empty => None
  | V1 k1 v => if K.eq_dec k k1 then Some v else None
  | V2 k11 v11 k1 v1 =>
      match K.compare k k1 with
      | Eq => Some v1
      | Lt => if K.eq_dec k k11 then Some v11 else None
      | Gt => None
      end
  | V3 k11 v11 k1 v1 k12 v12 => 
      match K.compare k k1 with
      | Eq => Some v1
      | Lt => if K.eq_dec k k11 then Some v11 else None
      | Gt => if K.eq_dec k k12 then Some v12 else None
      end
  | Node _ l k1 v r =>
      match K.compare k k1 with
      | Eq => Some v
      | Lt => find_opt l k
      | Gt => find_opt r k
      end
  end.

Inductive MapsTo {V : Type} (k : K.t) (v : V) : Tree V -> Prop :=
  | MapsTo_V1 :
      MapsTo k v (V1 k v)
  | MapsTo_V2_left (k1 : K.t) (v1 : V) :
      MapsTo k v (V2 k v k1 v1)
  | MapsTo_V2_top (k11 : K.t) (v11 : V) :
      MapsTo k v (V2 k11 v11 k v)
  | MapsTo_V3_left (k1 : K.t) (v1 : V) (k12 : K.t) (v12 : V) :
      MapsTo k v (V3 k v k1 v1 k12 v12)
  | MapsTo_V3_top (k11 : K.t) (v11 : V) (k12 : K.t) (v12 : V) :
      MapsTo k v (V3 k11 v11 k v k12 v12)
  | MapsTo_V3_right (k11 : K.t) (v11 : V) (k1 : K.t) (v1 : V) :
      MapsTo k v (V3 k11 v11 k1 v1 k v)
  | MapsTo_Node_here (n : nat) (l : Tree V) (r : Tree V) :
      MapsTo k v (Node n l k v r)
  | MapsTo_Node_left (n : nat) (l : Tree V) (k0 : K.t) (v0 : V) (r : Tree V) :
      (K.lt k k0) ->
      MapsTo k v l ->
      MapsTo k v (Node n l k0 v0 r)
  | MapsTo_Node_right (n : nat) (l : Tree V) (k0 : K.t) (v0 : V) (r : Tree V) :
      (K.lt k0 k) ->
      MapsTo k v r ->
      MapsTo k v (Node n l k0 v0 r)
.

Definition InTree {V : Type} (k : K.t) (T : Tree V) : Prop :=
  exists v, MapsTo k v T.

Lemma InTree_from_MapsTo {V : Type} {k : K.t} {v : V} {T : Tree V} :
  MapsTo k v T -> InTree k T.
Proof.
  intro H. exists v. exact H.
Qed.

Lemma find_opt_Correct {V : Type} (T : Tree V) (ord : Property [ Ordered ] T) (k : K.t) (v : V) : MapsTo k v T <-> find_opt T k = Some v.
Proof.
  split.
  {
  intros.
  induction H.
  * simpl. now destruct (K.eq_dec k k).
  * epose proof (Property_This' ord) as ord'. unfold Ordered in ord'.
    simpl. Bound.compare_smash.
    now destruct (K.eq_dec k k).
  * epose proof (Property_This' ord) as ord'. unfold Ordered in ord'.
    simpl. Bound.compare_smash.
  * epose proof (Property_This' ord) as ord'. unfold Ordered in ord'.
    destruct_conjs.
    simpl. Bound.compare_smash.
    now destruct (K.eq_dec k k).
  * epose proof (Property_This' ord) as ord'. unfold Ordered in ord'.
    destruct_conjs.
    simpl. Bound.compare_smash.
  * epose proof (Property_This' ord) as ord'. unfold Ordered in ord'.
    destruct_conjs.
    simpl. Bound.compare_smash.
    now destruct (K.eq_dec k k).
  * epose proof (Property_This' ord) as ord'. unfold Ordered in ord'.
    simpl. Bound.compare_smash.
  * epose proof (Property_This' ord) as ord'. unfold Ordered in ord'.
    cbn. inversion ord. intuition. subst.
    Bound.compare_smash.
  * epose proof (Property_This' ord) as ord'. unfold Ordered in ord'.
    cbn. inversion ord. intuition. subst.
    Bound.compare_smash.
  }
  {
  intros.
  induction T.
  - now simpl in H.
  - cbn in H. destruct (K.eq_dec k t).
    * injection H. intros. subst. constructor.
    * easy.
  - cbn in H. Bound.compare_smash.
    * injection H. intros. subst. constructor.
    * destruct (K.eq_dec k t).
      ** injection H. intros. subst. constructor.
      ** easy.
    * easy.
  - cbn in H. Bound.compare_smash.
    * injection H. intros. subst. constructor.
    * destruct (K.eq_dec k t).
      ** injection H. intros. subst. constructor.
      ** easy.
    * destruct (K.eq_dec k t1).
      ** injection H. intros. subst. constructor.
      ** easy.
  - inversion ord. subst. intuition.
    cbn in H.
    destruct (K.compare_spec k t).
    + injection H. intros. subst. constructor.
    + intuition. constructor; auto.
    + intuition. constructor 9; auto.
  }
Qed.

Fixpoint to_list {V : Type} (T : Tree V) : list (K.t * V) :=
  match T with
  | Empty => []
  | V1 k v => [(k, v)]
  | V2 k11 v11 k1 v1 => [(k11, v11); (k1, v1)]
  | V3 k11 v11 k1 v1 k12 v12 => [(k11, v11); (k1, v1); (k12, v12)]
  | Node _ l k v r => to_list l ++ [(k, v)] ++ to_list r
  end.

Fixpoint to_list_tail_recursive {V : Type} (T : Tree V) (acc : list (K.t * V)) : list (K.t * V) :=
  match T with
  | Empty => acc
  | V1 k v => (k, v) :: acc
  | V2 k11 v11 k1 v1 => (k11, v11) :: (k1, v1) :: acc
  | V3 k11 v11 k1 v1 k12 v12 => (k11, v11) :: (k1, v1) :: (k12, v12) :: acc
  | Node _ l k v r => to_list_tail_recursive l ((k, v) :: to_list_tail_recursive r acc)
  end.

Lemma to_list_tail_recursive_correct' {V : Type} (T : Tree V) (acc : list (K.t * V)) : to_list T ++ acc = to_list_tail_recursive T acc.
Proof.
  revert acc.
  induction T.
  - now auto.
  - now auto.
  - now auto.
  - now auto.
  - cbn.
    intros.
    rewrite<- (IHT2 acc).
    remember ((t, v) :: to_list T2 ++ acc) as acc'.
    rewrite<- (IHT1 acc').
    rewrite Heqacc'.
    rewrite<-app_assoc.
    now rewrite app_comm_cons.
Qed.

Lemma to_list_tail_recursive_correct {V : Type} (T : Tree V) : to_list T = to_list_tail_recursive T [].
Proof.
  epose proof (to_list_tail_recursive_correct' T []) as H.
  rewrite<-H.
  now rewrite app_nil_r.
Qed.

Definition size {V : Type} (T : Tree V) : nat := weight T - 1.

Lemma to_list_size {V : Type} {Ps : list (PropF (V:=V))} (T : Tree V) `{InList _ WeightConsistent Ps} (WC : Property Ps T) :
  size T = List.length (to_list T).
Proof.
  epose proof (Property_In WeightConsistent WC _) as wf.
  clear WC.
  induction T.
  - now auto.
  - now cbn.
  - now cbn.
  - now cbn.
  - inversion wf. intuition. subst.  cbn.
    simpl_list.
    rewrite<-H0.
    cbn.
    rewrite<-H6.
    epose proof (Property_This' wf) as wf'.
    epose proof (Property_This' Hl) as Hl'.
    epose proof (Property_This' Hr) as Hr'.
    unfold WeightConsistent in wf', Hl', Hr'.
    cbn in wf'.
    rewrite<- Hl' in wf'.
    rewrite<- Hr' in wf'.
    rewrite wf'.
    unfold size.
    epose proof (WeightConsistent_Size _ Hl).
    epose proof (WeightConsistent_Size _ Hr).
    lia.
Qed.

Lemma MapsTo_in_Bound { V : Type } {T : Tree V} {tb : Bound.TB.t} (btt : BoundedTreeTight T tb) :
  forall (k : K.t) (v : V),
  MapsTo k v T -> Bound.TB.key_contained_in k tb
  .
Proof.
  unfold Bound.TB.key_contained_in.
  induction btt.
  - intros. inversion H.
  - intros. inversion H; subst.
    apply Bound.TB.contained_in_Reflexive.
  - intros. inversion H; subst.
    + apply Bound.TB.containedMerge. left. 
      apply Bound.TB.contained_in_Reflexive.
    + apply Bound.TB.containedMerge. right.
      apply Bound.TB.contained_in_Reflexive.
  - intros. inversion H; subst.
    + apply Bound.TB.containedMerge3. left.
      apply Bound.TB.contained_in_Reflexive.
    + apply Bound.TB.containedMerge3. right. left.
      apply Bound.TB.contained_in_Reflexive.
    + apply Bound.TB.containedMerge3. right. right.
      apply Bound.TB.contained_in_Reflexive.
  - intros.
    apply Bound.TB.containedMerge3.
    inversion H1; subst.
    + right. left.
      apply Bound.TB.contained_in_Reflexive.
    + left. now specialize (IHbtt1 _ _ H8).
    + right. right. now specialize (IHbtt2 _ _ H8).
Qed.

Lemma MapsToNode_left {V : Type} {n : nat} {l : Tree V} (k : K.t) (v : V) {r : Tree V} {k0 : K.t} {v0 : V} (ord : Property [Ordered] (Node n l k0 v0 r)) :
  MapsTo k v l -> K.lt k k0.
Proof.
  intros.
  pose proof (BoundedOrderedTight (Node n l k0 v0 r) ord) as bot.
  inversion bot; subst.
  pose proof (MapsTo_in_Bound left_bound k v H) as inLeft.
  unfold Bound.TB.key_contained_in in inLeft.
  epose proof (Bound.TB.LtContained1 _ _ H2 _ inLeft) as HA.
  cbn in HA. Bound.compare_smash; simpl in *; easy.
Qed.

Lemma MapsToNode_right {V : Type} {n : nat} {l : Tree V} (k : K.t) (v : V) {r : Tree V} {k0 : K.t} {v0 : V} (ord : Property [Ordered] (Node n l k0 v0 r)) :
  MapsTo k v r -> K.lt k0 k.
Proof.
  intros.
  pose proof (BoundedOrderedTight (Node n l k0 v0 r) ord) as bot.
  inversion bot; subst.
  pose proof (MapsTo_in_Bound right_bound k v H) as inRight.
  unfold Bound.TB.key_contained_in in inRight.
  epose proof (Bound.TB.LtContained2 _ _ H7 _ inRight) as HA.
  cbn in HA. Bound.compare_smash; simpl in *; easy.
Qed.

Lemma to_list_MapsTo { V : Type } (T : Tree V) (ord : Property [ Ordered ] T) :
  forall (k : K.t) (v : V),
  MapsTo k v T <-> In (k, v) (to_list T).
Proof.
  split. intros.
  - clear ord. induction H; cbn; intuition.
    + rewrite in_app_iff.
      right.
      now constructor.
    + rewrite in_app_iff.
      now left.
    + rewrite in_app_iff.
      right.
      now apply in_cons.
  - intros. 
    epose proof (BoundedOrderedTight _ ord) as bot.
    induction bot.
    + inversion H.
    + cbn in *. destruct H; inversion H; subst; constructor.
    + cbn in *. destruct H.
      * inversion H; subst; constructor.
      * destruct H; inversion H; subst; constructor.
    + cbn in *. destruct H.
      * inversion H; subst; constructor.
      * destruct H.
        ** inversion H; subst; constructor.
        ** destruct H; inversion H; subst; constructor.
    + inversion ord. intuition. subst.
      cbn in H.
      rewrite in_app_iff in H.
      destruct H.
      * intuition. constructor; auto.
        now epose proof (MapsToNode_left k v ord H3).
      * inversion H.
        ** inversion H3. subst. constructor.
        ** intuition. constructor 9; auto.
           now epose proof (MapsToNode_right k v ord H4).
Qed. 
        

Definition binding_lt {V : Type} (b1 : K.t * V) (b2 : K.t * V) : Prop :=
  match b1, b2 with
  | (k1, _), (k2, _) => K.lt k1 k2
  end.

Definition binding_le {V : Type} (b1 : K.t * V) (b2 : K.t * V) : Prop :=
  match b1, b2 with
  | (k1, _), (k2, _) => K.le k1 k2
  end.

Definition binding_le_opt {V : Type} (b1 : option (K.t * V)) (b2 : option (K.t * V)) : Prop :=
  match b1, b2 with
  | Some b1, Some b2 => binding_le b1 b2
  | Some _, None => True
  | None, Some _ => True
  | None, None => True
  end.

Definition key_lt_opt (k1 : option K.t) (k2 : option K.t) : Prop :=
  match k1, k2 with
  | Some k1, Some k2 => K.lt k1 k2
  | Some _, None => True
  | None, Some _ => True
  | None, None => True
  end.

Definition key_le_opt (k1 : option K.t) (k2 : option K.t) : Prop :=
  match k1, k2 with
  | Some k1, Some k2 => K.le k1 k2
  | Some _, None => True
  | None, Some _ => True
  | None, None => True
  end.


Lemma list_last_Last {A : Type} (x0 : list A) (x1 : A) :
  last (x0 ++ [x1]) = Some x1.
Proof.
  induction x0.
  - now cbn.
  - rewrite<-app_comm_cons.
    unfold last. fold (last (A:=A)).
    cbn.
    cbn. rewrite IHx0. 
    destruct (x0 ++ [x1]) eqn:eX.
    + now cbn in *.
    + easy.
Qed.

Lemma list_last_Some {A : Type} (x0 : list A) :
  x0 <> [] -> exists (a : A), last x0 = Some a. 
Proof.
  induction x0.
  - now auto.
  - intros.
    destruct x0.
    + cbn in *. now exists a.
    + assert (a0 :: x0 <> []) by easy.
      intuition.
Qed.

Lemma list_last_skip {A : Type} (x0 : list A) (x' : A) (x1 : list A) :
  last (x0 ++ (x' :: x1)) = last (x' :: x1).
Proof.
  induction x0.
  - now cbn.
  - cbn in *.
    simpl.
    assert (x0 ++ x' :: x1 <> []) by (induction x0; now simpl).
    destruct (x0 ++ x' :: x1) eqn:eX; easy.
Qed.

Lemma list_last_In {A : Type} (x : list A) (x' : A) :
  last x = Some x' -> In x' x.
Proof.
  induction x.
  - now cbn.
  - cbn. intros.
    destruct x.
    + injection H. intros. subst. intuition.
    + intuition.
Qed.

Lemma LocallySortedAppend {A : Type} (order : A -> A -> Prop) (x : list A) (y : list A) :
  LocallySorted order x -> LocallySorted order y ->
  (match last x, hd_error y with
   | Some a, Some b => order a b
   | _, _ => True
   end) 
  -> LocallySorted order (x ++ y).
Proof.
  intros.
  induction x.
  - now cbn.
  - assert (LocallySorted order x) as Sx by (inversion H; now try constructor).
    specialize (IHx Sx).
    assert ((a::x) <> []) as nonempty by easy.
    epose proof (exists_last nonempty).
    destruct X.
    destruct s.
    cbn.
    induction x.
    + cbn. inversion H. cbn in *. intuition. subst. destruct y; auto.
      constructor; auto.
    + cbn in *.
      constructor; auto.
      now inversion H.
Qed.

Definition hd_last {A : Type} (l : list A) : option (A * A) :=
  match hd_error l, last l with
  | Some a, Some b => Some (a, b)
  | _, _ => None
  end.

Definition to_bound {V : Type} (pr : option ((K.t * V) * (K.t * V))) : Bound.TBound :=
  match pr with
  | Some ((k1, v1), (k2, v2)) => Some (Bound.Key k1, Bound.Key k2)
  | None => None
  end.

Lemma BoundedContained {V : Type} (T : Tree V) (tb : Bound.TB.t) :
  BoundedTree tb T ->  forall (k : K.t), InTree k T -> Bound.TB.key_contained_in k tb.
Proof.
  intros BT k inTree.
  induction BT.
  - inversion inTree. inversion H.
  - inversion inTree as [v' map].
    inversion map.
    now subst.
  - inversion inTree as [v' map].
    inversion map.
    + now subst.
    + now subst.
  - inversion inTree as [v' map].
    inversion map; now subst.
  - inversion inTree as [v' map].
    inversion map. subst.
    + auto.
    + epose proof (InTree_from_MapsTo H9).
      specialize (IHBT1 H10).
      subst.
      apply Bound.TB.containedMerge3.
      intuition.
    + subst.
      apply Bound.TB.containedMerge3.
      epose proof (InTree_from_MapsTo H9).
      specialize (IHBT2 H0).
      intuition.
Qed.

Lemma to_list_LocallySorted {V : Type} {Ps : list PropF} {il : InList Ordered Ps} (T : Tree V) (ps : Property Ps T) :
  LocallySorted binding_lt (to_list T).
Proof.
  epose proof (Property_In Ordered ps _) as ord.
  clear ps.
  epose proof (BoundedOrderedTight _ ord) as bo.
  induction bo.
  - cbn. constructor.
  - cbn. constructor.
  - epose proof (Property_This' ord) as ord'; cbn in ord'.
    cbn. repeat constructor. now cbn.
  - epose proof (Property_This' ord) as [ ord1 [ ord2 ord3]].
    cbn.
    repeat constructor; now cbn.
  - epose proof (to_list_MapsTo _ ord k v) as tlMT.
    inversion ord; intuition. subst.
    cbn.
    epose proof (LocallySortedAppend _ _ ((k, v) :: to_list r) H8).
    assert (LocallySorted binding_lt ((k, v) :: to_list r)).
    + destruct (to_list r) eqn:eR; constructor; auto.
      cbn. destruct p.
      epose proof (to_list_MapsTo _ Hr t v0) as [ tlMT0 tlMT1].
      specialize (tlMT1 ltac:(rewrite eR; now constructor)).
      now epose proof (MapsToNode_right _ _ ord tlMT1) as MNR.
    + intuition. cbn in H4.
      destruct (last (to_list l)) eqn:eL.
      * epose proof (list_last_In _ _ eL) as IL.
        unfold binding_lt in H4.
        destruct p eqn:Ep.
        fold (binding_lt (V:=V)) in H4.
        rewrite<-to_list_MapsTo in IL; auto.
        epose proof (MapsToNode_left _ _ ord IL) as MNL.
        intuition.
      * intuition.
Qed.

Lemma binding_lt_Transitive {V : Type} : Transitive (binding_lt (V:=V)).
Proof.
  unfold Transitive.
  unfold binding_lt.
  destruct x, y, z.
  KFacts.order.
Qed.

Lemma to_list_Sorted {V : Type} {Ps : list PropF} {il : InList Ordered Ps} (T : Tree V) (ps : Property Ps T) :
  StronglySorted binding_lt (to_list T).
Proof.
  epose proof (Property_In Ordered ps _) as ord.
  epose proof (to_list_LocallySorted _ ord) as ls.
  eapply Sorted_StronglySorted.
  - exact (binding_lt_Transitive).
  - now rewrite Sorted_LocallySorted_iff.
Qed.

Lemma to_list_NotEmpty {V : Type} (T : Tree V) :
  notEmpty T <-> to_list T <> [].
Proof.
  intros.
  induction T; try easy.
  cbn.
  destruct (to_list T1).
  + now cbn.
  + now cbn.
Qed.

Lemma to_list_Empty {V : Type} (T : Tree V) :
  to_list T = [] <-> T = Empty.
Proof.
  induction T; try now cbn.
  cbn.
  split; intros.
  - exfalso.
    now destruct (to_list T1).
  - easy.
Qed.

Lemma nodeNotEmpty {V : Type} {Ps : list PropF} {sl : SubList WellBalanced Ps} {n : nat} {Tl : Tree V} {k : K.t} {v : V} {Tr : Tree V} : Property Ps (Node n Tl k v Tr) -> notEmpty Tl /\ notEmpty Tr.
Proof.
  intros WF.
  destruct Tl, Tr.
  all: try pose proof (Node_NoEmptyL WF).
  all: try pose proof (Node_NoEmptyR WF).
  all: try contradiction.
  all: unfold notEmpty.
  all: easy.
Qed.

Definition fst_opt {A : Type} {B : Type} (x : option (A * B)) : option A :=
  match x with
  | Some (a, _) => Some a
  | None => None
  end.

Lemma min_binding_Sorted {V : Type} {Ps : list PropF} {sl : SubList WellBalanced Ps} (T : Tree V) (word : Property Ps T) :
  min_binding T = hd_error (to_list T).
Proof.
  induction T.
  - now cbn.
  - now cbn.
  - now cbn.
  - now cbn.
  - inversion word. intuition.
    epose proof (nodeNotEmpty word) as [nneL nneR].
    apply to_list_NotEmpty in nneL.
    cbn.
    rewrite H.
    destruct (to_list T1); easy.
Qed.

Lemma min_key_Sorted {V : Type} {Ps : list PropF} {sl : SubList WellBalanced Ps} (T : Tree V) (word : Property Ps T) :
  min_key T = fst_opt (head (to_list T)).
Proof.
  unfold min_key.
  epose proof (min_binding_Sorted _ word) as MB.
  rewrite MB.
  now unfold fst_opt.
Qed.

Lemma max_binding_Sorted {V : Type} {Ps : list PropF} {sl : SubList WellBalanced Ps} (T : Tree V) (word : Property Ps T) :
  max_binding T = last (to_list T).
Proof.
  induction T.
  - now cbn.
  - now cbn.
  - now cbn.
  - now cbn.
  - inversion word. intuition.
    epose proof (nodeNotEmpty word) as [nneL nneR].
    apply to_list_NotEmpty in nneR.
    cbn.
    rewrite H5.
    rewrite last_app_cons.
    destruct (to_list T2); easy.
Qed.

Lemma max_key_Sorted {V : Type} {Ps : list PropF} {sl : SubList WellBalanced Ps} (T : Tree V) (word : Property Ps T) :
  max_key T = fst_opt (last (to_list T)).
Proof.
  unfold max_key.
  epose proof (max_binding_Sorted _ word) as MB.
  rewrite MB.
  now unfold fst_opt.
Qed.

Program Definition min_binding_notEmpty {V : Type} {Ps : list PropF} {sl : SubList WellBalanced Ps} (T : Tree V) (word : Property Ps T) (ne : notEmpty T) : (K.t * V) :=
  match min_binding T with
  | Some k => k
  | None => False_rect _ _
  end.
Final Obligation.
  intros. induction T; cbn in *; try easy; epose proof (nodeNotEmpty word) as [nneL nneR]; inversion word; intuition.
Qed.

Program Definition max_binding_notEmpty {V : Type} {Ps : list PropF} {sl : SubList WellBalanced Ps} (T : Tree V) (word : Property Ps T) (ne : notEmpty T) : (K.t * V) :=
  match max_binding T with
  | Some k => k
  | None => False_rect _ _
  end.
Final Obligation.
  intros. induction T; cbn in *; try easy; epose proof (nodeNotEmpty word) as [nneL nneR]; inversion word; intuition.
Qed.

Lemma app_cons {A : Type} (x : list A) (y : A) : ([y] ++ x) = (y :: x). Proof. now cbn. Qed.

Lemma min_max_in_order {V : Type} (T : Tree V) (word : Property WellBalancedOrdered T) :
  binding_le_opt (min_binding T) (max_binding T).
Proof.
  epose proof min_binding_Sorted T word as minS.
  epose proof max_binding_Sorted T word as maxS.
  epose proof (to_list_Sorted _ word) as ss.
  unfold binding_le_opt.
  destruct (to_list T) eqn:eT.
  - cbn in *. now rewrite minS, maxS.
  - rewrite minS, maxS. cbn.
    rewrite<-app_cons in ss.
    destruct (last (p :: l)) eqn:el; auto.
    epose proof (StronglySorted_app_1_elem_of _ _ _ p p0 ss _).
    epose proof last_Some_elem_of l p0 as LSE.
    destruct l.
    + cbn in *. inversion el. subst. unfold binding_le. destruct p0. rewrite K.le_lteq. auto.
    + intuition. unfold binding_le. destruct p0. destruct p. rewrite K.le_lteq. auto.
  Unshelve.
  now rewrite list_elem_of_singleton.
Qed.

Lemma min_max_key_in_order {V : Type} (T : Tree V) (word : Property WellBalancedOrdered T) :
  key_le_opt (min_key T) (max_key T).
Proof.
  epose proof min_max_in_order T word as minmax.
  unfold binding_le_opt in *.
  unfold min_key, max_key.
  unfold key_le_opt. cbn in *.
  unfold binding_le in *.
  destruct (min_binding T) eqn:minB, (max_binding T) eqn:maxB.
  all: try destruct p; try destruct p0; auto.
Qed.

Lemma min_key_Node {V : Type} {n : nat} {l : Tree V} {k : K.t} {v : V} {r : Tree V} :
  min_key (Node n l k v r) = min_key l.
Proof.
  unfold min_key.
  now cbn.
Qed.

Lemma max_key_Node {V : Type} {n : nat} {l : Tree V} {k : K.t} {v : V} {r : Tree V} :
  max_key (Node n l k v r) = max_key r.
Proof.
  unfold max_key.
  now cbn.
Qed.

Lemma min_key_Node_Some {V : Type} {Ps : list PropF} {sl : SubList WellBalanced Ps} {n : nat} {l : Tree V} {k : K.t} {v : V} {r : Tree V}
(word : Property Ps (Node n l k v r)) :
  min_key (Node n l k v r) <> None.
Proof.
  unfold min_key.
  epose proof (min_binding_Sorted _ word).
  epose proof (to_list_NotEmpty (Node n l k v r)).
  
  destruct (to_list (Node n l k v r)) eqn:eT.
  - now apply to_list_NotEmpty in eT.
  - rewrite H. cbn. now destruct p.
    
Qed.

Lemma max_key_Node_Some {V : Type} {Ps : list PropF} {sl : SubList WellBalanced Ps} {n : nat} {l : Tree V} {k : K.t} {v : V} {r : Tree V}
(word : Property Ps (Node n l k v r)):
  max_key (Node n l k v r) <> None.
Proof.
  unfold max_key.
  epose proof (max_binding_Sorted _ word).
  destruct (to_list (Node n l k v r)) eqn:eT.
  - now apply to_list_NotEmpty in eT.
  - rewrite H. cbn. epose proof (last_None (p :: l0)) as [A B].
    destruct (last (p :: l0)); try destruct p0; try easy.
    now intuition.
Qed.

Lemma TreeBound_None {V : Type} (T : Tree V) :
  TreeBound T = None <-> T = Empty.
Proof.
  induction T.
  - now cbn.
  - now cbn.
  - now cbn.
  - now cbn.
  - cbn. destruct (TreeBound T1), (TreeBound T2); cbn.
    + destruct p, p0, t2; cbn; unfold Bound.compare, Bound.compare_k; easy.
    + destruct p; cbn; unfold Bound.compare, Bound.compare_k; easy.
    + destruct p; cbn; unfold Bound.compare, Bound.compare_k; easy.
    + easy.
Qed.
      

Lemma TreeBound_min {V : Type} (T : Tree V) (word : Property WellBalancedOrdered T) :
  Bound.lower (TreeBound T) = match min_key T with | None => None | Some k => Some (Bound.Key k) end.
Proof.
  epose proof (Property_In Ordered word _) as ord.
  epose proof (BoundedOrderedTight _ ord) as bot.
  induction bot; cbn; auto.
  epose proof (min_key_Node_Some word).
  epose proof (max_key_Node_Some word).
  rewrite min_key_Node in *.
  rewrite max_key_Node in *.

  destruct (min_key l) eqn:minl; try easy.
  
  inversion ord.
  subst.
  epose proof (BTT_is_TreeTB _ Hl _ bot1) as Hl0.
  epose proof (BTT_is_TreeTB _ Hr _ bot2) as Hr0.
  inversion word.
  specialize (IHbot1 Hl1 Hl).
  specialize (IHbot2 Hr1 Hr).
  subst.

  unfold Bound.lower in IHbot1.

  destruct (TreeBound l) eqn:TBL; cbn; try easy.

  destruct p eqn:Etbl.
  inversion IHbot1 as [ lbound ].

  destruct (TreeBound r) eqn:TBR; cbn; try easy.

  - destruct p0.
    cbn in IHbot2.
    destruct (min_key r) eqn:minr; try easy.
    cbn.

    unfold TreeTB, Bound.TB.lt_with_empty in H, H0.
    cbn in H, H0.
    rewrite TBR in H0.
    rewrite TBL in H.
    unfold Bound.lt in H, H0.
    rewrite H0.

    epose proof (OrderedValidTreeBound _ Hl) as valid_l.
    rewrite TBL in valid_l.
    cbn in valid_l.
    unfold Bound.ValidTBound, Bound.ValidBounds in valid_l.
    rewrite lbound in valid_l.
    unfold Bound.compare, Bound.compare_k in H, H0, valid_l.
    unfold Bound.compare, Bound.compare_k.
    
    destruct t1; cbn in *; repeat Bound.compare_smash; cbn in *; easy.
  - cbn in IHbot2.
    destruct (min_key r) eqn:minr; try easy.
    epose proof (TreeBound_None r) as [HA HB].
    specialize (HA TBR).
    rewrite HA in *; cbn in *. intuition.
Qed.

Lemma TreeBound_max {V : Type} (T : Tree V) (word : Property WellBalancedOrdered T) :
  Bound.upper (TreeBound T) = match max_key T with | None => None | Some k => Some (Bound.Key k) end.
Proof.
  epose proof (Property_In Ordered word _) as ord.
  epose proof (BoundedOrderedTight _ ord) as bot.
  induction bot; cbn; auto.
  epose proof (min_key_Node_Some word).
  epose proof (max_key_Node_Some word).
  rewrite min_key_Node in *.
  rewrite max_key_Node in *.

  destruct (max_key r) eqn:maxr; try easy.
  
  inversion ord.
  subst.
  epose proof (BTT_is_TreeTB _ Hl _ bot1) as Hl0.
  epose proof (BTT_is_TreeTB _ Hr _ bot2) as Hr0.
  inversion word.
  specialize (IHbot1 Hl1 Hl).
  specialize (IHbot2 Hr1 Hr).
  subst.

  unfold Bound.upper in IHbot2.

  destruct (TreeBound r) eqn:TBR; cbn; try easy.

  destruct p eqn:Etbl.
  inversion IHbot2 as [ rbound ].

  destruct (TreeBound l) eqn:TBL; cbn; try easy.

  - destruct p0.
    cbn in IHbot1.
    destruct (max_key l) eqn:maxl; try easy.
    cbn.

    unfold TreeTB, Bound.TB.lt_with_empty in H, H0.
    cbn in H, H0.
    rewrite TBR in H0.
    rewrite TBL in H.
    unfold Bound.lt in H, H0.

    inversion IHbot1 as [ lbound ].
    subst.

    clear IHbot1.
    clear IHbot2.
    clear H2.

    unfold Bound.compare, Bound.compare_k.
    unfold Bound.compare, Bound.compare_k in H, H0.

    repeat Bound.compare_smash; cbn in *; try easy; repeat Bound.compare_smash; cbn in *.

    epose proof (OrderedValidTreeBound _ Hr) as valid_r.
    rewrite TBR in valid_r.
    cbn in valid_r.
    unfold Bound.ValidTBound, Bound.ValidBounds in valid_r.
    subst; auto.

    all: destruct t0.
    + epose proof (TreeBound_min _ Hr1) as TBmin.
      unfold Bound.lower in TBmin. rewrite TBR in TBmin.
      destruct (min_key r) eqn:minr; try easy.
    + Bound.compare_smash; cbn in *; try easy.
      epose proof (OrderedValidTreeBound _ Hr) as valid_r.
      unfold Bound.ValidTBound, Bound.ValidBounds in valid_r.
      subst; auto.
      rewrite TBR in valid_r.
      unfold Bound.compare, Bound.compare_k in valid_r.
      Bound.compare_smash.
    + epose proof (OrderedValidTreeBound _ Hr) as valid_r.
      rewrite TBR in valid_r.
      unfold Bound.ValidTBound, Bound.ValidBounds in valid_r.
      now cbn in *.
  - cbn in IHbot1.
    destruct (max_key l) eqn:maxl; try easy.
    epose proof (TreeBound_None l) as [HA HB].
    specialize (HA TBL).
    rewrite HA in *; cbn in *. intuition.
Qed.
    

Program Lemma TreeBound_min_max {V : Type} (T : Tree V) (word : Property WellBalancedOrdered T) (min_b : K.t) (max_b : K.t) :
  min_key T = Some min_b -> max_key T = Some max_b -> TreeBound T = Some (Bound.Key min_b, Bound.Key max_b).
Proof.
  epose proof (TreeBound_max _ word) as maxB.
  epose proof (TreeBound_min _ word) as minB.
  intros minB' maxB'.
  rewrite minB' in minB.
  rewrite maxB' in maxB.
  unfold Bound.upper, Bound.lower in *.
  destruct (TreeBound T) eqn:TB; try easy.
  destruct p. inversion maxB. now inversion minB.
Qed.

    

Lemma StronglySorted_append {A : Type} (order : A -> A -> Prop) (x : list A) (y : list A) :
  StronglySorted order (x ++ y) -> StronglySorted order x /\ StronglySorted order y.
Proof.
  intros. split.
  - induction x.
    + constructor.
    + inversion H. intuition.
      constructor; auto.
      now rewrite Forall_app in H3.
  - induction x.
    + now cbn in H.
    + inversion H. intuition.
Qed.

Lemma StronglySorted_tail {A : Type} (order : A -> A -> Prop) (x : list A) (x' : A) :
  StronglySorted order (x ++ [x']) -> Forall (fun (a : A) => order a x') x.
Proof.
  intros.
  induction x.
  - constructor.
  - inversion H. intuition.
    rewrite StronglySorted_app in H.
    destruct H as [HA HB].
    constructor; auto.
    rewrite Forall_app in H3.
    destruct H3 as [HC HD].
    now inversion HD.
Qed.

Lemma and_true (P : Prop) :
  (P /\ True) = P.
Proof.
  now apply propositional_extensionality.
Qed.

Lemma true_and (P : Prop) :
  (True /\ P) = P.
Proof.
  now apply propositional_extensionality.
Qed.

Lemma binding_lt_neq {V : Type} (a : K.t * V) (b : K.t * V) :
  binding_lt a b -> a <> b.
Proof.
  destruct a,b.
  cbn. intros.
  intro Heq. inversion Heq.
  KFacts.order.
Qed.

Lemma binding_lt_NoDup {V : Type} {L : list (K.t * V)} :
  StronglySorted binding_lt L -> NoDup L.
Proof.
  induction L.
  - repeat constructor.
  - intros.
    apply NoDup_cons_2.
    + inversion H. subst.
      epose proof (Forall_impl _ _ _ H3 (binding_lt_neq a)).
      specialize (IHL H2).
      clear H3.
      clear H2.
      clear H.
      clear IHL.
      induction L; try apply not_elem_of_nil.
      inversion H0.
      intuition.
      subst.
      apply elem_of_cons in H4.
      destruct H4; intuition.
    + inversion H. subst. intuition.
Qed.

(*
Lemma binding_lt_not_elem_of {V : Type} (t : K.t) (v : V) (L : list (K.t * V)) :
  Forall (binding_lt (t, v)) L -> (t, v) ∉ L.
Proof.
  intros.
  epose proof (binding_lt_NoDup _ ).
  Search (_ ∉ _). 
  Qed.
 *)

Lemma to_list_NoDup {V : Type} (T : Tree V) :
  Property WellBalancedOrdered T -> NoDup (to_list T).
Proof.
  intros WBO.
  epose proof (to_list_Sorted _ WBO) as ss.
  epose proof (Property_In Ordered WBO _) as WBO'.
  epose proof (BoundedOrderedTight _ WBO') as bot.
  induction T.
  - repeat constructor.
  - cbn. repeat constructor.
    apply not_elem_of_nil.
  - cbn. repeat constructor; try apply not_elem_of_nil.
    cbn in *.
    inversion ss.
    apply not_elem_of_cons.
    split; try apply not_elem_of_nil.
    inversion H2. subst.
    unfold binding_lt in H5.
    intro Heq. injection Heq.
    try KFacts.order.
  - cbn. repeat constructor; try apply not_elem_of_nil; cbn in *.
    + epose proof (binding_lt_NoDup ss) as NoDup_ss.
      apply NoDup_cons in NoDup_ss.
      intuition.
    + inversion ss. subst.
      epose proof (binding_lt_NoDup H1).
      apply NoDup_cons in H.
      intuition.
  - cbn.
    cbn in ss.
    now apply binding_lt_NoDup in ss.
Qed.

(*
    inversion WBO.
    inversion WBO'.
    cbn in ss.
    apply StronglySorted_append in ss as [ssT1 ssT2'].
    apply StronglySorted_cons in ssT2' as [bltT2 ssT2].
    inversion bot.
    subst.
    epose proof (BTT_is_TreeTB _ Hl0 _ left_bound) as BTTl.
    epose proof (BTT_is_TreeTB _ Hr0 _ right_bound) as BTTr.

    rewrite<-BTTl in left_bound.
    rewrite<-BTTr in right_bound.
    
    specialize (IHT1 Hl ssT1 Hl0 left_bound).
    specialize (IHT2 Hr ssT2 Hr0 right_bound).
    
    cbn.
    apply NoDup_app; split; auto; split.
    + epose proof (to_list_Sorted _ WBO) as ss.
      cbn in ss.

    Search (NoDup (_ ++ _)).
    
    
    
    
    intuition.
      

      
      
      Search (StronglySorted _ _).
    Search (K.lt _ _).
    Check K.lt_not_eq.
 *)

Lemma min_key_None {V : Type} {Ps : list PropF} {sl : SubList WellBalanced Ps} {T : Tree V} (word : Property Ps T) :
    min_key T = None -> T = Empty.
Proof.
  intros.
  induction T; try easy.
  inversion word. intuition.
  unfold min_key in H.
  cbn in H.
  subst.
  cbn in *.
  now apply Node_NoEmptyL in word.
Qed.

Lemma max_key_None {V : Type} {Ps : list PropF} {sl : SubList WellBalanced Ps} {T : Tree V} (word : Property Ps T) :
    max_key T = None -> T = Empty.
Proof.
  intros.
  induction T; try easy.
  inversion word. intuition.
  unfold max_key in H.
  cbn in H.
  subst.
  cbn in *.
  now apply Node_NoEmptyR in word.
Qed.

Lemma StronglySorted_LastApp {A : Type} (order : A -> A -> Prop) (a : list A) (b : list A) :
  StronglySorted order (a ++ b) -> match last a with
                                   | None => True
                                   | Some x => StronglySorted order (x :: b)
                                   end.
Proof.
  intros ss.
  induction a.
  - now cbn.
  - rewrite<-app_cons in ss.
    rewrite<-app_assoc in ss.
    epose proof (StronglySorted_append _ _ _ ss) as [ss1 ss2].
    intuition.
    destruct a0; cbn in *; auto.
Qed.

Lemma to_list_Sorted_IsOrdered {V : Type}
  {Ps : list PropF} {sl : SubList WellBalanced Ps}
  (T : Tree V) :
  Property Ps T ->
  StronglySorted binding_lt (to_list T) -> Property [ Ordered ] T.
Proof.
  intros PP ssT.
  epose proof (Property_Sub PP) as WF.
  clear PP.
  induction T.
  - repeat constructor.
  - repeat constructor.
  - cbn in ssT.
    repeat constructor.
    cbn.
    inversion ssT.
    subst.
    inversion H2; subst.
    now cbn in H2.
  - cbn in ssT.
    inversion ssT. subst.
    repeat constructor.
    + inversion H2; subst.
      inversion H4; subst.
      now cbn in H5.
    + inversion H2; subst.
      now cbn in H3.
    + inversion H1; subst.
      inversion H4; subst.
      now cbn in H5.
  - inversion WF.
    cbn in ssT.
    specialize ssT as ssT'.
    apply StronglySorted_append in ssT' as [ssT1 ssT2'].
    specialize (IHT1 ssT1 Hl).
    apply StronglySorted_cons in ssT2' as [bltT2 ssT2].
    specialize (IHT2 ssT2 Hr).
    constructor; auto.
    repeat constructor.
    subst.
    cbn.
    epose proof (Property_Assemble WellBalancedOrdered IHT1 Hl) as wboT1.
    epose proof (Property_Assemble WellBalancedOrdered IHT2 Hr) as wboT2.
    epose proof (TreeBound_max _ wboT1) as TBmax1.
    epose proof (TreeBound_min _ wboT2) as TBmin2.
    epose proof (max_key_Sorted _ wboT1) as maxT1.
    rewrite maxT1 in TBmax1.
    epose proof (min_key_Sorted _ wboT2) as minT2.
    rewrite minT2 in TBmin2.
    unfold fst_opt in TBmax1, TBmin2.

    destruct (TreeBound T1) eqn:eTB1.
    unfold Bound.upper, Bound.lower in TBmax1, TBmin2.
    destruct p as [TBT1lo TBT1hi].
    epose proof (StronglySorted_LastApp _ _ _ ssT) as ssTla.
    + destruct (to_list T1) as [|T1hd T1tl] eqn:eT1.
      all: cbn in *.
      all: inversion bltT2. subst.
      all: subst.
      * rewrite<-H0 in *.
        cbn in *.
        epose proof (min_key_None wboT2 minT2) as eT2.
        subst.
        now apply Node_NoEmptyR in WF.
      * destruct (to_list T2) as [|T2hd T2tl] eqn:eT2.
        ** cbn in *.
           epose proof (min_key_None wboT2 minT2) as eT2'.
           subst.
           now apply Node_NoEmptyR in WF.
        ** epose proof (max_key_None wboT1 maxT1) as eT1'.
           subst.
           now apply Node_NoEmptyL in WF.
      * destruct (to_list T2) as [|T2hd T2tl] eqn:eT2.
        ** cbn in *.
           epose proof (min_key_None wboT2 minT2) as eT2'.
           subst.
           now apply Node_NoEmptyR in WF.
        ** inversion H0.
      * destruct (to_list T2) as [|T2hd T2tl] eqn:eT2.
        ** inversion H.
        ** inversion H. subst.
           destruct (TreeBound T2) eqn:eTB2.
           *** destruct p as [TBT2lo TBT2hi].
               subst. cbn in *.
               destruct T2hd as [T2hd_k T2hd_v].
               cbn in *.
               unfold Bound.lt, Bound.compare, Bound.compare_k in *.
               inversion TBmin2.
               pose proof (last_cons T1hd T1tl) as HA.
               rewrite HA in *.
               destruct (last T1tl) eqn:el.
               cbn in *.
               **** destruct p. subst.
                    inversion TBmax1. 
                    inversion ssTla.
                    subst.
                    inversion H6.
                    cbn in H4.
                    repeat Bound.compare_smash.
                    now cbn.
               **** destruct T1hd.
                    cbn in *.
                    inversion TBmax1. 
                    inversion ssTla.
                    subst.
                    inversion H7.
                    cbn in H4.
                    repeat Bound.compare_smash.
                    now cbn.
           *** epose proof (last_cons T1hd T1tl) as HA.
               rewrite HA in *.
               destruct (last T1tl) eqn:el.
               cbn in *.
               **** destruct p. subst.
                    inversion TBmax1. 
                    inversion ssTla.
                    subst.
                    inversion H6.
                    cbn in H4.
                    repeat Bound.compare_smash.
                    cbn.
                    Bound.compare_smash.
               **** destruct T1hd.
                    cbn in *.
                    inversion TBmax1. 
                    inversion ssTla.
                    subst.
                    cbn.
                    inversion H6.
                    cbn in H4.
                    repeat Bound.compare_smash.
    + destruct (TreeBound T2) eqn:eTB2; auto.
      destruct p as [TBT2lo TBT2hi].
      destruct (to_list T2) as [|T2hd T2tl] eqn:eT2.
      * cbn in *. easy.
      * cbn in *.
        inversion bltT2. subst.
        cbn in H1.
        destruct T2hd as [T2hd_k T2hd_v].
        inversion TBmin2. subst.
        cbn.
        Bound.compare_smash.
Qed.
    
Lemma LocallySorted_StronglySorted { A : Type } (R : A → A → Prop) (trans : Relations_1.Transitive R) :
  forall (l : list A) (ls : LocallySorted R l),
  StronglySorted R l.
Proof.
  intros.
  apply Sorted_StronglySorted.
  exact trans.
  now apply Sorted_LocallySorted_iff.
Qed.

Lemma StronglySorted_LocallySorted { A : Type } {R : A → A → Prop} :
  forall (l : list A) (ss : StronglySorted R l),
  LocallySorted R l.
Proof.
  intros.
  apply Sorted_LocallySorted_iff.
  now apply StronglySorted_Sorted.
Qed.

Ltac SortedSmash :=
  match goal with
  | [ H : StronglySorted ?rel ?l |- LocallySorted ?rel ?l ] =>
      apply Sorted_LocallySorted_iff; exact (StronglySorted_Sorted H)
  | [ H : Sorted ?rel ?l |- LocallySorted ?rel ?l ] =>
      apply Sorted_LocallySorted_iff; exact H
  | [ H : ?P |- ?P ] => exact H
  | [ |- StronglySorted ?rel ?l ] =>
      apply LocallySorted_StronglySorted; [> idtac | SortedSmash ]
  | [ |- Sorted ?rel ?l ] =>
      apply Sorted_LocallySorted_iff; SortedSmash
  | [ |- LocallySorted ?rel (?la ++ ?lb) ] =>
      apply LocallySortedAppend; [> SortedSmash | SortedSmash | cbn ]
  | [ |- LocallySorted ?rel (?la :: ?lb) ] =>
      apply Sorted_LocallySorted_iff; apply Sorted_cons; [> SortedSmash | SortedSmash ]
  | _ => idtac
  end.

Lemma BoundLt_max {V : Type} {Ps: list PropF} {Sl : SubList WellBalancedOrdered Ps} { T : Tree V } { k : K.t }
  { ord : Property Ps T}  {Sl2 : InList Ordered Ps}:
  Bound.TB.lt_with_empty (TreeTB T ord) (Bound.TB.key k) -> key_lt_opt (max_key T) (Some k).
Proof.
  epose proof (Property_In Ordered ord _) as ord'.
  epose proof (Property_Sub ord) as wbo.
  unfold TreeTB, Bound.TB.lt_with_empty.
  cbn.
  epose proof (max_key_Sorted _ wbo) as maxS.
  epose proof (TreeBound_max _ wbo) as tbm.

  destruct (last (to_list T)) eqn:eL.
  all: cycle 1.
  - cbn in *. rewrite maxS. now cbn.
  - cbn in maxS. destruct p as [maxK maxV].
    rewrite maxS in *.
    destruct (TreeBound T) as [ tb | ].
    all: cycle 1.
    + cbn in tbm. inversion tbm.
    + destruct tb as [tbLow tbHigh].
      cbn in tbm.
      inversion tbm.
      cbn.
      Bound.compare_smash; simpl; easy.
Qed.

Lemma BoundLt_min {V : Type} {Ps: list PropF} {Sl : SubList WellBalancedOrdered Ps} { T : Tree V } { k : K.t }
  { ord : Property Ps T}  {Sl2 : InList Ordered Ps}:
  Bound.TB.lt_with_empty (Bound.TB.key k) (TreeTB T ord) -> key_lt_opt (Some k) (min_key T).
Proof.
  epose proof (Property_In Ordered ord _) as ord'.
  epose proof (Property_Sub ord) as wbo.
  unfold TreeTB, Bound.TB.lt_with_empty.
  cbn.
  epose proof (min_key_Sorted _ wbo) as minS.
  epose proof (TreeBound_min _ wbo) as tbm.

  destruct (to_list T) eqn:eT.
  - cbn in *. rewrite minS. now cbn.
  - cbn in minS. destruct p as [minK minV].
    rewrite minS in *.
    destruct (TreeBound T) as [ tb | ].
    all: cycle 1.
    + cbn in tbm. inversion tbm.
    + destruct tb as [tbLow tbHigh].
      cbn in tbm.
      inversion tbm.
      cbn.
      Bound.compare_smash; simpl; easy.
Qed.


Lemma single_rotation_left_node_Ordered : forall {V : Type} (n1w : nat) (n2w : nat)
  (n11 : Tree V) (n1k : K.t) (n1v : V) (n12 : Tree V)
  (n0k : K.t) (n0v : V) (n2 : Tree V)
  (n1wEq : n1w = weight n11 + weight n12)
  (n2wEq : n2w = weight n2)
  (wboN1 : Property WellBalancedOrdered (Node n1w n11 n1k n1v n12))
  (wboN2 : Property WellBalancedOrdered n2),
  (IsDeepCase (Node n1w n11 n1k n1v n12) n2) ->
  (needsRotation n1w n2w) ->
  (ValidInputImbalance n1w n2w) ->
  (Bound.TB.lt_with_empty (TreeTB _ wboN1) (Bound.TB.key n0k)) ->
  (Bound.TB.lt_with_empty (Bound.TB.key n0k) (TreeTB _ wboN2)) ->
  (needsSingleRotationAnalyzeLeft (weight n11) n12 (weight n2)) ->
  Property [ Ordered ] (single_rotation_left_node n1w n2w n11 n1k n1v n12 n0k n0v n2).
Proof.
  intros V n1w n2w n11 n1k n1v n12 n0k n0v n2 n1wEq n2wEq wboN1 wboN2 DeepCase NR VI ordN1 ordN2 LS.
  apply to_list_Sorted_IsOrdered.
  + apply single_rotation_left_node_WellBalanced; auto.
    * apply (Property_Sub wboN1).
    * apply (Property_Sub wboN2).
  + cbn.
    epose proof (to_list_Sorted _ wboN1) as ssN1.
    epose proof (to_list_Sorted _ wboN2) as ssN2.
    cbn in ssN1.
    apply (StronglySorted_app _ _ _) in ssN1 as [ faN1 [ ssN11 ssnk12 ] ].
    specialize (StronglySorted_Sorted ssnk12) as snk12.
    apply Sorted_inv in snk12 as [sn12 hdkn12 ].
    SortedSmash.
    - exact binding_lt_Transitive.
    - epose proof (BoundLt_min ordN2) as minN2.
      epose proof (min_key_Sorted _ wboN2) as mks.
      rewrite mks in minN2.
      cbn in minN2.
      destruct (to_list n2) eqn:eT2; constructor.
      cbn. cbn in minN2. now destruct p.
    - epose proof (BoundLt_max ordN1) as maxN1.
      epose proof (max_key_Sorted _ wboN1) as mks.
      cbn in mks.
      rewrite max_key_Node in mks.
      rewrite max_key_Node in maxN1.
      unfold binding_lt.
      unfold fst_opt in mks.
      rewrite last_app_cons in mks.
      destruct (to_list n12).
      * now cbn.
      * cbn in mks.
        destruct (last (p :: l)).
        ** destruct p0.
           rewrite mks in maxN1.
           now cbn in maxN1.
        ** easy.
    - apply StronglySorted_Sorted in ssnk12. inversion ssnk12.
      
      destruct (to_list n12) eqn:eT12.
      * apply to_list_Empty in eT12.
        specialize wboN1 as wboN1'.
        rewrite eT12 in wboN1'.
        now apply Node_NoEmptyR in wboN1'.
      * constructor.
        now inversion H2.
    - destruct (last (to_list n11)) eqn:eMax; auto.
      eapply (faN1 p (n1k, n1v) ltac:(now apply last_Some_elem_of) ltac:(apply list_elem_of_here)).
Qed.

Lemma double_rotation_left_node_Ordered : forall {V : Type} (n1w : nat) (n12w : nat) (n2w : nat)
  (n11 : Tree V) (n1k : K.t) (n1v : V)
  (n12k : K.t) (n12v : V)
  (n121 : Tree V) (n122 : Tree V)
  (n0k : K.t) (n0v : V)
  (n2 : Tree V)
  (n1wEq : n1w = weight n11 + weight n121 + weight n122)
  (n2wEq : n2w = weight n2)
  (n12wEq : n12w = weight n121 + weight n122)
  (wboN1 : Property WellBalancedOrdered (Node n1w n11 n1k n1v (Node n12w n121 n12k n12v n122)))
  (wboN2 : Property WellBalancedOrdered n2),
  (IsDeepCase (Node n1w n11 n1k n1v (Node n12w n121 n12k n12v n122)) n2) ->
  (needsRotation n1w n2w) ->
  (ValidInputImbalance n1w n2w) ->
  (Bound.TB.lt_with_empty (TreeTB _ wboN1) (Bound.TB.key n0k)) ->
  (Bound.TB.lt_with_empty (Bound.TB.key n0k) (TreeTB _ wboN2)) ->
  (not (needsSingleRotation2 (weight n11) (weight n121) (weight n122) (weight n2))) ->
  Property [ Ordered ] (double_rotation_left_node n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 n0k n0v n2).
Proof.
  intros V n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 n0k n0v n2 n1wEq n2wEq n12wEq wboN1 wboN2 DeepCase NR VI ordN1 ordN2 NSR2.
  apply to_list_Sorted_IsOrdered.
  + apply double_rotation_left_node_WellBalanced; auto.
    * apply (Property_Sub wboN1).
    * apply (Property_Sub wboN2).
  + cbn.
    epose proof (to_list_Sorted _ wboN1) as ssN1.
    epose proof (to_list_Sorted _ wboN2) as ssN2.
    cbn in ssN1.
    apply (StronglySorted_app _ _ _) in ssN1 as [ faN1 [ ssN11 ssnk12 ] ].
    inversion ssnk12.
    subst.
    apply (StronglySorted_app _ _ _) in H1 as [ faN121 [ ssN121 ssnk122 ] ].
    inversion ssnk122.
    subst.
    epose proof (BoundLt_min ordN2) as minN2.
    epose proof (BoundLt_max ordN1) as maxN1.
    repeat rewrite max_key_Node in maxN1.
    
    SortedSmash.
    - exact binding_lt_Transitive.
    - 
      epose proof (min_key_Sorted _ wboN2) as mks.
      rewrite mks in minN2.
      cbn in minN2.
      destruct (to_list n2) eqn:eT2; cbn in mks; destruct (to_list n121) eqn:eT121; constructor;
      now inversion H2.
    - destruct (last (to_list n11)) eqn:eMax; auto.
      eapply (faN1 p (n1k, n1v) ltac:(now apply last_Some_elem_of) ltac:(apply list_elem_of_here)).
    - cbn in minN2.
      epose proof (min_key_Sorted _ wboN2) as mks.
      rewrite mks in minN2.
      cbn in minN2.
      destruct (to_list n2) eqn:eT2.
      * now cbn.
      * cbn in minN2. constructor. cbn. now destruct p.
    - inversion wboN1.
      inversion Hr.
      subst.
      epose proof (max_key_Sorted _ Hr0) as mks.
      rewrite mks in maxN1.
      destruct (last (to_list n122)) eqn:eMax122; auto.
      destruct p.
      cbn in maxN1. now cbn.
    - destruct (to_list n122) eqn:eT122.
      * inversion wboN1.
        inversion Hr.
        subst.
        rewrite to_list_Empty in eT122.
        subst.
        now apply Node_NoEmptyR in Hr.
      * constructor.
        now inversion H3.
    - destruct (to_list n121) eqn:eT121.
      * inversion wboN1.
        inversion Hr.
        subst.
        rewrite to_list_Empty in eT121.
        subst.
        now apply Node_NoEmptyL in Hr.
      * rewrite last_app_cons.
        rewrite last_cons_cons.
        rewrite<-eT121 in *.
        destruct (last (to_list n121)) eqn:eMax121; auto.
        now apply (faN121 p0 (n12k, n12v) ltac:(now apply last_Some_elem_of) ltac:(apply list_elem_of_here)).
Qed.

Lemma single_rotation_right_node_Ordered : forall {V : Type} (n1w : nat) (n2w : nat)
  (n1 : Tree V)
  (n0k : K.t) (n0v : V)
  (n21 : Tree V) (n2k : K.t) (n2v : V) (n22 : Tree V)
  (n1wEq : n1w = weight n1)
  (n2wEq : n2w = weight n21 + weight n22)
  (wboN1 : Property WellBalancedOrdered n1)
  (wboN2 : Property WellBalancedOrdered (Node n2w n21 n2k n2v n22)),
  (IsDeepCase n1 (Node n2w n21 n2k n2v n22)) ->
  (needsRotation n2w n1w) ->
  (ValidInputImbalance n1w n2w) ->
  (Bound.TB.lt_with_empty (TreeTB _ wboN1) (Bound.TB.key n0k)) ->
  (Bound.TB.lt_with_empty (Bound.TB.key n0k) (TreeTB _ wboN2)) ->
  (needsSingleRotationAnalyzeRight (weight n1) n21 (weight n22)) ->
  Property [ Ordered ] (single_rotation_right_node n1w n2w n1 n0k n0v n21 n2k n2v n22).
Proof.
  intros V n1w n2w n1 n0k n0v n21 n2k n2v n22 n1wEq n2wEq wboN1 wboN2 DeepCase NR VI ordN1 ordN2 RS.
  apply to_list_Sorted_IsOrdered.
  + apply single_rotation_right_node_WellBalanced; auto.
    * apply (Property_Sub wboN1).
    * apply (Property_Sub wboN2).
  + cbn.
    epose proof (to_list_Sorted _ wboN1) as ssN1.
    epose proof (to_list_Sorted _ wboN2) as ssN2.
    cbn in ssN2.
    apply (StronglySorted_app _ _ _) in ssN2 as [ faN2 [ ssN21 ssnk22 ] ].
    specialize (StronglySorted_Sorted ssnk22) as snk22.
    apply Sorted_inv in snk22 as [sn22 hdkn22].
    SortedSmash.
    - exact binding_lt_Transitive.
    - epose proof (BoundLt_min ordN2) as minN2.
      epose proof (min_key_Sorted _ wboN2) as mks.
      rewrite mks in minN2.
      cbn in minN2.
      destruct (to_list n21) eqn:eT21; constructor.
      cbn. cbn in minN2. now destruct p.
    - epose proof (BoundLt_max ordN1) as maxN1.
      epose proof (max_key_Sorted _ wboN1) as mks.
      destruct (to_list n1).
      * now cbn.
      * cbn in mks.
        destruct (last (p :: l)).
        ** destruct p0.
           rewrite mks in maxN1.
           now cbn in maxN1.
        ** easy.
    - rewrite last_app_cons.
      destruct (to_list n21) eqn:eT21.
      * cbn.
        epose proof (BoundLt_min ordN2) as minN2.
        epose proof (min_key_Sorted _ wboN2) as mks.
        rewrite mks in minN2.
        cbn in minN2.
        rewrite eT21 in minN2.
        cbn in minN2.
        exact minN2.
      * rewrite last_cons_cons.
        rewrite<-eT21 in *.
        destruct (last (to_list n21)) eqn:eMax21; auto.
        eapply (faN2 p0 (n2k, n2v) ltac:(now apply last_Some_elem_of) ltac:(apply list_elem_of_here)).
Qed.

Lemma double_rotation_right_node_Ordered : forall {V : Type} (n1w : nat) (n21w : nat) (n2w : nat)
  (n1 : Tree V)
  (n0k : K.t) (n0v : V)
  (n21k : K.t) (n21v : V)
  (n211 : Tree V) (n212 : Tree V)
  (n2k : K.t) (n2v : V)
  (n22 : Tree V)
  (n1wEq : n1w = weight n1)
  (n2wEq : n2w = weight n22 + weight n212 + weight n211)
  (n21wEq : n21w = weight n211 + weight n212)
  (wboN1 : Property WellBalancedOrdered n1)
  (wboN2 : Property WellBalancedOrdered (Node n2w (Node n21w n211 n21k n21v n212) n2k n2v n22)),
  (IsDeepCase n1 (Node n2w (Node n21w n211 n21k n21v n212) n2k n2v n22)) ->
  (needsRotation n2w n1w) ->
  (ValidInputImbalance n1w n2w) ->
  (Bound.TB.lt_with_empty (TreeTB _ wboN1) (Bound.TB.key n0k)) ->
  (Bound.TB.lt_with_empty (Bound.TB.key n0k) (TreeTB _ wboN2)) ->
  (not (needsSingleRotation2 (weight n22) (weight n212) (weight n211) (weight n1))) ->
  Property [ Ordered ] (double_rotation_right_node n1w n21w n2w n1 n0k n0v n21k n21v n211 n212 n2k n2v n22).
Proof.
  intros V n1w n21w n2w n1 n0k n0v n21k n21v n211 n212 n2k n2v n22 n1wEq n2wEq n21wEq wboN1 wboN2 DeepCase NR VI ordN1 ordN2 NSR2.
  apply to_list_Sorted_IsOrdered.
  + apply double_rotation_right_node_WellBalanced; auto.
    * apply (Property_Sub wboN1).
    * apply (Property_Sub wboN2).
  + cbn.
    epose proof (to_list_Sorted _ wboN1) as ssN1.
    epose proof (to_list_Sorted _ wboN2) as ssN2.
    cbn in ssN2.
    apply (StronglySorted_app _ _ _) in ssN2 as [ faN2 [ ssN21 ssnk22 ] ].
    apply (StronglySorted_app _ _ _) in ssN21 as [ faN211 [ ssN211 ssnk212 ] ].
    inversion ssnk212.
    subst.
    specialize (StronglySorted_Sorted ssnk22) as snk22.
    apply Sorted_inv in snk22 as [sn22 hdkn22].
    epose proof (BoundLt_min ordN2) as minN2.
    epose proof (BoundLt_max ordN1) as maxN1.
    SortedSmash.
    - exact binding_lt_Transitive.
    - epose proof (min_key_Sorted _ wboN2) as mks.
      rewrite mks in minN2.
      cbn in minN2.
      destruct (to_list n211) eqn:eT211; constructor.
      cbn. cbn in minN2. now destruct p.
    - epose proof (BoundLt_max ordN1) as maxN1'.
      epose proof (max_key_Sorted _ wboN1) as mks.
      destruct (to_list n1).
      * now cbn.
      * cbn in mks.
        destruct (last (p :: l)).
        ** destruct p0.
           rewrite mks in maxN1'.
           now cbn in maxN1'.
        ** easy.
    - destruct (last (to_list n212)) eqn:eMax212; auto.
      eapply (faN2 p (n2k, n2v)); [| apply list_elem_of_here].
      apply elem_of_app; right.
      apply list_elem_of_further.
      now apply last_Some_elem_of.
    - destruct (to_list n212) eqn:eT212.
      * inversion wboN2.
        inversion Hl.
        subst.
        rewrite to_list_Empty in eT212.
        subst.
        now apply Node_NoEmptyR in Hl.
      * constructor.
        now inversion H2.
    - rewrite last_app_cons.
      destruct (to_list n211) eqn:eT211.
      * inversion wboN2.
        inversion Hl.
        subst.
        rewrite to_list_Empty in eT211.
        subst.
        now apply Node_NoEmptyL in Hl.
      * rewrite last_cons_cons.
        rewrite<-eT211 in *.
        destruct (last (to_list n211)) eqn:eMax211; auto.
        now apply (faN211 p0 (n21k, n21v) ltac:(now apply last_Some_elem_of) ltac:(apply list_elem_of_here)).
Qed.

Lemma balance_deep_Ordered
  {V : Type} (n1 : Tree V) (k0 : K.t) (v0 : V) (n2 : Tree V)
  (wboN1 : Property WellBalancedOrdered n1) (wboN2 : Property WellBalancedOrdered n2) (DeepCase : IsDeepCase n1 n2)
  (VI : ValidInputImbalance (weight n1) (weight n2))
  (boundL : Bound.TB.lt_with_empty (TreeTB _ wboN1) (Bound.TB.key k0))
  (boundR : Bound.TB.lt_with_empty (Bound.TB.key k0) (TreeTB _ wboN2))
  : Property [ Ordered ] (balance_deep n1 k0 v0 n2 (Property_Sub wboN1) (Property_Sub wboN2) DeepCase).
Proof.
  epose proof (Property_Sub (Qs := WellBalanced) wboN1) as WFn1.
  epose proof (Property_Sub (Qs := WellBalanced) wboN2) as WFn2.
  funelim (balance_deep n1 k0 v0 n2 (Property_Sub wboN1) (Property_Sub wboN2) DeepCase).
  all: analyze_node_cases.
  all: match goal with
       | [ |- context [ single_rotation_right_node ] ] => eapply single_rotation_right_node_Ordered
       | [ |- context [ double_rotation_right_node ] ] => eapply double_rotation_right_node_Ordered
       | [ |- context [ double_rotation_left_node ] ] => eapply double_rotation_left_node_Ordered
       | [ |- context [ single_rotation_left_node ] ] => eapply single_rotation_left_node_Ordered
       | _ => idtac
       end.
  all: analyze_node_cases.
  Unshelve.
  all: analyze_node_cases.
  all: simpl; auto.
  - epose proof (Property_Sub (Qs := WellBalanced) wboN1) as WFn1.
    epose proof (Property_This WeightConsistent _ WFn1 _) as WCn1.
    epose proof (Property_Sub (Qs := WellBalanced) wboN2) as WFn2.
    epose proof (Property_This WeightConsistent _ WFn2 _) as WCn2.
    unfold WeightConsistent in WCn1, WCn2.
    simpl in WCn1.
    subst.
    cbn. lia.
  - pose proof (balance_deep_WellBalanced n1 k0 v0 n2 (Property_Sub wboN1) (Property_Sub wboN2) DeepCase VI) as HA.
    rewrite<-Heqcall in HA.
    unfold WellBalanced in HA.
    apply to_list_Sorted_IsOrdered.
    Unshelve.
    all: cycle 2.
    * exact [].
    * auto.
    * SortedSmash.
      + exact binding_lt_Transitive.
      + epose proof (to_list_Sorted _ wboN1) as sortedN1.
        epose proof (to_list_Sorted _ wboN2) as sortedN2.
        cbn.
        SortedSmash.
        ** Search (Bound.TB.lt_with_empty).
           epose proof (BoundLt_min boundR).
           destruct (to_list n2) eqn:eT2; try easy.
           constructor. cbn in H. 
           epose proof (min_key_Sorted _ wboN2) as mks.
           rewrite mks in H.
           rewrite eT2 in H.
           cbn in H.
           cbn.
           now destruct p.
        ** epose proof (BoundLt_max boundL).
           epose proof (max_key_Sorted _ wboN1) as mks.
           destruct (last (to_list n1)) eqn:eMax; auto.
           rewrite mks in H.
           cbn in H. destruct p.
           cbn.
           now cbn in H.
  - epose proof (Property_Sub (Qs := WellBalanced) wboN1) as WFn1.
    epose proof (Property_This WeightConsistent _ WFn1 _) as WCn1.
    epose proof (Property_Sub (Qs := WellBalanced) wboN2) as WFn2.
    epose proof (Property_This WeightConsistent _ WFn2 _) as WCn2.
    unfold WeightConsistent in WCn1, WCn2.
    simpl in WCn2.
    subst.
    cbn. lia.
Qed.

Ltac decompose_sorted n :=
  match n with
  | O => cbn [binding_lt] in *
  | S ?n' =>
      try (match goal with
           | [ H : Sorted binding_lt _ |- _ ] => apply Sorted_LocallySorted_iff in H
           | [ H : LocallySorted binding_lt [] |- _ ] => clear H
           | [ H : LocallySorted binding_lt [_] |- _ ] => clear H
           | [ H : LocallySorted binding_lt ?l |- _ ] => inversion_clear H
           end;
           decompose_sorted n')
  end.

Lemma balance_shallow_Ordered
  {V : Type} (n1 : Tree V) (k0 : K.t) (v0 : V) (n2 : Tree V)
  (wboN1 : Property WellBalancedOrdered n1) (wboN2 : Property WellBalancedOrdered n2)
  (VI : ValidInputImbalance (weight n1) (weight n2))
  (boundL : Bound.TB.lt_with_empty (TreeTB _ wboN1) (Bound.TB.key k0))
  (boundR : Bound.TB.lt_with_empty (Bound.TB.key k0) (TreeTB _ wboN2))
  : Property [ Ordered ] (balance_shallow n1 k0 v0 n2 (Property_Sub wboN1) (Property_Sub wboN2)).
Proof.
  epose proof (Property_Sub (Qs := WellBalanced) wboN1) as WFn1.
  epose proof (Property_Sub (Qs := WellBalanced) wboN2) as WFn2.
  all: pose proof (balance_shallow_WellBalanced n1 k0 v0 n2 (Property_Sub wboN1) (Property_Sub wboN2) VI) as HA.
  funelim (balance_shallow n1 k0 v0 n2 (Property_Sub wboN1) (Property_Sub wboN2)).
  all: match goal with
       | [ |- context [ balance_deep ] ] => eapply balance_deep_Ordered; auto
       | _ => idtac
       end.
   all: rewrite<-Heqcall in HA.
   all: try (now repeat constructor).
   all: epose proof (BoundLt_min boundR) as minN2.
   all: epose proof (BoundLt_max boundL) as maxN1.
   all: epose proof (Property_This Ordered _ wboN2 _) as ordN2; cbn in ordN2.
   all: epose proof (Property_This Ordered _ wboN1 _) as ordN1; cbn in ordN1.
   all: match goal with
        | [ |- Property [ Ordered ] (V2 ?k11 ?v11 ?k1 ?v1) ] =>
            repeat constructor; cbn; now cbn in minN2, maxN1
        | [ |- Property [ Ordered ] (V3 ?k11 ?v11 ?k1 ?v1 ?k12 ?v12) ] =>
            repeat constructor; cbn; cbn in minN2, maxN1; KFacts.order
        | _ => idtac
        end.
   all: apply (to_list_Sorted_IsOrdered _ HA).
   all: cbn.
   all: epose proof (to_list_Sorted _ wboN1) as ssN1;
   apply StronglySorted_Sorted in ssN1;
   cbn in ssN1.
   all: epose proof (to_list_Sorted _ wboN2) as ssN2;
   apply StronglySorted_Sorted in ssN2;
   cbn in ssN2.
   all: destruct_conjs.
   all: SortedSmash; try constructor.
   all: match goal with
        | [ |- Relations_1.Transitive binding_lt ] => exact binding_lt_Transitive
        | _ => idtac
        end.
   all: cbn in boundL, boundR.
   all: cbn in minN2, maxN1.
   all: cbn [binding_lt].
   all: unfold Bound.lt, Bound.compare, Bound.compare_k in boundR, boundL.
   all: auto.
   all: try (now decompose_sorted 9).
   all: apply Sorted_StronglySorted in ssN1; try exact binding_lt_Transitive.
   all: apply StronglySorted_app in ssN1.
   all: destruct_conjs.
   - apply StronglySorted_app in H0.
     destruct_conjs.
     apply StronglySorted_LocallySorted in H2.
     auto.
   - apply StronglySorted_app in H0.
     destruct_conjs.
     inversion_clear H3.
     apply StronglySorted_LocallySorted in H4.
     auto.
   - apply StronglySorted_app in H0.
     destruct_conjs.
     apply StronglySorted_Sorted in H3.
     inversion_clear H3.
     auto.
   - apply StronglySorted_app in H0.
     destruct_conjs.
     destruct (last (to_list n111)) eqn:eMax111; auto.
     now specialize (H0 p (k11,v11) ltac:(now apply last_Some_elem_of) ltac:(apply list_elem_of_here)).
   - clear H0.
     apply StronglySorted_Sorted in H1.
     now decompose_sorted 4.
   - match goal with 
     | [ |- context [ last (?x) ] ] => destruct (last x) eqn:eMax; auto
     end.
     now specialize (H p (k1,v1) ltac:(now apply last_Some_elem_of) ltac:(apply list_elem_of_here)).
Qed.
    
End Balanced.


