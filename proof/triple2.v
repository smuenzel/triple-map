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
From Balanced Require Import triple1.
From Corelib Require Extraction.
From Ltac2 Require Import Ltac2 String.
From stdpp Require Import sorting.
Set Default Proof Mode "Classic".


Set Printing Projections.
Module Balanced ( K : UsualOrderedTypeFull ).

Include triple1.Balanced(K).

Inductive how_to_change_existing {V : Type} :=
  | hte_Delete
  | hte_Replace (V : V)
  | hte_Unchanged
.

Definition chooser3 (T : Type) (x y z : T) : Type :=
  {v : T | v = x \/ v = y \/ v = z}.

Definition f_a (T : Type) (a b c : T) (f_b : forall x y z, chooser3 T x y z) : T :=
  proj1_sig (f_b a b c).


Definition is_Empty {V : Type} (T : Tree V) : Prop := T = Empty.
Definition is_V1 {V : Type} (T : Tree V) : Prop :=
  match T with
  | V1 _ _ => True
  | _ => False
  end.
Definition is_V2 {V : Type} (T : Tree V) : Prop :=
  match T with
  | V2 _ _ _ _ => True
  | _ => False
  end.
Definition is_V3 {V : Type} (T : Tree V) : Prop :=
  match T with
  | V3 _ _ _ _ _ _ => True
  | _ => False
  end.
Definition is_Node {V : Type} (T : Tree V) : Prop :=
  match T with
  | Node _ _ _ _ _ => True
  | _ => False
  end.




Definition f_change_existing
  {V : Type}
  (T : Tree V)
  (delete_fun : { t : Tree V | t = T } -> Tree V)
  (replace_fun : { t : Tree V | t = T } -> V -> Tree V)
  (unchanged_fun : { t : Tree V | t = T } -> Tree V)
  : Type :=
  let T' := exist _ T eq_refl in
  K.t -> V ->
  { r : Tree V | r = delete_fun T' \/ (exists v', r = replace_fun T' v') \/ r = unchanged_fun T' }
  .

Definition f_change_missing
  {V : Type}
  (T : Tree V)
  (insert_fun : { t : Tree V | t = T } -> K.t -> V -> Tree V)
  (unchanged_fun : { t : Tree V | t = T } -> Tree V)
  (k : K.t)
  : Type :=
  let T' := exist _ T eq_refl in
  { r : Tree V | (exists v', r = insert_fun T' k v') \/ r = unchanged_fun T' }
  .

Definition change_unchanged {V : Type} (T : Tree V) := T.

Definition change_delete_V1 {V : Type} (T : Tree V) : Tree V := Empty.

Program Definition change_insert_Empty {V : Type} {T' : Tree V} {is : is_Empty T'} (T : {t : Tree V | t = T'}) (k : K.t) (v : V) :=
  match T with
  | Empty => V1 k v
  | V1 _ _ | V2 _ _ _ _ | V3 _ _ _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_Empty in *; destruct T; subst; intuition; inversion Heq_T.

Program Definition change_replace_V1 {V : Type} {T' : Tree V} {is : is_V1 T'} (T : {t : Tree V | t = T'}) (v : V) :=
  match T with
  | (V1 k1 v1) => V1 k1 v
  | Empty | V2 _ _ _ _ | V3 _ _ _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V1 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_insert_V1_less {V : Type} {T' : Tree V} {is : is_V1 T'} (T : {t : Tree V | t = T'}) (k : K.t) (v : V) :=
  match T with
  | (V1 k1 v1) => V2 k v k1 v1
  | Empty | V2 _ _ _ _ | V3 _ _ _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V1 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_insert_V1_greater {V : Type} {T' : Tree V} {is : is_V1 T'} (T : {t : Tree V | t = T'}) (k : K.t) (v : V) :=
  match T with
  | (V1 k1 v1) => V2 k1 v1 k v
  | Empty | V2 _ _ _ _ | V3 _ _ _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V1 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_delete_V2_top {V : Type} {T' : Tree V} {is : is_V2 T'} (T : {t : Tree V | t = T'}) :=
  match T with
  | (V2 k11 v11 k1 v1) => V1 k11 v11
  | Empty | V1 _ _ | V3 _ _ _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V2 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_delete_V2_bottom {V : Type} {T' : Tree V} {is : is_V2 T'} (T : {t : Tree V | t = T'}) :=
  match T with
  | (V2 k11 v11 k1 v1) => V1 k1 v1
  | Empty | V1 _ _ | V3 _ _ _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V2 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_replace_V2_top {V : Type} {T' : Tree V} {is : is_V2 T'} (T : {t : Tree V | t = T'}) (v : V) :=
  match T with
  | (V2 k11 v11 k1 v1) => V2 k11 v11 k1 v
  | Empty | V1 _ _ | V3 _ _ _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V2 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_replace_V2_bottom {V : Type} {T' : Tree V} {is : is_V2 T'} (T : {t : Tree V | t = T'}) (v : V) :=
  match T with
  | (V2 k11 v11 k1 v1) => V2 k11 v k1 v1
  | Empty | V1 _ _ | V3 _ _ _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V2 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_insert_V2_bottom {V : Type} {T' : Tree V} {is : is_V2 T'} (T : {t : Tree V | t = T'}) (k : K.t) (v : V) :=
  match T with
  | (V2 k11 v11 k1 v1) => V3 k v k11 v11 k1 v1
  | Empty | V1 _ _ | V3 _ _ _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V2 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_insert_V2_middle {V : Type} {T' : Tree V} {is : is_V2 T'} (T : {t : Tree V | t = T'}) (k : K.t) (v : V) :=
  match T with
  | (V2 k11 v11 k1 v1) => V3 k11 v11 k v k1 v1
  | Empty | V1 _ _ | V3 _ _ _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V2 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_insert_V2_top {V : Type} {T' : Tree V} {is : is_V2 T'} (T : {t : Tree V | t = T'}) (k : K.t) (v : V) :=
  match T with
  | (V2 k11 v11 k1 v1) => V3 k11 v11 k1 v1 k v
  | Empty | V1 _ _ | V3 _ _ _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V2 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_delete_V3_top {V : Type} {T' : Tree V} {is : is_V3 T'} (T : {t : Tree V | t = T'}) :=
  match T with
  | (V3 k11 v11 k1 v1 k12 v12) => V2 k11 v11 k12 v12
  | Empty | V1 _ _ | V2 _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V3 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_delete_V3_left {V : Type} {T' : Tree V} {is : is_V3 T'} (T : {t : Tree V | t = T'}) :=
  match T with
  | (V3 k11 v11 k1 v1 k12 v12) => V2 k1 v1 k12 v12
  | Empty | V1 _ _ | V2 _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V3 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_delete_V3_right {V : Type} {T' : Tree V} {is : is_V3 T'} (T : {t : Tree V | t = T'}) :=
  match T with
  | (V3 k11 v11 k1 v1 k12 v12) => V2 k11 v11 k1 v1
  | Empty | V1 _ _ | V2 _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V3 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_replace_V3_top {V : Type} {T' : Tree V} {is : is_V3 T'} (T : {t : Tree V | t = T'}) (v : V) :=
  match T with
  | (V3 k11 v11 k1 v1 k12 v12) => V3 k11 v11 k1 v k12 v12
  | Empty | V1 _ _ | V2 _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V3 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_replace_V3_left {V : Type} {T' : Tree V} {is : is_V3 T'} (T : {t : Tree V | t = T'}) (v : V) :=
  match T with
  | (V3 k11 v11 k1 v1 k12 v12) => V3 k11 v k1 v1 k12 v12
  | Empty | V1 _ _ | V2 _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V3 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_replace_V3_right {V : Type} {T' : Tree V} {is : is_V3 T'} (T : {t : Tree V | t = T'}) (v : V) :=
  match T with
  | (V3 k11 v11 k1 v1 k12 v12) => V3 k11 v11 k1 v1 k12 v
  | Empty | V1 _ _ | V2 _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V3 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_insert_V3_below_11 {V : Type} {T' : Tree V} {is : is_V3 T'} (T : {t : Tree V | t = T'}) (k : K.t) (v : V) :=
  match T with
  | (V3 k11 v11 k1 v1 k12 v12) => Node 5 (V2 k v k11 v11) k1 v1 (V1 k12 v12)
  | Empty | V1 _ _ | V2 _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V3 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_insert_V3_between_11_1 {V : Type} {T' : Tree V} {is : is_V3 T'} (T : {t : Tree V | t = T'}) (k : K.t) (v : V) :=
  match T with
  | (V3 k11 v11 k1 v1 k12 v12) => Node 5 (V2 k11 v11 k v) k1 v1 (V1 k12 v12)
  | Empty | V1 _ _ | V2 _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V3 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_insert_V3_between_1_12 {V : Type} {T' : Tree V} {is : is_V3 T'} (T : {t : Tree V | t = T'}) (k : K.t) (v : V) :=
  match T with
  | (V3 k11 v11 k1 v1 k12 v12) => Node 5 (V2 k11 v11 k1 v1) k v (V1 k12 v12)
  | Empty | V1 _ _ | V2 _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V3 in *; destruct T, x; subst; intuition; inversion Heq_T.

Program Definition change_insert_V3_above_12 {V : Type} {T' : Tree V} {is : is_V3 T'} (T : {t : Tree V | t = T'}) (k : K.t) (v : V) :=
  match T with
  | (V3 k11 v11 k1 v1 k12 v12) => Node 5 (V2 k11 v11 k1 v1) k12 v12 (V1 k v)
  | Empty | V1 _ _ | V2 _ _ _ _ | Node _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_V3 in *; destruct T, x; subst; intuition; inversion Heq_T.


(*
Program Fixpoint remove_min {V : Type} {A : Type} (T : Tree V) {ne : notEmpty T} (callback : Tree V -> K.t -> V -> A) : A :=
  match T with
  | Empty => False_rect A _
  | V1 k v => callback Empty k v
  | V2 k11 v11 k1 v1 => callback (V1 k11 v11) k1 v1
  | V3 k11 v11 k1 v1 k12 v12 => callback (V2 k1 v1 k12 v12) k11 v11
  | Node w n1 k v n2 =>
      let n1' 

  end.


(* aka split_min *)
Equations split_right {V : Type} (T1 : Tree V) (T2 : Tree V) (wbo1 : Property WellBalancedOrdered T1) (wbo2 : Property WellBalancedOrdered T2) :=
   split_right 

Program Definition change_delete_node_top {V : Type} {T' : Tree V} {is : is_Node T'} {wbo : Property WellBalancedOrdered T'} (T : {t : Tree V | t = T'}) :=
  match T with
  | (Node w0 n1 k v n2) =>
      let w1 := weight n1 in
      let w2 := weight n2 in
      if lt_dec w1 w2 
      then split_right n1 n2
      else split_left n1 n2
  | Empty | V1 _ _ | V2 _ _ _ _ | V3 _ _ _ _ _ _ => False_rect (Tree V) _
  end.
Solve All Obligations with intros; subst filtered_var; unfold is_node in *; destruct T, x; subst; intuition; inversion Heq_T.
 *)






Program Fixpoint change {V : Type} 
  (T : Tree V)
  (k : K.t)
  (on_existing : forall T delete_fun replace_fun unchanged_fun, f_change_existing T delete_fun replace_fun unchanged_fun)
  (on_missing : forall T insert_fun unchanged_fun k', f_change_missing T insert_fun unchanged_fun k')
  (wbo : Property WellBalancedOrdered T) : Tree V :=
  match T with
  | Empty => proj1_sig (on_missing T change_insert_Empty change_unchanged k)
  | V1 k1 v =>
      match K.compare k k1 with
      | Eq => proj1_sig (on_existing T change_delete_V1 change_replace_V1 change_unchanged k1 v)
      | Lt => proj1_sig (on_missing T change_insert_V1_less change_unchanged k)
      | Gt => proj1_sig (on_missing T change_insert_V1_greater change_unchanged k)
      end
  | V2 k11 v11 k1 v1 =>
      match K.compare k k1 with
      | Eq => proj1_sig (on_existing T change_delete_V2_top change_replace_V2_top change_unchanged k1 v1)
      | Lt =>
          match K.compare k k11 with
          | Eq => proj1_sig (on_existing T change_delete_V2_bottom change_replace_V2_bottom change_unchanged k11 v11)
          | Lt => proj1_sig (on_missing T change_insert_V2_bottom change_unchanged k)
          | Gt => proj1_sig (on_missing T change_insert_V2_middle change_unchanged k)
          end
      | Gt => proj1_sig (on_missing T change_insert_V2_top change_unchanged k)
      end
  | V3 k11 v11 k1 v1 k12 v12 =>
      match K.compare k k1 with
      | Eq => proj1_sig (on_existing T change_delete_V3_top change_replace_V3_top change_unchanged k1 v1)
      | Lt => 
          match K.compare k k11 with
          | Eq => proj1_sig (on_existing T change_delete_V3_left change_replace_V3_left change_unchanged k11 v11)
          | Lt => proj1_sig (on_missing T change_insert_V3_below_11 change_unchanged k)
          | Gt => proj1_sig (on_missing T change_insert_V3_between_11_1 change_unchanged k)
          end
      | Gt =>
          match K.compare k k12 with
          | Eq => proj1_sig (on_existing T change_delete_V3_right change_replace_V3_right change_unchanged k12 v12)
          | Lt => proj1_sig (on_missing T change_insert_V3_between_1_12 change_unchanged k)
          | Gt => proj1_sig (on_missing T change_insert_V3_above_12 change_unchanged k)
          end
      end
  | _ => Empty
  end.
Solve All Obligations with intros; subst; now cbn.





(*
Program Fixpoint insert_or_replace {V: Type} (T : Tree V) (k : K.t) (v' : V) (wbo : Property WellBalancedOrdered T) : Tree V :=
  match T with
  | Empty => V1 k v'
  | V1 k1 v => 
      match K.compare k k1 with
      | Eq => V1 k v'
      | Lt => V2 k v' k1 v
      | Gt => V2 k1 v k v'
      end
  | V2 k11 v11 k1 v1 =>
      match K.compare k k1 with
      | Eq => V2 k11 v11 k1 v'
      | Lt =>
          match K.compare k k11 with
          | Eq => V2 k11 v' k1 v1
          | Lt => V3 k v' k11 v11 k1 v1
          | Gt => V3 k11 v11 k v' k1 v1
          end
      | Gt =>
          V3 k11 v11 k1 v1 k v'
      end
  | V3 k11 v11 k1 v1 k12 v12 => 
      match K.compare k k1 with
      | Eq => V3 k11 v11 k1 v' k12 v12
      | Lt =>
          match K.compare k k11 with
          | Eq => V3 k11 v' k1 v1 k12 v12
          | Lt => Node 5 (V2 k v' k11 v11) k1 v1 (V1 k12 v12)
          | Gt => Node 5 (V2 k11 v11 k v') k1 v1 (V1 k12 v12)
          end
      | Gt =>
          match K.compare k k12 with
          | Eq => V3 k11 v11 k1 v1 k12 v'
          | Lt => Node 5 (V2 k11 v11 k1 v1) k v' (V1 k12 v12)
          | Gt => Node 5 (V2 k11 v11 k1 v1) k12 v12 (V1 k v')
          end
      end
  | Node w l k1 v1 r =>
      match K.compare k k1 with
      | Eq => Node w l k1 v' r
      | Lt => balance_shallow (insert_or_replace l k v' _) k1 v1 r _ _
      | Gt => balance_shallow l k1 v1 (insert_or_replace r k v' _) _ _
      end
  end.
Next Obligation.
  intros.
  subst.
  now inversion wbo.
Qed.
Next Obligation.
  intros.
 *)


End Balanced.
