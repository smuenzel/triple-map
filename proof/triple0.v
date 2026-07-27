
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Structures.Orders.
From Stdlib Require Import Structures.OrdersFacts.
From Stdlib Require Import Program.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Recdef.
From Stdlib Require Import Decidable.
From Stdlib Require Import Compare_dec.
Require Import Program.Tactics.
Require Import Stdlib.Logic.PropExtensionality.
From Stdlib Require Import List.
Import ListNotations.
From Equations Require Import Equations.
From Equations.Prop Require Import Logic.
From Corelib Require Extraction.
From Ltac2 Require Import Ltac2 String.
Set Default Proof Mode "Classic".

Set Printing Projections.
Module Balanced ( K : UsualOrderedTypeFull ).

Module KFacts := OrderedTypeFacts K.

Inductive Tree (V: Type) : Type :=
  | Empty : Tree V
  | V1 : K.t -> V -> Tree V
  | V2 : K.t -> V -> K.t -> V -> Tree V (* LEFT; TOP *)
  | V3 : K.t -> V -> K.t -> V -> K.t -> V -> Tree V (* LEFT; TOP; RIGHT *)
  | Node : nat -> Tree V -> K.t -> V -> Tree V -> Tree V
.

Arguments Empty {V}.
Arguments V1 {V}.
Arguments V2 {V}.
Arguments V3 {V}.
Arguments Node {V}.

Inductive IsNode {V : Type } : Tree V -> Prop :=
  | IsNode_intro : forall (n : nat) (l : Tree V) (k : K.t) (v : V) (r : Tree V), IsNode (Node n l k v r)
.

Definition weight {V : Type} (t : Tree V) : nat :=
  match t with
  | Empty => 1
  | V1 _ _ => 2
  | V2 _ _ _ _ => 3
  | V3 _ _ _ _ _ _ => 4
  | Node n _ _ _ _ => n
  end.

(* Balanced: omega2 * n1 > 2 * n2*)
Definition omega2 := 5.
Definition alpha2 := 3.
Definition delta2 := 0.

Definition needsRotation (deep_side shallow_side : nat) : Prop :=
  2 * deep_side > omega2 * shallow_side + delta2
  .

Definition needsSingleRotation (inner_size outer_size : nat) :=
  2 *inner_size > alpha2 * outer_size.

Definition BalancedSize (n1 n2 : nat) : Prop :=
  (omega2 * n1 + delta2 >= 2 * n2) /\ (omega2 * n2 + delta2 >= 2 * n1).

Arguments BalancedSize n1 n2 /.

(* From the perspective of the left subtree *)
Definition needsSingleRotation2 (n11w n121w n122w n2w : nat) : Prop :=
  not (
  (BalancedSize n11w n121w) /\ (BalancedSize n122w n2w) /\ (BalancedSize (n11w + n121w) (n122w + n2w))).

Definition needsSingleRotationAnalyzeLeft {V : Type} (n11w : nat) (n12 : Tree V) (n2w : nat) : Prop :=
  match n12 with
  | Empty => True
  | V1 _ _ => True
  | V2 _ _ _ _ => True
  | V3 _ _ _ _ _ _ => True
  | Node _ n11 _ _ n12 => needsSingleRotation2 n11w (weight n11) (weight n12) n2w
  end.

Definition needsSingleRotationAnalyzeRight {V : Type} (n1w : nat) (n21 : Tree V) (n22w : nat) : Prop :=
  match n21 with
  | Empty => True
  | V1 _ _ => True
  | V2 _ _ _ _ => True
  | V3 _ _ _ _ _ _ => True
  | Node _ n211 _ _ n212 => needsSingleRotation2 n22w (weight n212) (weight n211) n1w
  end.

Definition balanceConditionLeftRotation (lsz rsz : nat)
  : {needsRotation lsz rsz} + {~ needsRotation lsz rsz} := lt_dec _ _.

Definition balanceConditionRightRotation (lsz rsz : nat)
  : {needsRotation rsz lsz} + {~ needsRotation rsz lsz} := lt_dec _ _.

Definition balanceConditionLeftSingle (lsz rsz : nat)
  : {needsSingleRotation lsz rsz} + {~ needsSingleRotation lsz rsz} := lt_dec _ _.

Definition balanceConditionRightSingle (lsz rsz : nat) : 
  {needsSingleRotation rsz lsz} + {~ needsSingleRotation rsz lsz} :=
  lt_dec _ _.

Definition balanceConditionLeftSingle2 (n11w n121w n122w n2w : nat)
  : {needsSingleRotation2 n11w n121w n122w n2w} + {~ needsSingleRotation2 n11w n121w n122w n2w}.
Proof.
  unfold needsSingleRotation2.
  unfold BalancedSize.
  unfold omega2, delta2.
  repeat rewrite Nat.add_0_r.
  apply sumbool_not.
  destruct (le_dec (2 * n121w) (5 * n11w)),
           (le_dec (2 * n11w) (5 * n121w)),
           (le_dec (2 * n2w) (5 * n122w)),
           (le_dec (2 * n122w) (5 * n2w)),
           (le_dec (2 * (n122w + n2w)) (5 * (n11w + n121w))),
           (le_dec (2 * (n11w + n121w)) (5 * (n122w + n2w))).
  all:try (left; lia); try (right; lia).
Defined.

Definition balanceConditionRightSingle2 (n1w n211w n212w n22w : nat)
  : {needsSingleRotation2 n22w n212w n211w n1w} + {~ needsSingleRotation2 n22w n212w n211w n1w}.
Proof.
  unfold needsSingleRotation2.
  unfold BalancedSize.
  unfold omega2, delta2.
  repeat rewrite Nat.add_0_r.
  apply sumbool_not.
  destruct (le_dec (2 * n212w) (5 * n22w)),
           (le_dec (2 * n22w) (5 * n212w)),
           (le_dec (2 * n1w) (5 * n211w)),
           (le_dec (2 * n211w) (5 * n1w)),
           (le_dec (2 * (n211w + n1w)) (5 * (n22w + n212w))),
           (le_dec (2 * (n22w + n212w)) (5 * (n211w + n1w))).
  all:try (left; lia); try (right; lia).
Defined.

(* 80% is just about the maximum that can be restored back to balance by a rotation *)
Definition ValidInputImbalance (n1w n2w : nat) : Prop :=
  10 * n1w < 8 * (n1w + n2w) /\ 10 * n2w < 8 * (n1w + n2w).

(* The bigger side is always a Node *)
Lemma InvalidInputImbalanceLowerBound (n1w : nat) (n2w : nat) :
  n1w >= 1 -> n2w >= 1 -> not (ValidInputImbalance n1w n2w) -> n1w > 3 \/ n2w > 3.
Proof.
  unfold ValidInputImbalance.
  intros.
  lia.
Qed.

Program Definition weight_inspect {V : Type} (t : Tree V) : {n : nat | n = weight t} :=
  weight t.
(*
Opaque weight_inspect.
 *)

Function realweight {V : Type} (t : Tree V) : nat :=
  match t with
  | Empty => 1
  | V1 _ _ => 2
  | V2 _ _ _ _ => 3
  | V3 _ _ _ _ _ _ => 4
  | Node _ l _ _ r => realweight l + realweight r
  end.

Lemma realweight_GT0 {V : Type} (T : Tree V) : realweight T >= 1.
Proof.
  induction T; cbn; lia.
Qed.

(* claude wrote InList/SubList*)

Class InList {A : Type} (x : A) (l : list A) : Prop :=
  in_list : In x l.

(* Instances that cover any position in a concrete list *)
#[export] Instance InList_head {A} (x : A) (xs : list A) : InList x (x :: xs).
Proof. left. reflexivity. Qed.

#[export] Instance InList_tail {A} (x : A) (y : A) (xs : list A)
  (H : InList x xs) : InList x (y :: xs).
Proof. right. exact in_list. Qed.

Class SubList {A : Type} (sub super : list A) : Prop :=
  sub_list : forall x, In x sub -> In x super.

(* Base case: empty list is a sublist of anything *)
#[export] Instance SubList_nil {A} (l : list A) : SubList [] l.
Proof. intros x H. inversion H. Qed.

(* Recursive case: head must be InList, tail must be SubList *)
#[export] Instance SubList_cons {A} (x : A) (xs l : list A)
(H1 : InList x l) (H2 : SubList xs l) : SubList (x :: xs) l.
Proof.
  intros y Hy. destruct Hy as [<- | Hy].
  - exact in_list.
  - exact (sub_list y Hy).
Qed.

Lemma InList_from_sub {A} (x : A) {sub super : list A}
  (H1 : InList x sub) (H2 : SubList sub super) : InList x super.
Proof. exact (sub_list x in_list). Qed.

Lemma SubList_tail {A} (x : A) (xs ys : list A) :
  SubList (x :: xs) ys -> SubList xs ys.
Proof. intros H y Hy. apply H. right. exact Hy. Qed.



Definition PropF {V : Type} := Tree V -> Prop.

Inductive Property {V : Type} (Ps : list PropF) : Tree V -> Prop :=
  | PropertyEmpty (HPs : Forall (fun P => P Empty) Ps) : Property Ps Empty
  | PropertyV1 (k : K.t) (v : V) (HPs : Forall (fun P => P (V1 k v)) Ps) : Property Ps (V1 k v)
  | PropertyV2 (k1 : K.t) (v1 : V) (k2 : K.t) (v2 : V) (HPs : Forall (fun P => P (V2 k1 v1 k2 v2)) Ps) : Property Ps (V2 k1 v1 k2 v2)
  | PropertyV3 (k1 : K.t) (v1 : V) (k2 : K.t) (v2 : V) (k3 : K.t) (v3 : V) (HPs : Forall (fun P => P (V3 k1 v1 k2 v2 k3 v3)) Ps) : Property Ps (V3 k1 v1 k2 v2 k3 v3)
  | PropertyNode (n : nat) (l : Tree V) (k : K.t) (v : V) (r : Tree V) (HPs : Forall (fun P => P (Node n l k v r)) Ps) (Hl : Property Ps l) (Hr : Property Ps r) : Property Ps (Node n l k v r)
      .

Lemma Property_This : forall {V : Type} {Ps : list PropF} (POne : PropF) (T : Tree V),
  Property Ps T -> `{ InList POne Ps } -> POne T.
Proof.
  intros V Ps POne T Hprop Hin.
  induction T eqn:eT; inversion Hprop.
  all: rewrite Forall_forall in HPs.
  all: now specialize (HPs POne Hin).
Qed.

Lemma Property_This' : forall {V : Type} {POne : PropF} {T : Tree V},
  Property [ POne ] T -> POne T.
Proof.
  intros V POne T Hprop.
  now epose proof (Property_This POne _ Hprop ltac:(simpl; auto)) as H.
Qed.

Lemma Property_In : forall {V : Type} {Ps : list (Tree V -> Prop)} (POne : PropF) {T : Tree V},
  Property Ps T -> `{ InList POne Ps } -> Property [ POne ] T.
Proof.
  intros V Ps POne T Hprop Hin.
  epose proof (Property_This POne _ Hprop Hin) as PT.
  induction Hprop.
  all: try now repeat constructor.
  epose proof (Property_This POne _ Hprop1 Hin) as Hp1.
  epose proof (Property_This POne _ Hprop2 Hin) as Hp2.
  constructor; auto.
Qed.

Lemma Property_Empty {V : Type} {T : Tree V}:
  Property [] T.
Proof.
  induction T; repeat constructor; auto.
Qed.

Lemma Property_Sub {V : Type} {Ps Qs : list (Tree V -> Prop)} {T : Tree V}
  `{SubList _ Qs Ps} : Property Ps T -> Property Qs T.
Proof.
  intros.
  induction Qs.
  - induction T; repeat constructor; apply Property_Empty.
  - induction T; repeat constructor.
    all: epose proof (Property_In _ H0 (InList_from_sub a _ H)) as HS.
    all: try now apply Property_This' in HS.
    all: epose proof (SubList_tail _ _ _ H) as SL.
    all: try (specialize (IHQs SL); now inversion IHQs).
    all: inversion H0; intuition; subst; 
    inversion H1; intuition.
Qed.


Lemma Property_Compose {V : Type} {Ps1 : list (Tree V -> Prop)} {Ps2 : list (Tree V -> Prop)} {T : Tree V}:
  (Property Ps1 T /\ Property Ps2 T) <-> Property (Ps1 ++ Ps2) T.
Proof.
  split.
  - intros [P1 P2].
    induction T. 
    + inversion P1. inversion P2. constructor.
      now rewrite Forall_app.
    + inversion P1. inversion P2. constructor.
      now rewrite Forall_app.
    + inversion P1. inversion P2. constructor.
      now rewrite Forall_app.
    + inversion P1. inversion P2. constructor.
      now rewrite Forall_app.
    + inversion P1. inversion P2. constructor.
      now rewrite Forall_app.
      all:auto.
  - intros P.
    induction T.
    all: inversion P. 
    all: rewrite Forall_app in HPs.
    all: repeat constructor; intuition.
Qed.

Lemma Property_Assemble {V : Type} {Ps1 : list (Tree V -> Prop)} {Ps2 : list (Tree V -> Prop)} {T : Tree V} (Ps3 : list (Tree V -> Prop)) {sl : SubList Ps3 (Ps1 ++ Ps2)}:
  Property Ps1 T -> Property Ps2 T -> Property Ps3 T.
Proof.
  intros P1 P2.
  pose proof (conj P1 P2) as P12.
  rewrite Property_Compose in P12.
  now apply Property_Sub.
Qed.

Ltac property_decompose :=
  repeat match goal with
  | [ |- context [ Property (?hd :: ?tl) ?T ] ]=>
      match tl with
      | [] => fail 1
      | _ => 
          let x := fresh "x" in
          assert ([ hd ] ++ tl = hd :: tl) as x by auto;
          rewrite<-x;
          rewrite<-Property_Compose;
          clear x
      end
  end.

Definition WeightConsistent {V : Type} (T : Tree V) : Prop :=
  weight T = realweight T.

Arguments WeightConsistent {V} !T /.

Definition NodeNodeWellFormed {V : Type} (n1w : nat) (n1 n2 : Tree V) : Prop :=
  match n1, n2 with
  | Empty, Empty => False
  | (V1 _ _), Empty => False
  | Empty, (V1 _ _) => False
  | (V1 _ _), (V1 _ _) => False
  | (V2 _ _ _ _), Empty => False
  | Empty, (V2 _ _ _ _) => False
  | _, _ => n1w > 4
  end.

Arguments NodeNodeWellFormed {V} n1w n1 n2/.

Definition NodeWellFormed {V : Type} (T : Tree V) : Prop :=
  match T with
  | Empty => True
  | V1 _ _ => True
  | V2 _ _ _ _ => True
  | V3 _ _ _ _ _ _ => True
  | Node n1w n1 _ _ n2 => NodeNodeWellFormed n1w n1 n2
  end.

Definition WellFormed {V : Type} :=
  [ (NodeWellFormed (V := V)); WeightConsistent].

Lemma WellFormed_NodeSize {V : Type} {Ps : list (PropF (V:=V))} (n0w : nat) (n1 : Tree V) (k0 : K.t) (v0 : V) (n2 : Tree V)
  `{SubList _ WellFormed Ps}:
  Property Ps (Node n0w n1 k0 v0 n2) -> n0w > 4 /\ n0w = weight n1 + weight n2.
Proof.
  intros WF'.
  epose proof (Property_Sub WF') as WF.
  unfold WellFormed in *.
  epose proof (Property_In NodeWellFormed WF _) as NWF.
  epose proof (Property_In WeightConsistent WF _) as WC.
  split.
  - inversion NWF. inversion HPs. subst.
    simpl in H7. unfold NodeNodeWellFormed in H7.
    destruct n1, n2; auto; try contradiction.
  - epose proof (Property_This WeightConsistent _ WC ltac:(simpl; auto)).
    simpl in *.
    inversion WC.
    apply Property_This' in Hl.
    apply Property_This' in Hr.
    unfold WeightConsistent in *.
    lia.
Qed.


Lemma NodeWellFormed_NodeSize {V : Type} (n0w : nat) (n1 : Tree V) (k0 : K.t) (v0 : V) (n2 : Tree V) :
  Property [ NodeWellFormed ] (Node n0w n1 k0 v0 n2) -> n0w > 4.
Proof.
  intros.
  apply Property_This' in H.
  simpl in *. unfold NodeNodeWellFormed in *.
  destruct n1,n2; easy.
Qed.

Lemma WeightConsistent_Size {V : Type} {Ps : list (PropF (V:=V))} (n : Tree V) `{InList _ WeightConsistent Ps}:
  Property Ps n -> weight n >= 1.
Proof.
  intro WC'. 
  epose proof (Property_In WeightConsistent WC' _) as WC.
  clear WC'.
  induction n.
  all: cbn; try lia.
  epose proof (Property_This' WC) as WC'.
  cbn in WC'.
  pose proof (realweight_GT0 n2).
  pose proof (realweight_GT0 n3).
  lia.
Qed.

Lemma WellFormed_Size {V : Type} {Ps : list (PropF (V:=V))} (n : Tree V) `{SubList _ WellFormed Ps}:
  Property Ps n -> weight n >= 1.
Proof.
  intro WF'. 
  epose proof (Property_Sub WF') as WF.
  epose proof (Property_In NodeWellFormed WF _) as NWF.
  epose proof (Property_In WeightConsistent WF _) as WC.
  induction WC; simpl; auto.
  epose proof (WellFormed_NodeSize _ _ _ _ _ WF). lia.
Qed.

Lemma NodeWellFormed_Size {V : Type} {Ps : list (PropF (V:=V))} (n : Tree V) `{InList _ NodeWellFormed Ps}:
  Property Ps n -> weight n >= 1.
Proof.
  intro. 
  epose proof (Property_In NodeWellFormed H0 H) as NWF.
  epose proof (Property_This' NWF) as WFt.
  induction NWF; simpl; auto.
  epose proof (Property_This' NWF1) as WFl.
  epose proof (Property_This' NWF2) as WFr.
  simpl in *.
  destruct l,r; simpl in *; try easy; try lia.
Qed.


Lemma BalancedSize_NoRotation (n1 n2 : nat) :
  BalancedSize n1 n2 <-> (not (needsRotation n1 n2) /\ not (needsRotation n2 n1)).
Proof.
  split.
  - unfold BalancedSize. unfold needsRotation. 
    unfold alpha2. unfold omega2.
    intros. destruct_conjs.
    intuition; lia.
  - unfold BalancedSize. unfold needsRotation.
    unfold omega2; unfold alpha2.
    intros.
    destruct_conjs.
    intuition.
    lia. lia.
Qed.

Definition BalancedWeight {V : Type} (T : Tree V) : Prop :=
  match T with
  | Empty => True
  | V1 _ _ => True
  | V2 _ _ _ _ => True
  | V3 _ _ _ _ _ _ => True
  | Node _ l _ _ r => BalancedSize (weight l) (weight r)
  end.

Definition BalancedRealWeight {V : Type} (T : Tree V) : Prop :=
  match T with
  | Empty => True
  | V1 _ _ => True
  | V2 _ _ _ _ => True
  | V3 _ _ _ _ _ _ => True
  | Node _ l _ _ r => BalancedSize (realweight l) (realweight r)
  end.

Lemma restoreBalance (n1 n11 n12 n121 n122 n2 : nat) :
  n1 >= 1 -> n11 >= 1 -> n12 >= 1 -> n2 >= 1
  -> (n1 = n11 + n12) -> (n12 = n121 + n122)
  -> BalancedSize n11 n12 -> BalancedSize n121 n122
  -> ValidInputImbalance n1 n2
  -> not (BalancedSize n1 n2)
  -> n1 > n2
  (* Double Rotation *)
  -> (
    ( (BalancedSize n11 n121) /\ (BalancedSize n122 n2) /\ (BalancedSize (n11 + n121) (n122 + n2)) )
    \/
    (* Single Rotation *)
    (BalancedSize n11 (n12 + n2)) /\ (BalancedSize n12 n2)
    )
    .
Proof.
  intros.
  unfold BalancedSize, ValidInputImbalance, omega2, delta2 in *.
  lia.
Qed.

Lemma restoreBalanceWithSpecificRotation (n1 n11 n12 n121 n122 n2 : nat) :
  n1 >= 1 -> n11 >= 1 -> n12 >= 1 -> n2 >= 1 -> (n121 > 0) -> (n122 > 0)
  -> (n1 = n11 + n12) -> (n12 = n121 + n122)
  -> BalancedSize n11 n12 -> BalancedSize n121 n122
  -> ValidInputImbalance n1 n2
  -> not (BalancedSize n1 n2)
  -> n1 > n2
  (* Double Rotation *)
  -> (
    ( (not (needsSingleRotation2 n11 n121 n122 n2 )) /\ (BalancedSize n11 n121) /\ (BalancedSize n122 n2) /\ (BalancedSize (n11 + n121) (n122 + n2)) )
    \/
    (* Single Rotation *)
    (needsSingleRotation2 n11 n121 n122 n2) /\ (BalancedSize n11 (n12 + n2)) /\ (BalancedSize n12 n2)
    )
    .
Proof.
  intros.
  unfold needsSingleRotation2, BalancedSize, ValidInputImbalance, alpha2, omega2, delta2 in *.
  lia.
Qed.

Definition IsShallowRotationCase
  {V:Type}
  (n1 : Tree V)
  (n2 : Tree V)
  : Prop
  :=
  match n1, n2 with
(*$ 
open Core
open Case_writer

let shallow_cases = Sexp.load_sexps_conv_exn "../shallow_cases.sexp" Line.t_of_sexp
let fusion_cases = Sexp.load_sexps_conv_exn "../fusion_cases.sexp" Line.t_of_sexp
let () = Printf.printf "\n"
let () = List.iter shallow_cases ~f:(fun l ->
  Printf.printf "%s\n" (Line.to_rocq_boolean l)
   )
*)
  | Empty, Empty => True
  | V1 k1 v1, Empty => True
  | Empty, V1 k2 v2 => True
  | V1 k1 v1, V1 k2 v2 => True
  | V2 k11 v11 k1 v1, Empty => True
  | Empty, V2 k21 v21 k2 v2 => True
  | V3 k11 v11 k1 v1 k12 v12, Empty => True
  | Empty, V3 k21 v21 k2 v2 k22 v22 => True
  | Node _ (V3 k111 v111 k11 v11 k112 v112) k1 v1 (V1 k12 v12), V1 k2 v2 => True
  | V1 k1 v1, Node _ (V1 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222) => True
  | Node _ (Node 5 n111 k11 v11 n112) k1 v1 (V1 k12 v12), V1 k2 v2 => True
  | V1 k1 v1, Node _ (V1 k21 v21) k2 v2 (Node 5 n221 k22 v22 n222) => True
  | Node _ (V1 k11 v11) k1 v1 (V3 k121 v121 k12 v12 k122 v122), V1 k2 v2 => True
  | V1 k1 v1, Node _ (V3 k211 v211 k21 v21 k212 v212) k2 v2 (V1 k22 v22) => True
  | Node _ (V1 k11 v11) k1 v1 (Node _ (V1 k121 v121) k12 v12 (V2 k1221 v1221 k122 v122)), V1 k2 v => True
  | V1 k1 v1, Node _ (Node _ (V2 k2111 v2111 k211 v211) k21 v21 (V1 k212 v212)) k2 v2 (V1 k22 v22) => True
  | Node _ (V1 k11 v11) k1 v1 (Node _ (V2 k1211 v1211 k121 v121) k12 v12 (V1 k122 v122)), V1 k2 v2 => True
  | V1 k1 v1, Node _ (Node _ (V1 k211 v211) k21 v21 (V2 k2121 v2121 k212 v212)) k2 v2 (V1 k22 v22) => True
  | Node _ (V2 k111 v111 k11 v11) k1 v1 (Node _ (V2 k1211 v1211 k121 v121) k12 v12 (V1 k122 v122)), V1 k2 v2 => True
  | V1 k1 v1, Node _ (Node _ (V1 k211 v211) k21 v21 (V2 k2121 v2121 k212 v212)) k2 v2 (V2 k221 v221 k22 v22) => True
  | Node _ (V1 k11 v11) k1 v1 (V2 k121 v121 k12 v12), Empty => True
  | Empty, Node _ (V1 k21 v21) k2 v2 (V2 k221 v221 k22 v22) => True
  | Node _ (V2 k111 v111 k11 v11) k1 v1 (V1 k12 v12), Empty => True
  | Empty, Node _ (V2 k211 v211 k21 v21) k2 v2 (V1 k22 v22) => True
  | Node _ (V2 k111 v111 k11 v11) k1 v1 (V2 k121 v121 k12 v12), Empty => True
  | Empty, Node _ (V2 k211 v211 k21 v21) k2 v2 (V2 k221 v221 k22 v22) => True
  | Node _ (V3 k111 v111 k11 v11 k112 v112) k1 v1 (V2 k121 v121 k12 v12), Empty => True
  | Empty, Node _ (V2 k211 v211 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222) => True
  | Node _ (V3 k111 v111 k11 v11 k112 v112) k1 v1 (V1 k12 v12), Empty => True
  | Empty, Node _ (V1 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222) => True
  | Node _ (V1 k11 v11) k1 v1 (V3 k121 v121 k12 v12 k122 v122), Empty => True
  | Empty, Node _ (V3 k211 v211 k21 v21 k212 v212) k2 v2 (V1 k22 v22) => True
(*$*)
  | _, _ => False
  end.

Definition IsDeepCase
  {V:Type}
  (n1 : Tree V)
  (n2 : Tree V)
  : Prop
  :=
  match n1, n2 with
(*$
let () = Printf.printf "\n"
let () = List.iter fusion_cases ~f:(fun l ->
  Printf.printf "%s\n" (Line.to_rocq_boolean ~value:false l)
   )
*)
  | V1 _ _, V2 _ _ _ _ => False
  | V2 _ _ _ _, V1 _ _ => False
  | V1 _ _, V3 _ _ _ _ _ _ => False
  | V3 _ _ _ _ _ _, V1 _ _ => False
  | V2 _ _ _ _, V2 _ _ _ _ => False
  | V2 _ _ _ _, V3 _ _ _ _ _ _ => False
  | V3 _ _ _ _ _ _, V2 _ _ _ _ => False
  | V3 _ _ _ _ _ _, V3 _ _ _ _ _ _ => False
  | V2 k11 v11 k1 v1, Node _ (V2 k211 v211 k21 v21) k2 v2 (V1 k22 v22) => False
  | V2 k11 v11 k1 v1, Node _ (V1 k21 v21) k2 v2 (V2 k221 v221 k22 v22) => False
  | Node _ (V2 k111 v111 k11 v11) k1 v1 (V1 k12 v12), V2 k21 v21 k2 v2 => False
  | Node _ (V1 k11 v11) k1 v1 (V2 k121 v121 k12 v12), V2 k21 v21 k2 v2 => False
(*$*)
  | _, _ => not (IsShallowRotationCase n1 n2)
  end.

Definition SmallNodesWellFormed
  {V : Type}
  (T : Tree V)
  : Prop
  :=
  match T with
  | Empty => True
  | V1 _ _ => True
  | V2 _ _ _ _ => True
  | V3 _ _ _ _ _ _ => True
  | Node _ n1 _ _ n2 =>
      not (IsShallowRotationCase n1 n2)
  end.

Definition WellFormedStruct {V : Type} :=
  Eval simpl in (WellFormed (V:=V)) ++ [ SmallNodesWellFormed ].

Definition WellBalanced {V : Type} :=
  Eval simpl in (WellFormedStruct (V:=V)) ++ [ BalancedWeight ].


Lemma Node_NoEmptyL : forall { V: Type} {Ps : list PropF} {sl : SubList WellBalanced Ps} {n0 : nat} {k : K.t} {v : V} {n2 : Tree V},
  Property Ps (Node n0 Empty k v n2) -> False.
Proof.
  intros V Ps sl n0 k v n2 WB'.
  epose proof (Property_Sub WB') as WB. clear WB'.
  subst.
  epose proof (Property_This NodeWellFormed _ WB _) as NWF.
  unfold NodeWellFormed, NodeNodeWellFormed in NWF.
  epose proof (Property_This BalancedWeight _ WB _) as BW.
  unfold BalancedWeight, BalancedSize, omega2, delta2 in BW.
  simpl in *.
  destruct n2; simpl in *; try lia.
  inversion WB. subst.
  epose proof (WellFormed_NodeSize _ _ _ _ _ Hr) as [ns1 ns2].
  lia.
Qed.

Lemma Node_NoEmptyR : forall { V: Type} {Ps : list PropF} {sl : SubList WellBalanced Ps} {n0 : nat} {k : K.t} {v : V} {n1 : Tree V},
  Property Ps (Node n0 n1 k v Empty) -> False.
Proof.
  intros V Ps sl n0 k v n1 WB'.
  epose proof (Property_Sub WB') as WB. clear WB'.
  subst.
  epose proof (Property_This NodeWellFormed _ WB _) as NWF.
  unfold NodeWellFormed, NodeNodeWellFormed in NWF.
  epose proof (Property_This BalancedWeight _ WB _) as BW.
  unfold BalancedWeight, BalancedSize, omega2, delta2 in BW.
  simpl in *.
  destruct n1; simpl in *; try lia.
  inversion WB. subst.
  epose proof (WellFormed_NodeSize _ _ _ _ _ Hl) as [ns1 ns2].
  lia.
Qed.

Definition single_rotation_left_node
  {V : Type}
  (n1w : nat) (n2w : nat)
  (n11 : Tree V) (n1k : K.t) (n1v : V) (n12 : Tree V)
  (n0k : K.t) (n0v : V) (n2 : Tree V)
  : Tree V
  :=
  Node (n1w + n2w) n11 n1k n1v (Node (weight n12 + n2w) n12 n0k n0v n2).

Lemma single_rotation_left_node_WeightConsistent : forall {V : Type} (n1w : nat) (n2w : nat)
  (n11 : Tree V) (n1k : K.t) (n1v : V) (n12 : Tree V)
  (n0k : K.t) (n0v : V) (n2 : Tree V),
  (n1w = weight n11 + weight n12) ->
  (n2w = weight n2) ->
  (Property [ WeightConsistent ] n11) ->
  (Property [ WeightConsistent ] n12) ->
  (Property [ WeightConsistent ] n2)  ->
  Property [ WeightConsistent ] (single_rotation_left_node n1w n2w n11 n1k n1v n12 n0k n0v n2).
Proof.
  intros. unfold single_rotation_left_node.
  epose proof (Property_This WeightConsistent _ H1 _) as TH1.
  epose proof (Property_This WeightConsistent _ H2 _) as TH2.
  epose proof (Property_This WeightConsistent _ H3 _) as TH3.
  repeat constructor; auto; unfold WeightConsistent; unfold WeightConsistent in TH1,TH2,TH3; simpl; lia.
Qed.

Ltac destruct_matches_n n :=
  match n with
  | O => idtac
  | S ?n' =>
    try (match goal with
         | |- context [match ?x with _ => _ end] =>
             is_var x; let T := type of x in unify T nat; destruct x; try auto
         end;
         destruct_matches_n n')
  end.

Ltac destruct_matches_n_h n :=
  match n with
  | O => idtac
  | S ?n' =>
    try (match goal with
         | [ H : context [match ?x with _ => _ end] |- _] =>
             is_var x; let T := type of x in unify T nat; destruct x; try auto; try lia
         end;
         destruct_matches_n_h n')
  end.

Ltac analyze_node_cases :=
  try match goal with
  | [ H : needsRotation ?n1w ?n2w |- _] => unfold needsRotation in H
  end;
  try match goal with
  | [ H : ValidInputImbalance ?n1w ?n2w |- _] => unfold ValidInputImbalance in H
  end;
  unfold omega2 in *;
  unfold delta2 in *;
  repeat multimatch goal with
  | [ H : Property WellBalanced (Node ?n1w ?n11 ?n1k ?n1v ?n12) |- _] =>
      match n11 with
      | Empty => now epose proof (Node_NoEmptyL H)
      | _ => idtac
      end;
      match n12 with
      | Empty => now epose proof (Node_NoEmptyR H)
      | _ => idtac
      end;
      match goal with
      | [ _ : Property WellBalanced n11, _ : Property WellBalanced n12 |- _] =>
          fail 1
      | [ |- _] =>
          let ns1 := fresh H "nsLow" in
          let ns2 := fresh H "nsSum" in
          let BW := fresh H "bw" in
          let NWF := fresh H "nwf" in
          let SNWF := fresh H "snwf" in
          let WC := fresh H "wc" in
          inversion H;
          epose proof (WellFormed_NodeSize _ _ _ _ _ H) as [ns1 ns2];
          epose proof (Property_This BalancedWeight _ H _) as BW;
          unfold BalancedWeight, BalancedSize, omega2 in BW;
          epose proof (Property_This NodeWellFormed _ H _) as NWF;
          epose proof (Property_This SmallNodesWellFormed _ H _) as SNWF;
          epose proof (Property_This WeightConsistent _ H _) as WC;
          try (simpl in *; lia);
          idtac
      end
  end;
  try match goal with
      | [ H : Property ?L ?T |- Property [ ?p ] ?T ] =>
          try (epose proof (Property_In p H _); try easy)
      end;
      (*
  try match goal with
      | [ H : Property WellBalanced (Node ?n1w ?n11 ?n1k ?n1v ?n12)
      |- BalancedSize (weight ?n1) (weight ?n2) ] =>
      end;
       *)
  unfold omega2 in *;
  unfold delta2 in *;
  try auto;
  try contradiction;
  try lia;
  idtac.

Ltac destruct_node_cases n :=
  match n with
  | O => idtac
  | S ?n' =>
    try (match goal with
         | |- context [match ?x with _ => _ end] =>
           is_var x;
           match type of x with
           | Tree _ => destruct x; analyze_node_cases
           end
         end;
         destruct_node_cases n')
  end.

Ltac destruct_node_cases_h n :=
  match n with
  | O => idtac
  | S ?n' =>
    try (match goal with
         | [ H : context [match ?x with _ => _ end] |- _] =>
           is_var x;
           match type of x with
           | Tree _ => destruct x; analyze_node_cases
           end
         end;
         destruct_node_cases_h n')
  end.

Lemma single_rotation_left_node_SmallNodes : forall {V : Type} (n1w : nat) (n2w : nat)
  (n11 : Tree V) (n1k : K.t) (n1v : V) (n12 : Tree V)
  (n0k : K.t) (n0v : V) (n2 : Tree V),
  (n1w = weight n11 + weight n12) ->
  (n2w = weight n2) ->
  (Property WellBalanced (Node n1w n11 n1k n1v n12)) ->
  (Property WellBalanced n2) ->
  (IsDeepCase (Node n1w n11 n1k n1v n12) n2) ->
  (needsRotation n1w n2w) ->
  (ValidInputImbalance n1w n2w) ->
  Property [ SmallNodesWellFormed ] (single_rotation_left_node n1w n2w n11 n1k n1v n12 n0k n0v n2).
Proof.
  intros V n1w n2w n11 n1k n1v n12 n0k n0v n2 n1weq n2weq WFS WFSn2 DeepCase NR VI.
  unfold single_rotation_left_node.
  unfold WellFormedStruct in *.
  unfold IsDeepCase in *; unfold IsShallowRotationCase in *.
  unfold needsRotation in *. unfold omega2 in *.
  unfold ValidInputImbalance in *.
  repeat constructor.
  all: analyze_node_cases.
  all: unfold SmallNodesWellFormed, IsShallowRotationCase.
  - destruct_node_cases 5; destruct_matches_n 10.
    simpl in *. subst. simpl in *. lia.
  - destruct_node_cases 6; destruct_matches_n 10;
    destruct_node_cases_h 6.
    all: simpl in *; try lia.
    destruct_node_cases_h 2.
    all: simpl in *; try lia.
    all: subst; simpl in *; try lia.
Qed.

Lemma single_rotation_left_node_NodeWellFormed : forall {V : Type} (n1w : nat) (n2w : nat)
  (n11 : Tree V) (n1k : K.t) (n1v : V) (n12 : Tree V)
  (n0k : K.t) (n0v : V) (n2 : Tree V),
  (n1w = weight n11 + weight n12) ->
  (n2w = weight n2) ->
  (Property WellBalanced (Node n1w n11 n1k n1v n12)) ->
  (Property WellBalanced n2) ->
  (IsDeepCase (Node n1w n11 n1k n1v n12) n2) ->
  (needsRotation n1w n2w) ->
  (ValidInputImbalance n1w n2w) ->
  Property [ NodeWellFormed ] (single_rotation_left_node n1w n2w n11 n1k n1v n12 n0k n0v n2).
Proof.
  intros V n1w n2w n11 n1k n1v n12 n0k n0v n2 n1weq n2weq WFS WFSn2 DeepCase NR VI.
  unfold single_rotation_left_node.

  repeat constructor.
  all: analyze_node_cases.
  
  all: subst.
  - simpl. destruct n11; simpl in *; destruct n12; simpl in *; try lia; destruct n2; simpl in *; try lia.
  - simpl. destruct n12; simpl in *; destruct n2, n11; simpl in *; try lia.
    all: analyze_node_cases.
    simpl in *; destruct n; try lia; destruct n; try lia; destruct n; try lia.
    simpl in *. destruct n; try lia; destruct n; try lia; destruct n; try lia.
Qed.

Lemma single_rotation_left_node_BalancedWeight : forall {V : Type} (n1w : nat) (n2w : nat)
  (n11 : Tree V) (n1k : K.t) (n1v : V) (n12 : Tree V)
  (n0k : K.t) (n0v : V) (n2 : Tree V),
  (n1w = weight n11 + weight n12) ->
  (n2w = weight n2) ->
  (Property WellBalanced (Node n1w n11 n1k n1v n12)) ->
  (Property WellBalanced n2) ->
  (IsDeepCase (Node n1w n11 n1k n1v n12) n2) ->
  (needsRotation n1w n2w) ->
  (ValidInputImbalance n1w n2w) ->
  (needsSingleRotationAnalyzeLeft (weight n11) n12 (weight n2)) ->
  Property [ BalancedWeight ] (single_rotation_left_node n1w n2w n11 n1k n1v n12 n0k n0v n2).
Proof.
  intros V n1w n2w n11 n1k n1v n12 n0k n0v n2 n1weq n2weq WFS WFSn2 DeepCase NR VI LS.
  unfold single_rotation_left_node.
  unfold needsSingleRotationAnalyzeLeft, needsSingleRotation2, alpha2 in LS.
  repeat constructor.
  all: analyze_node_cases.
  all: simpl in *.
  all: destruct_node_cases_h 3.
  all: simpl in *; try lia.
Qed.


Lemma single_rotation_left_node_WellBalanced : forall {V : Type} (n1w : nat) (n2w : nat)
  (n11 : Tree V) (n1k : K.t) (n1v : V) (n12 : Tree V)
  (n0k : K.t) (n0v : V) (n2 : Tree V),
  (n1w = weight n11 + weight n12) ->
  (n2w = weight n2) ->
  (Property WellBalanced (Node n1w n11 n1k n1v n12)) ->
  (Property WellBalanced n2) ->
  (IsDeepCase (Node n1w n11 n1k n1v n12) n2) ->
  (needsRotation n1w n2w) ->
  (ValidInputImbalance n1w n2w) ->
  (needsSingleRotationAnalyzeLeft (weight n11) n12 (weight n2)) ->
  Property WellBalanced (single_rotation_left_node n1w n2w n11 n1k n1v n12 n0k n0v n2).
Proof.
  intros V n1w n2w n11 n1k n1v n12 n0k n0v n2 n1weq n2weq WFS WFSn2 DeepCase NR VI LS.
  epose proof (single_rotation_left_node_BalancedWeight n1w n2w n11 n1k n1v n12 n0k n0v n2 n1weq n2weq WFS WFSn2 DeepCase NR VI LS).
  epose proof (single_rotation_left_node_NodeWellFormed n1w n2w n11 n1k n1v n12 n0k n0v n2 n1weq n2weq WFS WFSn2 DeepCase NR VI).
  epose proof (single_rotation_left_node_SmallNodes n1w n2w n11 n1k n1v n12 n0k n0v n2 n1weq n2weq WFS WFSn2 DeepCase NR VI).
  epose proof (single_rotation_left_node_WeightConsistent n1w n2w n11 n1k n1v n12 n0k n0v n2 n1weq n2weq _ _ _).
  unfold WellBalanced.
  property_decompose. intuition.
  Unshelve.
  all: analyze_node_cases.
Qed.
  
Definition single_rotation_right_node
  {V : Type}
  (n1w : nat) (n2w : nat)
  (n1 : Tree V)
  (n0k : K.t) (n0v : V)
  (n21 : Tree V) (n2k : K.t) (n2v : V) (n22 : Tree V)
  : Tree V
  :=
  Node (n1w + n2w) (Node (n1w + weight n21) n1 n0k n0v n21) n2k n2v n22.

Lemma single_rotation_right_node_WeightConsistent : forall {V : Type} (n1w : nat) (n2w : nat)
  (n1 : Tree V)
  (n0k : K.t) (n0v : V)
  (n21 : Tree V) (n2k : K.t) (n2v : V) (n22 : Tree V),
  (n1w = weight n1) ->
  (n2w = weight n21 + weight n22) ->
  (Property [ WeightConsistent ] n1) ->
  (Property [ WeightConsistent ] n21) ->
  (Property [ WeightConsistent ] n22) ->
  Property [ WeightConsistent ] (single_rotation_right_node n1w n2w n1 n0k n0v n21 n2k n2v n22).
Proof.
  intros.
  intros. unfold single_rotation_right_node.
  epose proof (Property_This WeightConsistent _ H1 _) as TH1.
  epose proof (Property_This WeightConsistent _ H2 _) as TH2.
  epose proof (Property_This WeightConsistent _ H3 _) as TH3.
  repeat constructor; unfold WeightConsistent in *; simpl in *; auto; lia.
Qed.

Lemma single_rotation_right_node_NodeWellFormed : forall {V : Type} (n1w : nat) (n2w : nat)
  (n1 : Tree V)
  (n0k : K.t) (n0v : V)
  (n21 : Tree V) (n2k : K.t) (n2v : V) (n22 : Tree V),
  (n1w = weight n1) ->
  (n2w = weight n21 + weight n22) ->
  (Property WellBalanced n1) ->
  (Property WellBalanced (Node n2w n21 n2k n2v n22)) ->
  (IsDeepCase n1 (Node n2w n21 n2k n2v n22)) ->
  (needsRotation n2w n1w) ->
  (ValidInputImbalance n1w n2w) ->
  Property [ NodeWellFormed ] (single_rotation_right_node n1w n2w n1 n0k n0v n21 n2k n2v n22).
Proof.
  intros V n1w n2w n1 n0k n0v n21 n2k n2v n22 n1weq n2weq WFn1 WFn2 DeepCase NR VI.
  unfold single_rotation_right_node.
  repeat constructor.
  all: analyze_node_cases.
  simpl in *.
  all: destruct_node_cases_h 3.
  all: simpl in *; try lia.
  all: destruct_node_cases 3.
  all: simpl in *; try lia.
  all: destruct_node_cases_h 3.
  all: simpl in *; try lia.
  all: destruct_matches_n_h 10.
  all: simpl in *; try lia.
Qed.

Lemma single_rotation_right_node_BalancedWeight : forall {V : Type} (n1w : nat) (n2w : nat)
  (n1 : Tree V)
  (n0k : K.t) (n0v : V)
  (n21 : Tree V) (n2k : K.t) (n2v : V) (n22 : Tree V),
  (n1w = weight n1) ->
  (n2w = weight n21 + weight n22) ->
  (Property WellBalanced n1) ->
  (Property WellBalanced (Node n2w n21 n2k n2v n22)) ->
  (IsDeepCase n1 (Node n2w n21 n2k n2v n22)) ->
  (needsRotation n2w n1w) ->
  (ValidInputImbalance n1w n2w) ->
  (needsSingleRotationAnalyzeRight (weight n1) n21 (weight n22)) ->
  Property [ BalancedWeight ] (single_rotation_right_node n1w n2w n1 n0k n0v n21 n2k n2v n22).
Proof.
  intros V n1w n2w n1 n0k n0v n21 n2k n2v n22 n1weq n2weq WFn1 WFn2 DeepCase NR VI RS.
  unfold single_rotation_right_node.
  unfold needsSingleRotationAnalyzeRight, needsSingleRotation2, alpha2 in RS.
  unfold IsDeepCase, IsShallowRotationCase in *.
  repeat constructor.
  all: analyze_node_cases.
  all: simpl in *.
  all: destruct_node_cases_h 3.
  all: simpl in *; try lia.
Qed.

Lemma single_rotation_right_node_SmallNodes : forall {V : Type} (n1w : nat) (n2w : nat)
  (n1 : Tree V)
  (n0k : K.t) (n0v : V)
  (n21 : Tree V) (n2k : K.t) (n2v : V) (n22 : Tree V),
  (n1w = weight n1) ->
  (n2w = weight n21 + weight n22) ->
  (Property WellBalanced n1) ->
  (Property WellBalanced (Node n2w n21 n2k n2v n22)) ->
  (IsDeepCase n1 (Node n2w n21 n2k n2v n22)) ->
  (needsRotation n2w n1w) ->
  (ValidInputImbalance n1w n2w) ->
  (needsSingleRotationAnalyzeRight (weight n1) n21 (weight n22)) ->
  Property [ SmallNodesWellFormed ] (single_rotation_right_node n1w n2w n1 n0k n0v n21 n2k n2v n22).
Proof.
  intros V n1w n2w n1 n0k n0v n21 n2k n2v n22 n1weq n2weq WFn1 WFn2 DeepCase NR VI RS.
  unfold single_rotation_right_node.
  unfold needsSingleRotationAnalyzeRight, needsSingleRotation2, alpha2 in RS.
  unfold IsDeepCase, IsShallowRotationCase in *.
  repeat constructor.
  all: analyze_node_cases.
  all: simpl in *.
  all: unfold IsShallowRotationCase in *.
  all: destruct_node_cases_h 2; simpl in *; try lia.
  all: destruct n1; analyze_node_cases; simpl in *; try lia.
  all: destruct_matches_n 10.
  all: destruct_node_cases_h 2; simpl in *; try lia.
  all: destruct_node_cases 6; destruct_matches_n 10.
  all: simpl in *; try lia.
  all: destruct_matches_n_h 10.
Qed.

Lemma single_rotation_right_node_WellBalanced : forall {V : Type} (n1w : nat) (n2w : nat)
  (n1 : Tree V)
  (n0k : K.t) (n0v : V)
  (n21 : Tree V) (n2k : K.t) (n2v : V) (n22 : Tree V),
  (n1w = weight n1) ->
  (n2w = weight n21 + weight n22) ->
  (Property WellBalanced n1) ->
  (Property WellBalanced (Node n2w n21 n2k n2v n22)) ->
  (IsDeepCase n1 (Node n2w n21 n2k n2v n22)) ->
  (needsRotation n2w n1w) ->
  (ValidInputImbalance n1w n2w) ->
  (needsSingleRotationAnalyzeRight (weight n1) n21 (weight n22)) ->
  Property WellBalanced (single_rotation_right_node n1w n2w n1 n0k n0v n21 n2k n2v n22).
Proof.
  intros V n1w n2w n1 n0k n0v n21 n2k n2v n22 n1weq n2weq WFn1 WFn2 DeepCase NR VI RS.
  epose proof (single_rotation_right_node_BalancedWeight n1w n2w n1 n0k n0v n21 n2k n2v n22 n1weq n2weq WFn1 WFn2 DeepCase NR VI RS).
  epose proof (single_rotation_right_node_NodeWellFormed n1w n2w n1 n0k n0v n21 n2k n2v n22 n1weq n2weq WFn1 WFn2 DeepCase NR VI).
  epose proof (single_rotation_right_node_SmallNodes n1w n2w n1 n0k n0v n21 n2k n2v n22 n1weq n2weq WFn1 WFn2 DeepCase NR VI RS).
  epose proof (single_rotation_right_node_WeightConsistent n1w n2w n1 n0k n0v n21 n2k n2v n22 n1weq n2weq _ _ _).
  unfold WellBalanced.
  property_decompose. intuition.
  Unshelve.
  all: analyze_node_cases.
Qed.

Definition double_rotation_left_node
  {V : Type}
  (n1w : nat) (n12w : nat) (n2w : nat)
  (n11 : Tree V) (n1k : K.t) (n1v : V)
  (n12k : K.t) (n12v : V)
  (n121 : Tree V) (n122 : Tree V)
  (n0k : K.t) (n0v : V)
  (n2 : Tree V)
  : Tree V
  :=
  Node (n1w + n2w)
    (Node (weight n11 + weight n121) n11 n1k n1v n121)
    n12k n12v
    (Node (n2w + weight n122) n122 n0k n0v n2).

Lemma double_rotation_left_node_WeightConsistent : forall {V : Type} (n1w : nat) (n12w : nat) (n2w : nat)
  (n11 : Tree V) (n1k : K.t) (n1v : V)
  (n12k : K.t) (n12v : V)
  (n121 : Tree V) (n122 : Tree V)
  (n0k : K.t) (n0v : V)
  (n2 : Tree V),
  (n1w = weight n11 + weight n121 + weight n122) ->
  (n2w = weight n2) ->
  (Property [ WeightConsistent ] n11) ->
  (Property [ WeightConsistent ] n121) ->
  (Property [ WeightConsistent ] n122) ->
  (Property [ WeightConsistent ] n2) ->
  Property [ WeightConsistent ] (double_rotation_left_node n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 n0k n0v n2).
Proof.
  intros. unfold double_rotation_left_node.
  epose proof (Property_This WeightConsistent _ H1 _) as TH1.
  epose proof (Property_This WeightConsistent _ H2 _) as TH2.
  epose proof (Property_This WeightConsistent _ H3 _) as TH3.
  epose proof (Property_This WeightConsistent _ H4 _) as TH4.
  repeat constructor; auto; unfold WeightConsistent in *; simpl in *; try lia.
Qed.

Lemma double_rotation_left_node_NodeWellFormed : forall {V : Type} (n1w : nat) (n12w : nat) (n2w : nat)
  (n11 : Tree V) (n1k : K.t) (n1v : V)
  (n12k : K.t) (n12v : V)
  (n121 : Tree V) (n122 : Tree V)
  (n0k : K.t) (n0v : V)
  (n2 : Tree V),
  (n1w = weight n11 + weight n121 + weight n122) ->
  (n2w = weight n2) ->
  (n12w = weight n121 + weight n122) ->
  (Property WellBalanced (Node n1w n11 n1k n1v (Node n12w n121 n12k n12v n122))) ->
  (Property WellBalanced n2) ->
  (IsDeepCase (Node n1w n11 n1k n1v (Node n12w n121 n12k n12v n122)) n2) ->
  (needsRotation n1w n2w) ->
  (ValidInputImbalance n1w n2w) ->
  (not (needsSingleRotation2 (weight n11) (weight n121) (weight n122) (weight n2))) ->
  Property [ NodeWellFormed ] (double_rotation_left_node n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 n0k n0v n2).
Proof.
  intros V n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 n0k n0v n2 n1weq n2weq n12weq WFn1 WFn2 DeepCase NR VI LS.
  remember (double_rotation_left_node n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 n0k
     n0v n2) as DR.
  rewrite HeqDR.
  unfold double_rotation_left_node.
  unfold needsSingleRotation2 in *.
  repeat constructor.
  all: analyze_node_cases.
  all: simpl in *.
  all: destruct n11; simpl in *; analyze_node_cases.
  all: destruct n121; simpl in *; analyze_node_cases.
  all: destruct n122; simpl in *; analyze_node_cases.
  all: destruct n2; simpl in *; analyze_node_cases.
Qed.

Lemma double_rotation_left_node_SmallNodes : forall {V : Type} (n1w : nat) (n12w : nat) (n2w : nat)
  (n11 : Tree V) (n1k : K.t) (n1v : V)
  (n12k : K.t) (n12v : V)
  (n121 : Tree V) (n122 : Tree V)
  (n0k : K.t) (n0v : V)
  (n2 : Tree V),
  (n1w = weight n11 + weight n121 + weight n122) ->
  (n2w = weight n2) ->
  (n12w = weight n121 + weight n122) ->
  (Property WellBalanced (Node n1w n11 n1k n1v (Node n12w n121 n12k n12v n122))) ->
  (Property WellBalanced n2) ->
  (IsDeepCase (Node n1w n11 n1k n1v (Node n12w n121 n12k n12v n122)) n2) ->
  (needsRotation n1w n2w) ->
  (ValidInputImbalance n1w n2w) ->
  (not (needsSingleRotation2 (weight n11) (weight n121) (weight n122) (weight n2))) ->
  Property [ SmallNodesWellFormed ] (double_rotation_left_node n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 n0k n0v n2).
Proof.
  intros V n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 n0k n0v n2 n1weq n2weq n12weq WFn1 WFn2 DeepCase NR VI LS.
  remember (double_rotation_left_node n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 n0k
     n0v n2) as DR.
  rewrite HeqDR.
  unfold double_rotation_left_node.
  unfold needsSingleRotation2 in *.
  repeat constructor.
  all: analyze_node_cases.
  all: simpl in *.
  all: unfold IsShallowRotationCase in *.
  all: destruct_node_cases 6; destruct_matches_n 10.
  all: simpl in *; try lia.
  all: destruct_node_cases_h 6.
  all: simpl in *; try lia.
Qed.

Lemma double_rotation_left_node_BalancedWeight : forall {V : Type} (n1w : nat) (n12w : nat) (n2w : nat)
  (n11 : Tree V) (n1k : K.t) (n1v : V)
  (n12k : K.t) (n12v : V)
  (n121 : Tree V) (n122 : Tree V)
  (n0k : K.t) (n0v : V)
  (n2 : Tree V),
  (n1w = weight n11 + weight n121 + weight n122) ->
  (n2w = weight n2) ->
  (n12w = weight n121 + weight n122) ->
  (Property WellBalanced (Node n1w n11 n1k n1v (Node n12w n121 n12k n12v n122))) ->
  (Property WellBalanced n2) ->
  (IsDeepCase (Node n1w n11 n1k n1v (Node n12w n121 n12k n12v n122)) n2) ->
  (needsRotation n1w n2w) ->
  (ValidInputImbalance n1w n2w) ->
  (not (needsSingleRotation2 (weight n11) (weight n121) (weight n122) (weight n2))) ->
  Property [ BalancedWeight ] (double_rotation_left_node n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 n0k n0v n2).
Proof.
  intros V n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 n0k n0v n2 n1weq n2weq n12weq WFn1 WFn2 DeepCase NR VI LS.
  remember (double_rotation_left_node n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 n0k
     n0v n2) as DR.
  rewrite HeqDR.
  unfold double_rotation_left_node.
  unfold needsSingleRotation2 in *.
  repeat constructor.
  all: analyze_node_cases.
  all: simpl in *.
  all: unfold IsShallowRotationCase in *.
  all: destruct_node_cases 6; destruct_matches_n 10.
  all: simpl in *; try lia.
  all: destruct_node_cases_h 6.
  all: simpl in *; try lia.
Qed.

Lemma double_rotation_left_node_WellBalanced : forall {V : Type} (n1w : nat) (n12w : nat) (n2w : nat)
  (n11 : Tree V) (n1k : K.t) (n1v : V)
  (n12k : K.t) (n12v : V)
  (n121 : Tree V) (n122 : Tree V)
  (n0k : K.t) (n0v : V)
  (n2 : Tree V),
  (n1w = weight n11 + weight n121 + weight n122) ->
  (n2w = weight n2) ->
  (n12w = weight n121 + weight n122) ->
  (Property WellBalanced (Node n1w n11 n1k n1v (Node n12w n121 n12k n12v n122))) ->
  (Property WellBalanced n2) ->
  (IsDeepCase (Node n1w n11 n1k n1v (Node n12w n121 n12k n12v n122)) n2) ->
  (needsRotation n1w n2w) ->
  (ValidInputImbalance n1w n2w) ->
  (not (needsSingleRotation2 (weight n11) (weight n121) (weight n122) (weight n2))) ->
  Property WellBalanced (double_rotation_left_node n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 n0k n0v n2).
Proof.
  intros V n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 n0k n0v n2 n1weq n2weq n12weq WFn1 WFn2 DeepCase NR VI LS.
  epose proof (double_rotation_left_node_BalancedWeight n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 n0k n0v n2 n1weq n2weq n12weq WFn1 WFn2 DeepCase NR VI LS).
  epose proof (double_rotation_left_node_NodeWellFormed n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 n0k n0v n2 n1weq n2weq n12weq WFn1 WFn2 DeepCase NR VI LS).
  epose proof (double_rotation_left_node_SmallNodes n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 n0k n0v n2 n1weq n2weq n12weq WFn1 WFn2 DeepCase NR VI LS).
  epose proof (double_rotation_left_node_WeightConsistent n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 n0k n0v n2 n1weq n2weq _  _ _ _). 
  unfold WellBalanced.
  property_decompose. intuition.
  Unshelve.
  all: analyze_node_cases.
Qed.

Definition double_rotation_right_node
  {V : Type}
  (n1w : nat) (n21w : nat) (n2w : nat)
  (n1 : Tree V)
  (n0k : K.t) (n0v : V)
  (n21k : K.t) (n21v : V)
  (n211 : Tree V)
  (n212 : Tree V) 
  (n2k : K.t) (n2v : V)
  (n22 : Tree V)
  :=
  Node (n1w + n2w)
    (Node (n1w + weight n211) n1 n0k n0v n211)
    n21k n21v
    (Node (weight n22 + weight n212) n212 n2k n2v n22).

Lemma double_rotation_right_node_WeightConsistent : forall {V : Type} (n1w : nat) (n21w : nat) (n2w : nat)
  (n1 : Tree V)
  (n0k : K.t) (n0v : V)
  (n21k : K.t) (n21v : V)
  (n211 : Tree V)
  (n212 : Tree V) 
  (n2k : K.t) (n2v : V)
  (n22 : Tree V),
  (n1w = weight n1) ->
  (n2w = weight n22 + weight n212 + weight n211) ->
  (Property [ WeightConsistent ] n1) ->
  (Property [ WeightConsistent ] n211) ->
  (Property [ WeightConsistent ] n212) ->
  (Property [ WeightConsistent ] n22) ->
  Property [ WeightConsistent ] (double_rotation_right_node n1w n21w n2w n1 n0k n0v n21k n21v n211 n212 n2k n2v n22).
Proof.
  intros. unfold double_rotation_right_node.
  epose proof (Property_This WeightConsistent _ H1 _) as TH1.
  epose proof (Property_This WeightConsistent _ H2 _) as TH2.
  epose proof (Property_This WeightConsistent _ H3 _) as TH3.
  epose proof (Property_This WeightConsistent _ H4 _) as TH4.
  repeat constructor; auto; unfold WeightConsistent in *; simpl in *; try lia.
Qed.

Lemma double_rotation_right_node_NodeWellFormed : forall {V : Type} (n1w : nat) (n21w : nat) (n2w : nat)
  (n1 : Tree V)
  (n0k : K.t) (n0v : V)
  (n21k : K.t) (n21v : V)
  (n211 : Tree V)
  (n212 : Tree V) 
  (n2k : K.t) (n2v : V)
  (n22 : Tree V),
  (n1w = weight n1) ->
  (n2w = weight n22 + weight n212 + weight n211) ->
  (n21w = weight n211 + weight n212) ->
  (Property WellBalanced n1) ->
  (Property WellBalanced (Node n2w (Node n21w n211 n21k n21v n212) n2k n2v n22)) ->
  (IsDeepCase n1 (Node n2w (Node n21w n211 n21k n21v n212) n2k n2v n22)) ->
  (needsRotation n2w n1w) ->
  (ValidInputImbalance n1w n2w) ->
  (not (needsSingleRotation2 (weight n22) (weight n212) (weight n211) (weight n1))) ->
  Property [ NodeWellFormed ] (double_rotation_right_node n1w n21w n2w n1 n0k n0v n21k n21v n211 n212 n2k n2v n22).
Proof.
  intros V n1w n21w n2w n1 n0k n0v n21k n21v n211 n212 n2k n2v n22 n1weq n2weq n21weq WFn1 WFn2 DeepCase NR VI RS.
  unfold needsRotation, ValidInputImbalance, needsSingleRotation2, IsDeepCase, BalancedSize, IsShallowRotationCase, omega2, delta2 in *.
  unfold double_rotation_right_node.
  repeat constructor.
  all: analyze_node_cases.
  all: simpl in *.
  all: destruct_node_cases 6; simpl in *; try lia.
  all: destruct_node_cases_h 6; simpl in *; try lia.
Qed.

Lemma double_rotation_right_node_SmallNodes : forall {V : Type} (n1w : nat) (n21w : nat) (n2w : nat)
  (n1 : Tree V)
  (n0k : K.t) (n0v : V)
  (n21k : K.t) (n21v : V)
  (n211 : Tree V)
  (n212 : Tree V) 
  (n2k : K.t) (n2v : V)
  (n22 : Tree V),
  (n1w = weight n1) ->
  (n2w = weight n22 + weight n212 + weight n211) ->
  (n21w = weight n211 + weight n212) ->
  (Property WellBalanced n1) ->
  (Property WellBalanced (Node n2w (Node n21w n211 n21k n21v n212) n2k n2v n22)) ->
  (IsDeepCase n1 (Node n2w (Node n21w n211 n21k n21v n212) n2k n2v n22)) ->
  (needsRotation n2w n1w) ->
  (ValidInputImbalance n1w n2w) ->
  (not (needsSingleRotation2 (weight n22) (weight n212) (weight n211) (weight n1))) ->
  Property [ SmallNodesWellFormed ] (double_rotation_right_node n1w n21w n2w n1 n0k n0v n21k n21v n211 n212 n2k n2v n22).
Proof.
  intros V n1w n21w n2w n1 n0k n0v n21k n21v n211 n212 n2k n2v n22 n1weq n2weq n21weq WFn1 WFn2 DeepCase NR VI RS.
  unfold needsRotation, ValidInputImbalance, needsSingleRotation2, IsDeepCase, BalancedSize, IsShallowRotationCase, omega2, delta2 in *.
  unfold double_rotation_right_node.
  repeat constructor.
  all: analyze_node_cases.
  all: simpl in *.
  all: unfold IsShallowRotationCase in *.
  all: destruct_node_cases 6; simpl in *; try lia.
  all: destruct_matches_n 10.
  all: destruct_node_cases_h 3; simpl in *; try lia.
Qed.

Lemma double_rotation_right_node_BalancedWeight : forall {V : Type} (n1w : nat) (n21w : nat) (n2w : nat)
  (n1 : Tree V)
  (n0k : K.t) (n0v : V)
  (n21k : K.t) (n21v : V)
  (n211 : Tree V)
  (n212 : Tree V) 
  (n2k : K.t) (n2v : V)
  (n22 : Tree V),
  (n1w = weight n1) ->
  (n2w = weight n22 + weight n212 + weight n211) ->
  (n21w = weight n211 + weight n212) ->
  (Property WellBalanced n1) ->
  (Property WellBalanced (Node n2w (Node n21w n211 n21k n21v n212) n2k n2v n22)) ->
  (IsDeepCase n1 (Node n2w (Node n21w n211 n21k n21v n212) n2k n2v n22)) ->
  (needsRotation n2w n1w) ->
  (ValidInputImbalance n1w n2w) ->
  (not (needsSingleRotation2 (weight n22) (weight n212) (weight n211) (weight n1))) ->
  Property [ BalancedWeight ] (double_rotation_right_node n1w n21w n2w n1 n0k n0v n21k n21v n211 n212 n2k n2v n22).
Proof.
  intros V n1w n21w n2w n1 n0k n0v n21k n21v n211 n212 n2k n2v n22 n1weq n2weq n21weq WFn1 WFn2 DeepCase NR VI RS.
  unfold needsRotation, ValidInputImbalance, needsSingleRotation2, IsDeepCase, BalancedSize, IsShallowRotationCase, omega2, delta2 in *.
  unfold double_rotation_right_node.
  repeat constructor.
  all: analyze_node_cases.
Qed.

Lemma double_rotation_right_node_WellBalanced : forall {V : Type} (n1w : nat) (n21w : nat) (n2w : nat)
  (n1 : Tree V)
  (n0k : K.t) (n0v : V)
  (n21k : K.t) (n21v : V)
  (n211 : Tree V)
  (n212 : Tree V) 
  (n2k : K.t) (n2v : V)
  (n22 : Tree V),
  (n1w = weight n1) ->
  (n2w = weight n22 + weight n212 + weight n211) ->
  (n21w = weight n211 + weight n212) ->
  (Property WellBalanced n1) ->
  (Property WellBalanced (Node n2w (Node n21w n211 n21k n21v n212) n2k n2v n22)) ->
  (IsDeepCase n1 (Node n2w (Node n21w n211 n21k n21v n212) n2k n2v n22)) ->
  (needsRotation n2w n1w) ->
  (ValidInputImbalance n1w n2w) ->
  (not (needsSingleRotation2 (weight n22) (weight n212) (weight n211) (weight n1))) ->
  Property WellBalanced (double_rotation_right_node n1w n21w n2w n1 n0k n0v n21k n21v n211 n212 n2k n2v n22).
Proof.
  intros V n1w n21w n2w n1 n0k n0v n21k n21v n211 n212 n2k n2v n22 n1weq n2weq n21weq WFn1 WFn2 DeepCase NR VI RS.
  epose proof (double_rotation_right_node_BalancedWeight n1w n21w n2w n1 n0k n0v n21k n21v n211 n212 n2k n2v n22 n1weq n2weq n21weq WFn1 WFn2 DeepCase NR VI RS).
  epose proof (double_rotation_right_node_NodeWellFormed n1w n21w n2w n1 n0k n0v n21k n21v n211 n212 n2k n2v n22 n1weq n2weq n21weq WFn1 WFn2 DeepCase NR VI RS).
  epose proof (double_rotation_right_node_SmallNodes n1w n21w n2w n1 n0k n0v n21k n21v n211 n212 n2k n2v n22 n1weq n2weq n21weq WFn1 WFn2 DeepCase NR VI RS).
  epose proof (double_rotation_right_node_WeightConsistent n1w n21w n2w n1 n0k n0v n21k n21v n211 n212 n2k n2v n22 n1weq n2weq _ _ _ _).
  unfold WellBalanced.
  property_decompose. intuition.
  Unshelve.
  all: analyze_node_cases.
Qed.



Ltac wfns V WFn :=
  epose proof (WellFormed_NodeSize (V := V) _ _ _ _ _ WFn) as [WFNSA WFNSB];
  repeat progress match goal with
  | [ H : context [ needsRotation _ _ ] |- _ ] => unfold needsRotation in H; unfold omega2 in H
  | _ => idtac
  end;
  try
  first [ lia | (cbn [weight] in *; lia) | (simpl in *; lia)].

Notation "x 'eq:' p" := (exist _ x p) (only parsing, at level 20).

Definition inspect {A : Type} (a : A) : {b : A | a = b} := exist _ a eq_refl.

Lemma balance_o : forall {V : Type} (nw nw' : nat) (n: Tree V) (nr : needsRotation nw' nw)
  (WF : Property WellBalanced n),
  (weight n = nw) ->
  (nw > 3) ->
  (nw' <= 4) -> False.
Proof.
  intros.
  destruct n; simpl in *; try lia.
  - rewrite<-H in nr. unfold needsRotation in *. simpl in *. lia.
  - unfold needsRotation in *. simpl in *. lia.
Qed.

Equations balance_deep
  {V:Type}
  (n1 : Tree V) (k0 : K.t) (v0 : V) (n2 : Tree V)
  (WFn1 : Property WellBalanced n1)
  (WFn2 : Property WellBalanced n2)
  (DeepCase : IsDeepCase n1 n2)
  : Tree V
  :=
  balance_deep n1 k0 v0 n2 _ _ _ with inspect (weight n1), inspect (weight n2) :=
      { | n1w eq:Hn1w, n2w eq:Hn2w with balanceConditionLeftRotation n1w n2w :=
        { | left Hbclr with inspect n1 :=
            { | Node n1w' n11 n1k n1v n12 eq:en1' with inspect n12 :=
                { | Node n12w n121 n12k n12v n122 eq:en12 with inspect (weight n121) :=
                    { | n121w eq:Hn121w with balanceConditionLeftSingle2 (weight n11) n121w (weight n122) n2w :=
                        { | left _ := single_rotation_left_node n1w n2w n11 n1k n1v n12 k0 v0 n2
                          | right _ := double_rotation_left_node n1w n12w n2w n11 n1k n1v n12k n12v n121 n122 k0 v0 n2
                        }
                    }
                  | _ := single_rotation_left_node n1w n2w n11 n1k n1v n12 k0 v0 n2
                };
              | _ 
                  (*n1' eq:en1'
                   *)
                  with balance_o n2w n1w n1 Hbclr WFn1 _ _ _ := {  }
                  (*
                  := False_rect (Tree V) _
                   *)
            }
          | right Hbclr with balanceConditionRightRotation n1w n2w :=
              { | left Hbcrr with inspect n2 :=
                  { | Node n2w' n21 n2k n2v n22 eq:en2' with inspect n21 :=
                      { | Node n21w n211 n21k n21v n212 eq:en21 with inspect (weight n211) :=
                          { | n211w eq:Hn211w with balanceConditionRightSingle2 n1w n211w (weight n212) (weight n22) :=
                             { | left _ := single_rotation_right_node n1w n2w n1 k0 v0 n21 n2k n2v n22
                               | right _ := double_rotation_right_node n1w n21w n2w n1 k0 v0 n21k n21v n211 n212 n2k n2v n22
                             }
                          }
                        | _ := single_rotation_right_node n1w n2w n1 k0 v0 n21 n2k n2v n22
                      };

                    | _ 
                        with balance_o n1w n2w n2 Hbcrr WFn2 _ _ _ := {  }
                      (*
                    | _  eq:_ := False_rect (Tree V) _
                       *)
                  }
                | right Hbcrr := Node (n1w + n2w) n1 k0 v0 n2
              }
        }
  }.
Next Obligation. destruct n2; auto; try contradiction. wfns V WFn2. Qed.
Next Obligation. destruct n2; auto; try contradiction. wfns V WFn2. Qed.
Next Obligation. destruct n2; auto; try contradiction. wfns V WFn2. Qed.
Next Obligation. destruct n2; auto; try contradiction. wfns V WFn2. Qed.
Next Obligation. destruct n2; auto; try contradiction. wfns V WFn2. Qed.
Next Obligation. destruct n2; auto; try contradiction. wfns V WFn2. Qed.
Next Obligation. destruct n2; auto; try contradiction. wfns V WFn2. Qed.
Next Obligation. destruct n2; auto; try contradiction. wfns V WFn2. Qed.
Next Obligation. destruct n1; auto; simpl in *; try contradiction. wfns V WFn1. Qed.
Next Obligation. destruct n1; auto; simpl in *; try contradiction. wfns V WFn1. Qed.
Next Obligation. destruct n1; auto; simpl in *; try contradiction. wfns V WFn1. Qed.
Next Obligation. destruct n1; auto; simpl in *; try contradiction. wfns V WFn1. Qed.
Next Obligation. destruct n1; auto; simpl in *; try contradiction. wfns V WFn1. Qed.
Next Obligation. destruct n1; auto; simpl in *; try contradiction. wfns V WFn1. Qed.
Next Obligation. destruct n1; auto; simpl in *; try contradiction. wfns V WFn1. Qed.
Final Obligation. destruct n1; auto; simpl in *; try contradiction. wfns V WFn1. Qed.

Equations balance_shallow
  {V:Type}
  (n1 : Tree V) (k0 : K.t) (v0 : V) (n2 : Tree V)
  (WFn1 : Property WellBalanced n1)
  (WFn2 : Property WellBalanced n2)
  : Tree V
  :=
  balance_shallow n1 k0 v0 n2 _ _ with inspect n1, inspect n2 :=
  {
(*$ 
let () = Printf.printf "\n"
let () = List.iter shallow_cases ~f:(fun l ->
  Printf.printf "%s\n" (Line.to_rocq l)
   )
let () = List.iter fusion_cases ~f:(fun l ->
  Printf.printf "%s\n" (Line.to_rocq l)
   )
*)
  | Empty eq:_
  , Empty eq:_ :=
    V1 k0 v0
  | V1 k1 v1 eq:_
  , Empty eq:_ :=
    V2 k1 v1 k0 v0
  | Empty eq:_
  , V1 k2 v2 eq:_ :=
    V2 k0 v0 k2 v2
  | V1 k1 v1 eq:_
  , V1 k2 v2 eq:_ :=
    V3 k1 v1 k0 v0 k2 v2
  | V2 k11 v11 k1 v1 eq:_
  , Empty eq:_ :=
    V3 k11 v11 k1 v1 k0 v0
  | Empty eq:_
  , V2 k21 v21 k2 v2 eq:_ :=
    V3 k0 v0 k21 v21 k2 v2
  | V3 k11 v11 k1 v1 k12 v12 eq:_
  , Empty eq:_ :=
    Node 5 (V2 k11 v11 k1 v1) k12 v12 (V1 k0 v0)
  | Empty eq:_
  , V3 k21 v21 k2 v2 k22 v22 eq:_ :=
    Node 5 (V2 k0 v0 k21 v21) k2 v2 (V1 k22 v22)
  | Node _ (V3 k111 v111 k11 v11 k112 v112) k1 v1 (V1 k12 v12) eq:_
  , V1 k2 v2 eq:_ :=
    Node 8 (V3 k111 v111 k11 v11 k112 v112) k1 v1 (V3 k12 v12 k0 v0 k2 v2)
  | V1 k1 v1 eq:_
  , Node _ (V1 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222) eq:_ :=
    Node 8 (V3 k1 v1 k0 v0 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222)
  | Node _ (Node 5 n111 k11 v11 n112) k1 v1 (V1 k12 v12) eq:_
  , V1 k2 v2 eq:_ :=
    Node 9 (Node 5 n111 k11 v11 n112) k1 v1 (V3 k12 v12 k0 v0 k2 v2)
  | V1 k1 v1 eq:_
  , Node _ (V1 k21 v21) k2 v2 (Node 5 n221 k22 v22 n222) eq:_ :=
    Node 9 (V3 k1 v1 k0 v0 k21 v21) k2 v2 (Node 5 n221 k22 v22 n222)
  | Node _ (V1 k11 v11) k1 v1 (V3 k121 v121 k12 v12 k122 v122) eq:_
  , V1 k2 v2 eq:_ :=
    Node 8 (V3 k11 v11 k1 v1 k121 v121) k12 v12 (V3 k122 v122 k0 v0 k2 v2)
  | V1 k1 v1 eq:_
  , Node _ (V3 k211 v211 k21 v21 k212 v212) k2 v2 (V1 k22 v22) eq:_ :=
    Node 8 (V3 k1 v1 k0 v0 k211 v211) k21 v21 (V3 k212 v212 k2 v2 k22 v22)
  | Node _ (V1 k11 v11) k1 v1 (Node _ (V1 k121 v121) k12 v12 (V2 k1221 v1221 k122 v122)) eq:_
  , V1 k2 v eq:_ :=
    Node 9 (V3 k11 v11 k1 v1 k121 v121) k12 v12 (Node 5 (V2 k1221 v1221 k122 v122) k0 v0 (V1 k2 v))
  | V1 k1 v1 eq:_
  , Node _ (Node _ (V2 k2111 v2111 k211 v211) k21 v21 (V1 k212 v212)) k2 v2 (V1 k22 v22) eq:_ :=
    Node 9 (Node 5 (V1 k1 v1) k0 v0 (V2 k2111 v2111 k211 v211)) k21 v21 (V3 k212 v212 k2 v2 k22 v22)
  | Node _ (V1 k11 v11) k1 v1 (Node _ (V2 k1211 v1211 k121 v121) k12 v12 (V1 k122 v122)) eq:_
  , V1 k2 v2 eq:_ :=
    Node 9 (V3 k11 v11 k1 v1 k1211 v1211) k121 v121 (Node 5 (V2 k12 v12 k122 v122) k0 v0 (V1 k2 v2))
  | V1 k1 v1 eq:_
  , Node _ (Node _ (V1 k211 v211) k21 v21 (V2 k2121 v2121 k212 v212)) k2 v2 (V1 k22 v22) eq:_ :=
    Node 9 (Node 5 (V1 k1 v1) k0 v0 (V2 k211 v211 k21 v21)) k2121 v2121 (V3 k212 v212 k2 v2 k22 v22)
  | Node _ (V2 k111 v111 k11 v11) k1 v1 (Node _ (V2 k1211 v1211 k121 v121) k12 v12 (V1 k122 v122)) eq:_
  , V1 k2 v2 eq:_ :=
    Node 10 (Node 6 (V2 k111 v111 k11 v11) k1 v1 (V2 k1211 v1211 k121 v121)) k12 v12 (V3 k122 v122 k0 v0 k2 v2)
  | V1 k1 v1 eq:_
  , Node _ (Node _ (V1 k211 v211) k21 v21 (V2 k2121 v2121 k212 v212)) k2 v2 (V2 k221 v221 k22 v22) eq:_ :=
    Node 10 (V3 k1 v1 k0 v0 k211 v211) k21 v21 (Node 6 (V2 k2121 v2121 k212 v212) k2 v2 (V2 k221 v221 k22 v22))
  | Node _ (V1 k11 v11) k1 v1 (V2 k121 v121 k12 v12) eq:_
  , Empty eq:_ :=
    Node 6 (V2 k11 v11 k1 v1) k121 v121 (V2 k12 v12 k0 v0)
  | Empty eq:_
  , Node _ (V1 k21 v21) k2 v2 (V2 k221 v221 k22 v22) eq:_ :=
    Node 6 (V2 k0 v0 k21 v21) k2 v2 (V2 k221 v221 k22 v22)
  | Node _ (V2 k111 v111 k11 v11) k1 v1 (V1 k12 v12) eq:_
  , Empty eq:_ :=
    Node 6 (V2 k111 v111 k11 v11) k1 v1 (V2 k12 v12 k0 v0)
  | Empty eq:_
  , Node _ (V2 k211 v211 k21 v21) k2 v2 (V1 k22 v22) eq:_ :=
    Node 6 (V2 k0 v0 k211 v211) k21 v21 (V2 k2 v2 k22 v22)
  | Node _ (V2 k111 v111 k11 v11) k1 v1 (V2 k121 v121 k12 v12) eq:_
  , Empty eq:_ :=
    Node 7 (V2 k111 v111 k11 v11) k1 v1 (V3 k121 v121 k12 v12 k0 v0)
  | Empty eq:_
  , Node _ (V2 k211 v211 k21 v21) k2 v2 (V2 k221 v221 k22 v22) eq:_ :=
    Node 7 (V3 k0 v0 k211 v211 k21 v21) k2 v2 (V2 k221 v221 k22 v22)
  | Node _ (V3 k111 v111 k11 v11 k112 v112) k1 v1 (V2 k121 v121 k12 v12) eq:_
  , Empty eq:_ :=
    Node 8 (V3 k111 v111 k11 v11 k112 v112) k1 v1 (V3 k121 v121 k12 v12 k0 v0)
  | Empty eq:_
  , Node _ (V2 k211 v211 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222) eq:_ :=
    Node 8 (V3 k0 v0 k211 v211 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222)
  | Node _ (V3 k111 v111 k11 v11 k112 v112) k1 v1 (V1 k12 v12) eq:_
  , Empty eq:_ :=
    Node 7 (V3 k111 v111 k11 v11 k112 v112) k1 v1 (V2 k12 v12 k0 v0)
  | Empty eq:_
  , Node _ (V1 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222) eq:_ :=
    Node 7 (V2 k0 v0 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222)
  | Node _ (V1 k11 v11) k1 v1 (V3 k121 v121 k12 v12 k122 v122) eq:_
  , Empty eq:_ :=
    Node 7 (V3 k11 v11 k1 v1 k121 v121) k12 v12 (V2 k122 v122 k0 v0)
  | Empty eq:_
  , Node _ (V3 k211 v211 k21 v21 k212 v212) k2 v2 (V1 k22 v22) eq:_ :=
    Node 7 (V2 k0 v0 k211 v211) k21 v21 (V3 k212 v212 k2 v2 k22 v22)
  | V1 _ _ eq:_
  , V2 _ _ _ _ eq:_ :=
    Node 5 n1 k0 v0 n2
  | V2 _ _ _ _ eq:_
  , V1 _ _ eq:_ :=
    Node 5 n1 k0 v0 n2
  | V1 _ _ eq:_
  , V3 _ _ _ _ _ _ eq:_ :=
    Node 6 n1 k0 v0 n2
  | V3 _ _ _ _ _ _ eq:_
  , V1 _ _ eq:_ :=
    Node 6 n1 k0 v0 n2
  | V2 _ _ _ _ eq:_
  , V2 _ _ _ _ eq:_ :=
    Node 6 n1 k0 v0 n2
  | V2 _ _ _ _ eq:_
  , V3 _ _ _ _ _ _ eq:_ :=
    Node 7 n1 k0 v0 n2
  | V3 _ _ _ _ _ _ eq:_
  , V2 _ _ _ _ eq:_ :=
    Node 7 n1 k0 v0 n2
  | V3 _ _ _ _ _ _ eq:_
  , V3 _ _ _ _ _ _ eq:_ :=
    Node 8 n1 k0 v0 n2
  | V2 k11 v11 k1 v1 eq:_
  , Node _ (V2 k211 v211 k21 v21) k2 v2 (V1 k22 v22) eq:_ :=
    Node 8 (V3 k11 v11 k1 v1 k0 v0) k211 v211 (V3 k21 v21 k2 v2 k22 v22)
  | V2 k11 v11 k1 v1 eq:_
  , Node _ (V1 k21 v21) k2 v2 (V2 k221 v221 k22 v22) eq:_ :=
    Node 8 (V3 k11 v11 k1 v1 k0 v0) k21 v21 (V3 k2 v2 k221 v221 k22 v22)
  | Node _ (V2 k111 v111 k11 v11) k1 v1 (V1 k12 v12) eq:_
  , V2 k21 v21 k2 v2 eq:_ :=
    Node 8 (V3 k111 v111 k11 v11 k1 v1) k12 v12 (V3 k0 v0 k21 v21 k2 v2)
  | Node _ (V1 k11 v11) k1 v1 (V2 k121 v121 k12 v12) eq:_
  , V2 k21 v21 k2 v2 eq:_ :=
    Node 8 (V3 k11 v11 k1 v1 k121 v121) k12 v12 (V3 k0 v0 k21 v21 k2 v2)
(*$*)
  | _ eq:_, _ eq:_ :=
      balance_deep n1 k0 v0 n2 _ _ _
  }.


Lemma balance_deep_WeightConsistent
  {V : Type} (n1 : Tree V) (k0 : K.t) (v0 : V) (n2 : Tree V)
  (WFn1 : Property WellBalanced n1) (WFn2 : Property WellBalanced n2) (DeepCase : IsDeepCase n1 n2)
  : Property [ WeightConsistent ] (balance_deep n1 k0 v0 n2 WFn1 WFn2 DeepCase).
Proof.
  funelim (balance_deep n1 k0 v0 n2 WFn1 WFn2 DeepCase).
  all: try (eapply single_rotation_left_node_WeightConsistent; shelve).
  all: try (eapply single_rotation_right_node_WeightConsistent; shelve).
  all: try (eapply double_rotation_left_node_WeightConsistent; shelve).
  all: try (eapply double_rotation_right_node_WeightConsistent; shelve).
  constructor; analyze_node_cases.
  repeat constructor; simpl.
  epose proof (Property_This WeightConsistent _ WFn1 _) as WC1.
  epose proof (Property_This WeightConsistent _ WFn2 _) as WC2.
  unfold WeightConsistent in *; lia.
  Unshelve.
  all: analyze_node_cases.
  repeat constructor; analyze_node_cases. simpl.
  epose proof (Property_This WeightConsistent _ Hr _) as WC1.
  epose proof (Property_This WeightConsistent _ Hr0 _) as WC2.
  unfold WeightConsistent in *; lia.
Qed.

Lemma balance_shallow_WeightConsistent
  {V : Type} (n1 : Tree V) (k0 : K.t) (v0 : V) (n2 : Tree V)
  (WFn1 : Property WellBalanced n1) (WFn2 : Property WellBalanced n2)
  : Property [ WeightConsistent ] (balance_shallow n1 k0 v0 n2 WFn1 WFn2).
Proof.
  funelim (balance_shallow n1 k0 v0 n2 WFn1 WFn2).
  all: try match goal with
           | [ |- context [ balance_deep ?n1' ?k0' ?v0' ?n2' ?WFn1' ?WFn2' ?DeepCase ] ] =>
               epose proof (balance_deep_WeightConsistent n1' k0' v0' n2' WFn1' WFn2' DeepCase); auto
           end.
  all: repeat constructor; analyze_node_cases.
Qed.

Lemma balance_deep_WellBalanced
  {V : Type} (n1 : Tree V) (k0 : K.t) (v0 : V) (n2 : Tree V)
  (WFn1 : Property WellBalanced n1) (WFn2 : Property WellBalanced n2) (DeepCase : IsDeepCase n1 n2)
  (VI : ValidInputImbalance (weight n1) (weight n2))
  : Property WellBalanced (balance_deep n1 k0 v0 n2 WFn1 WFn2 DeepCase).
Proof.
  funelim (balance_deep n1 k0 v0 n2 WFn1 WFn2 DeepCase).
  all: match goal with
       | [ |- context [ single_rotation_right_node ] ] => eapply single_rotation_right_node_WellBalanced
       | [ |- context [ double_rotation_right_node ] ] => eapply double_rotation_right_node_WellBalanced
       | [ |- context [ double_rotation_left_node ] ] => eapply double_rotation_left_node_WellBalanced
       | [ |- context [ single_rotation_left_node ] ] => eapply single_rotation_left_node_WellBalanced
       | _ => idtac
       end.
  all: analyze_node_cases.
  repeat constructor; analyze_node_cases.
  - simpl; destruct_node_cases 6; simpl in *; lia.
  - epose proof (Property_This WeightConsistent _ WFn1 _).
    epose proof (Property_This WeightConsistent _ WFn2 _).
    unfold WeightConsistent in *; simpl; lia.
  - simpl; unfold IsDeepCase in *; destruct_node_cases_h 6.
  - unfold needsRotation, omega2, delta2 in *; lia.
  - unfold needsRotation, omega2, delta2 in *; lia.
Qed.

Lemma balance_shallow_WellBalanced
  {V : Type} (n1 : Tree V) (k0 : K.t) (v0 : V) (n2 : Tree V)
  (WFn1 : Property WellBalanced n1) (WFn2 : Property WellBalanced n2)
  (VI : ValidInputImbalance (weight n1) (weight n2))
  : Property WellBalanced (balance_shallow n1 k0 v0 n2 WFn1 WFn2).
Proof.
  funelim (balance_shallow n1 k0 v0 n2 WFn1 WFn2).
  all: match goal with
       | [ |- context [ balance_deep ] ] => eapply balance_deep_WellBalanced; auto
       | _ => idtac
       end.
  all: repeat constructor; analyze_node_cases.
  all: simpl; auto.
  destruct_node_cases 6.
Qed.

End Balanced.
