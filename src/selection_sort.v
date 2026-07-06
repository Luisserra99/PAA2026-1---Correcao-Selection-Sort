From Stdlib Require Import Arith List Lia.
From Stdlib Require Import Recdef.
From Stdlib Require Import Sorted.
From Stdlib Require Import Permutation.
Import ListNotations.


(** [select_min] recebe uma lista de naturais e retorna o menor elemento
    desta lista. Se a lista for vazia, [select_min nil] retorna None. *)

Function select_min (l : list nat) {measure length l} : option nat :=
  match l with
  | nil => None
  | h::nil => Some h
  | h1::h2::tl => if h1 <=? h2 then select_min (h1::tl) else select_min (h2::tl)
  end.
Proof.
  - auto.
  - auto.
Defined.

Definition le_all x l := forall y, In y l -> x <= y.

(** Se [select_min l] retorna um natural [m], então [m] é menor ou igual a
    todos os elementos da lista [l]. *)
Lemma select_min_correct : forall l m, select_min l = Some m -> le_all m l.
Proof.
  intros l m H.
  functional induction (select_min l).
  - discriminate H.
  - injection H as ->.
    intros y Hy. simpl in Hy. destruct Hy as [-> | []]. apply le_n.
  - (* h1 <=? h2 = true *)
    apply IHo in H.
    intros y Hy. simpl in Hy.
    match goal with | He0 : (_ <=? _) = true |- _ => rename He0 into e0 end.
    apply Nat.leb_le in e0.
    destruct Hy as [-> | [-> | Hy]].
    + apply H. simpl. left. reflexivity.
    + apply Nat.le_trans with h1.
      * apply H. simpl. left. reflexivity.
      * exact e0.
    + apply H. simpl. right. exact Hy.
  - (* h1 <=? h2 = false *)
    apply IHo in H.
    intros y Hy. simpl in Hy.
    match goal with | He0 : (_ <=? _) = false |- _ => rename He0 into e0 end.
    apply Nat.leb_gt in e0.
    destruct Hy as [-> | [-> | Hy]].
    + apply Nat.le_trans with h2.
      * apply H. simpl. left. reflexivity.
      * lia.
    + apply H. simpl. left. reflexivity.
    + apply H. simpl. right. exact Hy.
Qed.

(** Se [select_min l] retorna [Some m], então [m] pertence a [l]. Isso é
    necessário para garantir que [remove_one] de fato diminui o tamanho da
    lista (usado na medida da função [ss] mais abaixo). *)
Lemma select_min_in : forall l m, select_min l = Some m -> In m l.
Proof.
  intros l m H.
  functional induction (select_min l).
  - discriminate H.
  - injection H as ->. simpl. left. reflexivity.
  - apply IHo in H. simpl in H. simpl.
    destruct H as [H | H].
    + left. exact H.
    + right. right. exact H.
  - apply IHo in H. simpl in H. simpl.
    destruct H as [H | H].
    + right. left. exact H.
    + right. right. exact H.
Qed.

(** se [select_min l = None], então [l] é vazia (o único caso da
    definição que retorna None é o caso nil). *)
Lemma select_min_none : forall l, select_min l = None -> l = nil.
Proof.
  intros l H.
  functional induction (select_min l).
  - reflexivity.
  - discriminate H.
  - apply IHo in H. discriminate H.
  - apply IHo in H. discriminate H.
Qed.

