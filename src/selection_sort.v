(** * Correção do Selection Sort

    Verificação formal do algoritmo Selection Sort em Rocq/Coq: prova-se que a
    função de ordenação produz uma [Permutation] da entrada que também está
    ordenada ([Sorted le]). A especificação [is_a_sorting_algorithm] e a
    estrutura das provas seguem as três referências abaixo.

    Referências:

    [1] osa1, "Proving sorting algorithms correct" (2014-09-08).
        https://osa1.net/posts/2014-09-08-proving-sorting-correct.html
        Prova insertion/selection/pancake sort corretos estabelecendo, para
        cada um, que a saída é uma permutação ordenada da entrada (predicado
        indutivo [sorted] + biblioteca [Permutation]), combinados num registro
        [Sorting_correct].

    [2] Software Foundations, Vol. 3 (Verified Functional Algorithms - VFA),
        capítulo "Selection: Selection Sort" (versão terse, Cornell CS4160).
        https://www.cs.cornell.edu/courses/cs4160/2020sp/sf/vfa/terse/Selection.html

    [3] Software Foundations, Vol. 3 (Verified Functional Algorithms - VFA),
        capítulo "Selection: Selection Sort" (versão completa).
        https://coq.vercel.app/ext/sf/vfa/full/Selection.html

    As referências [2] e [3] são o mesmo capítulo de VFA. Elas definem:
      - [select : nat -> list nat -> nat * list nat], que devolve o menor
        elemento e o restante da lista numa única passagem;
      - [selsort]/[selection_sort] com um argumento de "combustível" (fuel)
        para garantir a terminação; e
      - a especificação
        [is_a_sorting_algorithm f := forall al, Permutation al (f al) /\ sorted (f al)].
    O capítulo ainda sugere, como técnica avançada, substituir o fuel por
    [Function] com [measure] — abordagem adotada aqui (em [select_min] e [ss]).
    O predicado [sorted] de VFA equivale ao [Sorted le] da biblioteca padrão,
    usado neste arquivo.

    Correspondência entre este arquivo e VFA (referências [2] e [3]):

      este arquivo             VFA - Selection Sort
      ----------------------   -------------------------------------------
      Sorted le / Permutation  sorted / Permutation
      select_min + remove_one  select (menor + restante numa passagem)
      select_min_correct       select_smallest  (mínimo <= todo o restante)
      select_min_in            select_in        (mínimo pertence à lista)
      remove_one_perm          parte de select_perm
      remove_one_length        select_rest_length
      le_all_sorted            cons_of_small_maintains_sort
      ss  (Function/measure)   selection_sort  (selsort + fuel)
      ss_perm                  selection_sort_perm
      ss_sorted                selection_sort_sorted
      is_a_sorting_algorithm   is_a_sorting_algorithm
      selection_sort_correct   selection_sort_is_correct

    Diferença de projeto: em vez de [select] devolver o par (mínimo, resto)
    numa passagem, aqui o mínimo é obtido por [select_min] e removido por
    [remove_one min]. Isso corrige o bug da definição original de [ss], que
    recursava sobre a cauda [tl] em vez de remover o mínimo efetivamente
    encontrado. *)

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
    todos os elementos da lista [l]. Corresponde a [select_smallest] em VFA
    (referências [2] e [3]). *)
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
    lista (usado na medida da função [ss] mais abaixo). Corresponde a
    [select_in] em VFA (referências [2] e [3]). *)
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
(** [remove_one x l] remove UMA ocorrência do elemento [x] da lista [l].
    Esta função corrige o bug da definição original de [ss], que recursava
    sobre a cauda [tl] em vez de remover o mínimo efetivamente encontrado. *)
Fixpoint remove_one (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: tl => if h =? x then tl else h :: remove_one x tl
  end.

(** Remover uma ocorrência de [x] (presente em [l]) diminui estritamente o
    tamanho. Corresponde a [select_rest_length] em VFA (referências [2] e [3]),
    que garante a mesma propriedade de decréscimo para o resto devolvido por
    [select]. *)
Lemma remove_one_length : forall x l, In x l -> length (remove_one x l) < length l.
Proof.
  induction l as [| h tl IH]; intros Hin.
  - contradiction.
  - simpl. destruct (h =? x) eqn:Heq.
    + simpl. lia.
    + simpl in Hin. destruct Hin as [Hin | Hin].
      * subst. apply Nat.eqb_neq in Heq. contradiction.
      * simpl. apply IH in Hin. lia.
Qed.

Lemma remove_one_In : forall y x l, In y (remove_one x l) -> In y l.
Proof.
  intros y x l. induction l as [| h tl IH]; intros Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin. destruct (h =? x) eqn:Heq.
    + simpl. right. exact Hin.
    + simpl in Hin. destruct Hin as [Hin | Hin].
      * subst. simpl. left. reflexivity.
      * simpl. right. apply IH. exact Hin.
Qed.

(** Retirar uma ocorrência de [x] e colocá-la na cabeça é uma permutação da
    lista original. Corresponde à parte de permutação de [select_perm] em VFA
    (referências [2] e [3]). *)
Lemma remove_one_perm : forall x l, In x l -> Permutation l (x :: remove_one x l).
Proof.
  intros x l. induction l as [| h tl IH]; intros Hin.
  - contradiction.
  - simpl. destruct (h =? x) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst h. apply Permutation_refl.
    + simpl in Hin. destruct Hin as [Hin | Hin].
      * subst. apply Nat.eqb_neq in Heq. contradiction.
      * apply IH in Hin.
        apply perm_trans with (h :: x :: remove_one x tl).
        -- apply perm_skip. exact Hin.
        -- apply perm_swap.
Qed.

(** Se [l] está ordenada e [x] é menor ou igual a todos os elementos de [l],
    então [x::l] também está ordenada. Corresponde a
    [cons_of_small_maintains_sort] em VFA (referências [2] e [3]). *)
Lemma le_all_sorted : forall l x, Sorted le l -> le_all x l -> Sorted le (x :: l).
Proof.
  intros l x Hs Hall.
  constructor.
  - exact Hs.
  - destruct l as [| h tl].
    + apply HdRel_nil.
    + apply HdRel_cons. apply Hall. simpl. left. reflexivity.
Qed.

(** ** Selection sort

    [ss] é o selection sort recursivo: seleciona o mínimo da lista com
    [select_min], emite-o, e recursa sobre a lista sem esse mínimo
    ([remove_one]). A terminação é garantida por [measure length l]: cada
    chamada recursiva opera sobre [remove_one m l], estritamente menor que [l]
    porque [m] pertence a [l] ([select_min_in] seguido de [remove_one_length]).

    Corresponde a [selection_sort] em VFA (referências [2] e [3]), com
    [Function]/[measure] no lugar do argumento de combustível (fuel) — a
    técnica avançada sugerida ao final daquele capítulo. *)
Function ss (l : list nat) {measure length l} : list nat :=
  match select_min l with
  | None => nil
  | Some m => m :: ss (remove_one m l)
  end.
Proof.
  (* obrigação de terminação: length (remove_one m l) < length l *)
  intros. apply remove_one_length. apply select_min_in. assumption.
Defined.

(** Alias com o nome usado nas referências [2] e [3]. *)
Definition selection_sort (l : list nat) : list nat := ss l.

(* Testes de sanidade: [ss] de fato ordena. *)
Example ss_example : ss [3;1;2;5;0;4] = [0;1;2;3;4;5].
Proof. reflexivity. Qed.

Example ss_example_dup : ss [2;1;2;1;3] = [1;1;2;2;3].
Proof. reflexivity. Qed.

(** [ss] preserva os elementos: a saída é uma permutação da entrada.
    Corresponde a [selection_sort_perm] em VFA (referências [2] e [3]). *)
Lemma ss_perm : forall l, Permutation l (ss l).
Proof.
  intro l.
  functional induction (ss l).
  - (* select_min l = None, logo l = nil *)
    match goal with H : select_min _ = None |- _ => apply select_min_none in H end.
    subst l. apply Permutation_refl.
  - (* select_min l = Some m *)
    apply perm_trans with (m :: remove_one m l).
    + apply remove_one_perm. apply select_min_in. assumption.
    + apply perm_skip. assumption.
Qed.

(** [ss] devolve uma lista ordenada. A cada passo, o mínimo emitido é menor ou
    igual a todos os elementos restantes (por [select_min_correct] combinado
    com [remove_one_In] e [ss_perm]), então [le_all_sorted] garante que
    prependê-lo à cauda ordenada preserva a ordenação. Corresponde a
    [selection_sort_sorted] em VFA (referências [2] e [3]). *)
Lemma ss_sorted : forall l, Sorted le (ss l).
Proof.
  intro l.
  functional induction (ss l).
  - (* ss nil = nil *)
    constructor.
  - (* ss l = m :: ss (remove_one m l) *)
    apply le_all_sorted.
    + (* cauda ordenada, pela hipótese de indução *)
      assumption.
    + (* m <= y para todo y na cauda *)
      intros y Hy.
      match goal with H : select_min _ = Some _ |- _ =>
        apply select_min_correct in H; apply H end.
      (* basta mostrar In y l *)
      apply remove_one_In with (x := m).
      (* y está em ss (remove_one m l), que é permutação de remove_one m l *)
      apply Permutation_in with (l := ss (remove_one m l)).
      * apply Permutation_sym. apply ss_perm.
      * exact Hy.
Qed.

(** Especificação de "algoritmo de ordenação correto", como em VFA
    (referências [2] e [3]): [f] devolve uma permutação da entrada que está
    ordenada. Combina as duas propriedades no espírito do registro
    [Sorting_correct] de osa1 (referência [1]). *)
Definition is_a_sorting_algorithm (f : list nat -> list nat) : Prop :=
  forall l, Permutation l (f l) /\ Sorted le (f l).

(** Corretude do selection sort. Corresponde a [selection_sort_is_correct] em
    VFA (referências [2] e [3]). *)
Theorem selection_sort_correct : is_a_sorting_algorithm selection_sort.
Proof.
  intro l. unfold selection_sort. split.
  - apply ss_perm.
  - apply ss_sorted.
Qed.
