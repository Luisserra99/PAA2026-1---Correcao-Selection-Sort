From Stdlib Require Import Arith List Lia.
From Stdlib Require Import Recdef.
From Stdlib Require Import Sorted.
From Stdlib Require Import Permutation.

(** A função [select_min] a seguir, recebe uma lista de naturais e retorna o menor elemento desta lista. Se a lista for vazia, [select_min nil] retorna None. *)

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

(** A correção da função [select_min] é estabelecida provando-se que, se [select_min l] retorna um natural [m] então [m] é menor ou igual do que todos os elementos de [l]. *)

Lemma select_min_correct : forall l m, select_min l = Some m -> le_all m l.
Proof.
  intros l m H. functional induction (select_min l). Admitted.

(** A função principal [ss] recebe uma lista de naturais [l], e retorna uma permutação ordenada de [l]: *)
  
Fixpoint ss (l: list nat) :=
  match l with
  | nil => nil
  | h::tl => match select_min l with
             | None => nil
             | Some m => m::(ss tl)
             end
  end.

(** A correção do algoritmo [ss] é obtida a partir da prova de que [ss] retorna uma permutação ordenada da lista de entrada. *)

Theorem selectionsort_correct: forall l, Sorted le (ss l) /\ Permutation l (ss l)
.
Proof. Admitted.

   
 
  
