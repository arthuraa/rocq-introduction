From stdpp Require Import ssreflect base list.

(** Now that we have explored the basics of Rocq, let us see how to use it more
    effectively.  We will be using the standard library of Rocq together with
    the stdpp library, which provides several convenience features that are not
    included there.  The basic datatypes [nat] and [list] are already defined in
    those libraries.  They use a notation mechanism to make it easier for us to
    write programs: *)

Compute 1.
Compute 1 + 2.
Compute []. (* Empty list *)
Compute 1 :: []. (* Cons *)
Compute [1].
Compute [1] ++ [2].




(** These notations are just a convenience feature: under the hood, Rocq still
    sees a function applied to arguments.  We can turn off notation printing
    momentarily to see what is going on more explicitly. *)

Unset Printing Notations.
Check [1] ++ [2].
Set Printing Notations.




(** There are several other datatypes that are available for us out of the box.
    The type [bool] contains the booleans [true] and [false].  We can write
    basic boolean operations using familiar syntax: *)

Compute true && false.
Compute true || false.

(** We will now develop our first non-trivial verified program: an
    implementation of insertion sorting on lists of natural numbers.  We begin
    with a function that inserts a number [x] in the list [xs] in the correct
    position, assuming that [xs] is already sorted.  The [<=?] operator returns
    [true] if and only if one number is less than the other. *)

Fixpoint insert (x : nat) (xs : list nat) : list nat :=
[].




Fixpoint sort (xs : list nat) : list nat :=
[].



Compute sort [5; 4; 4; 1; 3].




(** We will now prove that this algorithm is correct. What properties should we
    prove? We will focus on the following two:

    - The elements of the result are in ascending order.

    - The result contains the same elements as the input.  If an element occurs
      more than once, its multiplicity should be maintained.

    We begin with the second one, since it is simpler.  We define a function
    [count] that counts how many times a number occurs in a list.

*)

Fixpoint count (x : nat) (xs : list nat) : nat :=
0.



(** How should we prove that [sort] preserves [count]? Because [sort] is defined
    using [insert], we begin by showing what [insert] does to [count]. *)

Lemma count_insert x y xs :
  count x (insert y xs) = Nat.b2n (x =? y) + count x xs.
Proof. Admitted.


Lemma count_sort x xs : count x (sort xs) = count x xs.
Proof. Admitted.


(** For the first requirement, we will write a predicate [sorted xs], which
    holds true precisely when the elements of [xs] are sorted.  Logical
    statements in Rocq are first-class citizens; they are just elements of the
    type [Prop].  To write a predicate, we just need to write a function that
    returns a [Prop]. *)

Definition lt_hd x xs :=
  match xs with
  | [] => True
  | y :: _ => x <= y
  end.

Fixpoint sorted (xs : list nat) : Prop :=
False.



(** It is worth stopping to discuss one common source of confusion to Rocq
    beginners: the difference between booleans and propositions.  A boolean in
    Rocq eventually computes to either [true] or [false].  The operators [&&]
    and [||] are functions on booleans, and the comparison operator [<=?]
    returns a boolean.  By constrast, propositions do not usually compute to
    something that is trivially true or false: we must manually prove whether
    the proposition holds or not.

    We define [sorted] in terms of the [lt_hd] predicate.  For sorted lists,
    this predicate is equivalent to ensuring that an element is a lower bound of
    a list. *)

Lemma lt_hd_sorted x xs :
  sorted xs ->
  lt_hd x xs <-> (forall y, y ∈ xs -> x <= y).
Proof. Admitted.


Lemma elem_of_insert x y xs : elem_of x (insert y xs) <-> x = y \/ elem_of x xs.
Proof. Admitted.


Lemma sorted_insert x xs : sorted xs -> sorted (insert x xs).
Proof. Admitted.


Lemma sorted_sort xs : sorted (sort xs).
Proof. Admitted.


(** Now that we have verified our sorting function, we can extract it to an
    OCaml implementation. *)

Require Extraction.

Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive nat  => "int" ["0" "(fun n -> n + 1)"]
  "(fun fO fS n -> if n = 0 then fO () else fS (n - 1))".
Extract Inductive list => "list" ["[]" "(::)"].

Extraction "sort.ml" sort.

(** Exercise: Alternate Definition of Sorted

    This defines an alternative version of the [sorted] predicate. Prove that it
    is equivalent to the original one. *)

Fixpoint sorted' xs : Prop :=
  match xs with
  | [] => True
  | x :: xs => (forall y, elem_of y xs -> x <= y) /\ sorted' xs
  end.

Lemma sorted_alt xs : sorted xs <-> sorted' xs.
Proof. Admitted.


(** Exercise: Tail-Recursive Sorting

    The following tail-recursive implementation also sorts the list, but using
    less auxiliary stack space. Prove that it is also a valid implementation of
    sorting. *)

Fixpoint tr_sort_aux xs acc :=
  match xs with
  | [] => acc
  | x :: xs => tr_sort_aux xs (insert x acc)
  end.

Definition tr_sort xs := tr_sort_aux xs [].




(** Exercise: Equal sorted lists

    If two sorted lists have the same counts, they must be the same. Prove this
    fact.  *)




Lemma sorted_eq xs ys :
  sorted xs ->
  sorted ys ->
  (forall x, count x xs = count x ys) ->
  xs = ys.
Proof. Admitted.


(** Exercise: Sorting Twice

    Prove that sorting a sorted list does not modify the input. *)

Lemma sort_sorted xs : sorted xs -> sort xs = xs.
Proof. Admitted.


(** Exercise: Tail-Recursive Sorting, redux

    Prove that [tr_sort] and [sort] always return the same results. *)

Lemma tr_sort_sort xs : tr_sort xs = sort xs.
Proof. Admitted.

