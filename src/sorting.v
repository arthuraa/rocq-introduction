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

(* <skip /> *)

(** These notations are just a convenience feature: under the hood, Rocq still
    sees a function applied to arguments.  We can turn off notation printing
    momentarily to see what is going on more explicitly. *)

Unset Printing Notations.
Check [1] ++ [2].
Set Printing Notations.

(* <skip /> *)

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
(* <exercise-only>[].</exercise-only> *)
(* <solution> *)
  match xs with
  | [] => [x]
  | x' :: xs' => if x <=? x' then x :: x' :: xs'
                 else x' :: insert x xs'
  end.
(* </solution> *)


Fixpoint sort (xs : list nat) : list nat :=
(* <exercise-only>[].</exercise-only> *)
(* <solution> *)
  match xs with
  | [] => []
  | x :: xs' => insert x (sort xs')
  end.
(* </solution> *)

Compute sort [5; 4; 4; 1; 3].

(* <skip /> *)

(** We will now prove that this algorithm is correct. What properties should we
    prove? We will focus on the following two:

    - The elements of the result are in ascending order.

    - The result contains the same elements as the input.  If an element occurs
      more than once, its multiplicity should be maintained.

    We begin with the second one, since it is simpler.  We define a function
    [count] that counts how many times a number occurs in a list.

*)

Fixpoint count (x : nat) (xs : list nat) : nat :=
(* <exercise-only>0.</exercise-only> *)
(* <solution> *)
  match xs with
  | [] => 0
  | y :: xs' => Nat.b2n (x =? y) + count x xs'
  end.
(* </solution> *)

(** How should we prove that [sort] preserves [count]? Because [sort] is defined
    using [insert], we begin by showing what [insert] does to [count]. *)

Lemma count_insert x y xs :
  count x (insert y xs) = Nat.b2n (x =? y) + count x xs.
(* <admitted> *)
Proof.
induction xs as [|z xs IH]; rewrite /=.
- done.
- destruct (y <=? z); rewrite /=.
  + done.
  + rewrite IH. lia.
Qed.
(* </admitted> *)

Lemma count_sort x xs : count x (sort xs) = count x xs.
(* <admitted> *)
Proof.
induction xs as [|y xs IH]; rewrite /=.
- done.
- rewrite -IH count_insert. done.
Qed.
(* </admitted> *)

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
(* <exercise-only>False.</exercise-only> *)
(* <solution> *)
  match xs with
  | [] => True
  | x :: xs => lt_hd x xs /\ sorted xs
  end.
(* </solution> *)

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
(* <admitted> *)
Proof.
rewrite -Forall_forall.
intros sorted_xs. induction xs as [|y xs IH] in x, sorted_xs |- *.
- rewrite Forall_nil. split; auto.
- rewrite Forall_cons /= in sorted_xs *.
  destruct sorted_xs as [y_xs sorted_xs]. split.
  + intros x_y. split; auto. apply IH; auto.
    destruct xs as [|??]; rewrite /= in y_xs *; lia.
  + intros [??]; auto.
Qed.
(* </admitted> *)

Lemma elem_of_insert x y xs : x ∈ insert y xs <-> x = y \/ x ∈ xs.
(* <admitted> *)
Proof.
induction xs as [|z xs IH].
- rewrite /= elem_of_nil list_elem_of_singleton right_id. done.
- rewrite /= elem_of_cons.
  destruct (_ <=? _).
  + rewrite !elem_of_cons. done.
  + rewrite elem_of_cons IH.
    rewrite [_ ∨ _]assoc [x = z ∨ _]comm assoc. done.
Qed.
(* </admitted> *)

Lemma sorted_insert x xs : sorted xs -> sorted (insert x xs).
(* <admitted> *)
Proof.
induction xs as [|y xs IH]; rewrite /=.
- done.
- intros H. destruct H as [y_xs sorted_xs].
  assert (sorted_x_xs := IH sorted_xs).
  destruct (x <=? y) eqn:x_y; rewrite /=.
  + rewrite -Nat.leb_le. auto.
  + split; auto.
    rewrite lt_hd_sorted; auto.
    intros z Hz.
    rewrite elem_of_insert in Hz. rewrite Nat.leb_nle in x_y.
    rewrite lt_hd_sorted in y_xs; auto.
    destruct Hz as [z_x|z_xs].
    * rewrite z_x. lia.
    * apply y_xs. done.
Qed.
(* </admitted> *)

Lemma sorted_sort xs : sorted (sort xs).
(* <admitted> *)
Proof.
induction xs as [|x xs IH]; rewrite /=.
- done.
- apply sorted_insert. done.
Qed.
(* </admitted> *)

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
  | x :: xs => (forall y, y ∈ xs -> x <= y) /\ sorted' xs
  end.

Lemma sorted_alt xs : sorted xs <-> sorted' xs.
(* <admitted> *)
Proof.
induction xs as [|x xs IH]; rewrite /=; auto.
rewrite -IH. split.
- intros [x_xs sorted_xs]. rewrite -lt_hd_sorted; auto.
- intros [x_xs sorted_xs]. rewrite lt_hd_sorted; auto.
Qed.
(* </admitted> *)

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

(* <solution> *)
Lemma count_tr_sort_aux x xs acc :
  count x (tr_sort_aux xs acc) = count x xs + count x acc.
Proof.
induction xs as [|y xs IH] in acc |- *; rewrite /=; auto.
rewrite IH count_insert. lia.
Qed.

Lemma count_tr_sort x xs : count x (tr_sort xs) = count x xs.
Proof. rewrite /tr_sort count_tr_sort_aux /=. lia. Qed.

Lemma sorted_tr_sort_aux xs acc :
  sorted acc ->
  sorted (tr_sort_aux xs acc).
Proof.
induction xs as [|x xs IH] in acc |- *; rewrite /=; auto.
intros sorted_acc. apply IH. apply sorted_insert. done.
Qed.

Lemma sorted_tr_sort xs : sorted (tr_sort xs).
Proof. rewrite /tr_sort. apply sorted_tr_sort_aux. done. Qed.
(* </solution> *)

(** Exercise: Equal sorted lists

    If two sorted lists have the same counts, they must be the same. Prove this
    fact.  *)

(* <solution> *)
Lemma count_elem_of x xs : x ∈ xs <-> 0 < count x xs.
Proof.
induction xs as [|y xs IH].
- rewrite elem_of_nil /=. split; lia.
- rewrite elem_of_cons /= IH. split.
  + intros [x_y|x_xs].
    * rewrite x_y Nat.eqb_refl /=. lia.
    * lia.
  + destruct (x =? y) eqn:x_y; rewrite /=.
    * rewrite Nat.eqb_eq in x_y. auto.
    * auto.
Qed.
(* </solution> *)

Lemma sorted_eq xs ys :
  sorted xs ->
  sorted ys ->
  (forall x, count x xs = count x ys) ->
  xs = ys.
(* <admitted> *)
Proof.
induction xs as [|x xs IH] in ys |- *; rewrite /=.
- destruct ys as [|y ys]; auto.
  intros _ _ H. assert (contra := H y).
  rewrite /= Nat.eqb_refl /= in contra.
  done.
- intros [x_xs sorted_xs] sorted_ys H.
  destruct ys as [|y ys].
  + assert (contra := H x).
    rewrite /= Nat.eqb_refl /= in contra. done.
  + rewrite /= in sorted_ys. destruct sorted_ys as [y_ys sorted_ys].
    assert (forall z, z ∈ xs -> x <= z) as x_xs'.
    { rewrite -lt_hd_sorted; auto. }
    assert (forall z, z ∈ ys -> y <= z) as y_ys'.
    { rewrite -lt_hd_sorted; auto. }
    assert (x <= y) as x_y.
    { assert (Hy := H y). rewrite /= Nat.eqb_refl /= in Hy.
      destruct (y =? x) eqn:x_y.
      - rewrite Nat.eqb_eq in x_y. lia.
      - rewrite /= in Hy. apply x_xs'. rewrite count_elem_of. lia. }
    assert (y <= x) as y_x.
    { assert (Hx := H x). rewrite /= Nat.eqb_refl /= in Hx.
      destruct (x =? y) eqn:e.
      - rewrite Nat.eqb_eq in e. lia.
      - rewrite /= in Hx. apply y_ys'. rewrite count_elem_of. lia. }
    assert (x = y) as e. { lia. }
    rewrite e in H x_xs' *.
    assert (forall z, count z xs = count z ys) as H'.
    { intros z. assert (Hz := H z). rewrite /= in Hz. lia. }
    rewrite (IH _ sorted_xs sorted_ys H'). done.
Qed.
(* </admitted> *)

(** Exercise: Sorting Twice

    Prove that sorting a sorted list does not modify the input. *)

Lemma sort_sorted xs : sorted xs -> sort xs = xs.
(* <admitted> *)
Proof.
intros sorted_xs. apply sorted_eq.
- apply sorted_sort.
- auto.
- intros x. rewrite count_sort. done.
Qed.
(* </admitted> *)

(** Exercise: Tail-Recursive Sorting, redux

    Prove that [tr_sort] and [sort] always return the same results. *)

Lemma tr_sort_sort xs : tr_sort xs = sort xs.
(* <admitted> *)
Proof.
apply sorted_eq.
- apply sorted_tr_sort.
- apply sorted_sort.
- intros x. rewrite count_tr_sort count_sort. done.
Qed.
(* </admitted> *)
