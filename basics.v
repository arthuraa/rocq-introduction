(** We are going to start by exploring basic functionalities of the Rocq
    languages: how we define datatypes, functions, and write proofs.  Many of
    these definitions are provided by the Rocq standard library, but we'll start
    from scratch to understand how things work under the hood. Later, we'll see
    how to use external libraries. For now, we will just import the stdpp
    library, which will provide various convenient commands for us to use. *)

From stdpp Require Import base ssreflect.

(** The first thing we'll do is to define a number type.  A natural number is a
    type that is defined inductively by two constructors: O and S.  *)

Inductive nat : Type :=
| O
| S (n : nat).

(** We can define constants and functions using the [Definition] keyword. *)

Definition zero : nat := O.
Definition one : nat := S zero.
Definition two : nat := S one.

Definition succ (n : nat) : nat := S n.
Definition plus_two (n : nat) : nat := succ (succ n).

(** We can also define functions recursively using the [Fixpoint] keyword. *)

Fixpoint add n m :=
  match n with
  | O => m
  | S n' => S (add n' m)
  end.

(** The [Compute] command allows us to evaluate the result of an expression. *)

Compute add two two.

(** What makes Rocq different from other languages is that we can state
    properties about our definitions and try to prove them. For example: *)

Lemma add_l_0 : forall n, add O n = n.

(** To prove this result, we must enter a sequence of _tactics_: commands that
    instruct Rocq to apply deduction rules. *)

Proof.      (* Start proof *)
intros n.   (* Name the quantified variable *)
rewrite /=. (* Simplify definitions in the goal *)
auto.       (* Rocq can conclude automatically: everything is equal to itself *)
Qed.        (* Assert that the proof is over *)

(** This result is so simple that the [auto] tactic is enough.  In general,
    [auto] will try to prove a goal by chaining together a series of elementary
    proof steps, up to some limit. *)

Lemma add_l_0' : forall n, add O n = n.
Proof. auto. Qed.

(** Some results require more effort.  For example: *)

Lemma add_r_0 : forall n, add n O = n.
Proof.
intros n.
rewrite /=. (* Nothing happens... *)
auto. (* Still nothing *)

(** The problem is that [add] is defined by case analysis on its first argument.
    Since the first argument is a variable, Rocq does not attempt to simplify
    anything.

    We can try to make some progress by performing a case analysis.  The
    [destruct] tactic tells Rocq to consider all constructors that could have
    been used to form a value.  Each constructor generates a subcase in our
    proof. *)

destruct n as [|m]. (* Either n is [O] or [S m] *)
- auto.
- rewrite /=.

(** Here, we'll need something stronger than [destruct].  The [induction] tactic
    performs a proof by induction.  It is similar to [destruct], except that it
    gives us an induction hypothesis. *)

Restart.

intros n. induction n as [|m IH].
- rewrite /=. auto.
- rewrite /= IH. (* Simplify and rewrite with the induction hypothesis *)
  auto.
Qed.

(** Let's try to prove some other results. *)

Lemma add_l_S : forall n m, add (S n) m = S (add n m).
Proof. auto. Qed.

Lemma add_r_S : forall n m, add n (S m) = S (add n m).
Proof. Admitted.

Lemma add_comm n m : add n m = add m n.
Proof. Admitted.

(** Besides equality and [forall], we have many other logical connectives to
    write theorem statements.  For example: *)

Lemma add_eq_0 : forall n m, add n m = O -> n = O /\ m = O.

(** In words, if [n + m] is 0, then both [n] and [m] are 0. *)

Proof.
intros n m H.
(* Run one tactic after the other, including all subgoals *)
destruct n as [|n]; destruct m as [|m].

(** The first goal is trivial. We use the [split] tactic to prove each side of
    the conjunction in a separate subgoal. *)

- split.
  + done.
  + done.

(** The following goals are contradictory: they assert that a non-zero number
    equals zero. [done] knows that different constructors yield different
    values and allows us to finish the proof. *)

- rewrite /= in H. done.
- rewrite /= in H. done.
- rewrite /= in H. done.
Qed.

Lemma add_eq_S : forall n m p, add n m = S p -> exists k, n = S k \/ m = S k.
Proof.

intros n m p H.
destruct n as [|n]; destruct m as [|m].

- rewrite /= in H. done.
- exists m. right. done.
- exists n. left. done.
- exists n. left. done.

Qed.


(** We can also define more interesting data types.  The following declaration
    defines a data type [list T] that is parameterized by the type [T] of
    elements stored in the list.  *)

Inductive list (T : Type) : Type :=
| nil (* An empty list *)
| cons (x : T) (xs : list T) (* A list with first element [x] followed by [xs] *).

(** Similarly to some languages (e.g. old versions of C++), we need to specify
    what the type is when invoking a constructor: *)

Definition ex1 : list nat :=
  (* An empty list of nats *)
  nil nat.

Definition ex2 : list nat :=
  (* A list with zero and nothing else *)
  cons nat zero (nil nat).

(** Since this to annoying to use, we can ask Rocq to infer what these types are
    automatically: *)

Arguments nil {T}.
Arguments cons {T}.

Definition ex1' : list nat := nil.
Definition ex2' : list nat := cons zero nil.

(** We can define generic, or polymorphic, functions on lists. The following
    function appends one list onto another.  Note that we use curly braces to
    tell Rocq to always infer the type T, whenever possible. *)

Fixpoint app {T} (xs ys : list T) : list T :=
  match xs with
  | nil => ys
  | cons x xs' => cons x (app xs' ys)
  end.

(** Lemmas can also be polymorphic. Note that we can perform induction directly
    any type defined inductively: we get as many cases as we have constructors,
    each constructor requires us to name its arguments, and each recursive
    argument comes with an induction hypothesis. *)

Lemma app_nil_l : forall T (xs : list T), app nil xs = xs.
Proof. done. Qed.

Lemma app_nil_r : forall T (xs : list T), app xs nil = xs.
Proof.
intros T xs.
induction xs as [|x xs IH].
- done.
- rewrite /= IH. done.
Qed.

Lemma app_assoc :
  forall T (xs ys zs : list T), app xs (app ys zs) = app (app xs ys) zs.
Proof. Admitted.
