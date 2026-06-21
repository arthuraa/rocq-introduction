From stdpp Require Import base ssreflect.

(** We can understand logical connectives by asking two questions:

    1. How to I prove a formula with that connective?
    2. How do I use a hypothesis involving that connective?

    In logic jargon, 1 is known as _introducing_ that connective, and 2 is known
    as _eliminating_ it.  In Rocq, each one of these tasks is done with a
    separate tactic.

    | connective  | introduction | elimination |
    |-------------|--------------|-------------|
    | forall      | intros       | application |
    | ->          | intros       | application |
    | exists      | exists       | destruct    |
    | /\          | split        | destruct    |
    | \/          | left, right  | destruct    |
    | =           | done         | rewrite     |
    | True        | done         |             |
    | False       |              | destruct    |

    Here are some examples:

*)

Lemma forall_intro : forall n : nat, n = n.
Proof. intros n. done. Qed.

Lemma forall_elim : (forall n, n = 4) -> 0 = 4.
Proof. intros H. apply (H 0). Qed.

Lemma impl_intro : forall (P : Prop), P -> P.
Proof. intros P H. apply H. Qed.

Lemma impl_elim : forall (P Q : Prop), ((P -> P) -> Q) -> Q.
Proof. intros P Q H. apply (H (impl_intro P)). Qed.

Lemma exists_intro : exists n, n + n = 4.
Proof. exists 2. done. Qed.

Lemma exists_elim : forall b, (exists c, b && c = true) -> b = true.
Proof.
intros b H. destruct H as [c H]. destruct b; done.
Qed.

Lemma and_intro : forall P Q : Prop, P -> Q -> P /\ Q.
Proof. intros P Q H. split; done. Qed.

Lemma and_elim : forall P Q, P /\ Q -> P.
Proof. intros P Q H. destruct H as [HP _]. done. Qed.

Lemma or_intro : forall P Q, P -> P \/ Q.
Proof. intros P Q. left. done. Qed.

Lemma or_intro' : forall P Q, Q -> P \/ Q.
Proof. intros P Q. right. done. Qed.

Lemma or_elim : forall n, n = 0 \/ n = 2 -> exists m, n = 2 * m.
Proof.
intros n H. destruct H as [H|H].
- rewrite H. exists 0. done.
- rewrite H. exists 1. done.
Qed.

Lemma eq_intro : forall n : nat, n = n.
Proof. done. Qed.

Lemma eq_elim : forall n m p : nat, n = m -> m = p -> n = p.
Proof. intros n m p H1 H2. rewrite H1. done. Qed.

Lemma True_intro : True.
Proof. done. Qed.

Lemma False_elim : forall P : Prop, False -> P.
Proof. intros P H. destruct H. Qed.

(** Negation

    To negate a formula [P], we write [~ P], which is a synomym for [P ->
    False]. In other words, [~ P] if we obtain a contradiction by assuming [P].
    For example: *)

Lemma neg_ex_1 : ~ False.
Proof. intros contra. apply contra. Qed.

(** Other tactics:

    - [assert]: introduce an intermediate assertion.
    - [eauto]: automatically apply hint lemmas.
    - [lia]: solve simple formulas involving integers.
    - [apply]: apply a hypothesis or previous lemma, possibly generating subgoals
    - [congruence]: basic equality reasoning involving constructors.

*)

Lemma ex1 : forall n m, S n = S m -> n * n = m * m.
Proof.
intros n m e.
assert (n = m) as e'. { congruence. }
congruence.
Qed.

Lemma ex2 : forall n m, S n <= S m -> n <= m + m.
Proof. intros n m. lia. Qed.
