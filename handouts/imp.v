(** We are now going to use Rocq to define the semantics of a simple imperative
    programming language.  The language, known as _Imp_, only has arithmetic,
    global variables, and control flow operations (if and while).  We leave out
    complex data types, function calls, objects, etc.

    We begin by defining the abstract syntax of the language.  Imp has binary
    operations, arithmetic expressions and commands, given by the following Rocq
    data types.  (We use strings to represent variable names.) *)

From stdpp Require Import base ssreflect strings gmap.

Inductive binop :=
| Add
| Mul
| Sub
| Leq.

Inductive expr :=
(* Read the value of a global variable *)
| Var (x : string)
(* A literal *)
| Num (n : nat)
(* Apply a binary operation *)
| Binop (b : binop) (e1 e2 : expr).

Inductive com :=
(* Do nothing *)
| Skip
(* Sequence two commands *)
| Seq (c1 c2 : com)
(* Assign the current value of [e] to the variable [x] *)
| Assign (x : string) (e : expr)
(* Run [c1] if [e] is non-zero, [c2] otherwise *)
| If (e : expr) (c1 c2 : com)
(* Run [c] while [e] is non-zero *)
| While (e : expr) (c : com).




(** We will start using several features of Rocq and stdpp more freely.  Rocq
    has a type class mechanism similar to that of Haskell, which allows us to
    overload operations.  The [EqDecision] type class says that a type has a
    boolean equality operation. The [solve_decision] tactic of stdpp can be used
    to define instances for these type classes automatically. *)

Global Instance binop_eqdec : EqDecision binop.
Proof. solve_decision. Defined.

Global Instance expr_eqdec : EqDecision expr.
Proof. solve_decision. Defined.

Global Instance com_eqdec : EqDecision com.
Proof. solve_decision. Defined.




(** We will now define several functions for evaluating programs of our
    language. First, we define a function [eval_binop] that applies a binary
    operation to two numbers.

    ([bool_decide P] is an stdpp function that returns [true] if and only if [P]
    holds.  It only works for propositions that were shown to be decidable, like
    we did for equality on [com].) *)

Definition eval_binop b :=
  match b with
  | Add => Nat.add
  | Mul => Nat.mul
  | Sub => Nat.sub
  | Leq => fun n1 n2 => if bool_decide (n1 ≤ n2) then 1 else 0
  end.

(** To evaluate a command, we need access to the current state of the program.
    We define the state of the program as a map from variable names to their
    values.  The [gmap] type is provided by stdpp and behaves similarly to maps
    in Java or dictionaries in Python.  *)

Definition state : Type := gmap string nat.




(** We have several options to define the semantics.  The most traditional
    choice in Rocq is to define a reduction relation on states; for example,
    [eval c s1 s2 : Prop] might say that the command [c] takes the state [s1] to
    the final state [s2].  Another possibility, which we follow here, is to
    write an _interpreter_ for commands as just another Rocq function.  Though
    less conventional, it allows us to use mostly features of Rocq we have
    already seen.

    Our interpreter will be a _monadic_ interpreter.  The [result T] type below
    represents a monadic computation that returns a final value of type [T]. It
    is given by several cases. (The final case will be needed to define the
    interpreter as a recursive function, as we'll see below.) *)

Inductive result (T : Type) :=
(* The computation ended successfully and returned the value [x]. *)
| Done (x : T)
(* The computation ended with an error *)
| Error
(* The computation has not ended yet. *)
| NotYet.

Arguments Done {T}.
Arguments Error {T}.
Arguments NotYet {T}.

(** The following declaration defines [bind] for the [result] monad.  If the
    computation returns successfully, we pass its result to the continuation of
    [bind]; otherwise, we simply propagate the abnormal result. The [MBind] type
    class is provided by stdpp and gives us a convenient syntax for writing
    monadic functions, similarly to Haskell's [do] notation. *)

Global Instance mbind_result : MBind result := fun A B f x =>
  match x with
  | Done a => f a
  | Error => Error
  | NotYet => NotYet
  end.




(** We are now ready to evaluate expressions.  Note that the computation returns
    error if some variable is not defined in the current state [s]. *)

Fixpoint eval_expr (e : expr) (s : state) : result nat :=
NotYet.



(** Evaluating an expression always yields a final result or an error. *)

Lemma eval_expr_notyet e s : eval_expr e s ≠ NotYet.
Proof. Admitted.


(** Ideally, to evaluate commands, we would write a function [eval_com] of type
    [com -> state -> result state].  Unfortunately, Rocq will not allow us to do
    so.  The problem is that it is possible to write imperative programs that do
    not terminate, whereas every function in Rocq must terminate on all
    inputs.

    To circumvent this issue, we employ a standard Rocq trick: we add a separate
    input [k] to the evaluation function, which counts the maximum number of
    iterations of [while] that we are allowed to perform. *)

Fixpoint iter {T} (f : (T -> result T) -> T -> result T) k x : result T :=
  f (fun x' =>
      match k with
      | 0 => NotYet
      | S k' => iter f k' x'
      end) x.

Fixpoint eval_com (c : com) (k : nat) (s : state) : result state :=
  match c with
  | Skip =>
      Done s

  | Seq c1 c2 =>
      s' ← eval_com c1 k s;
      eval_com c2 k s'

  | Assign x e =>
      n ← eval_expr e s;
      Done (<[x := n]> s)

  | If e c1 c2 =>
      NotYet
      


  | While e c =>
      NotYet
      


  end.

(** Now that we have defined the semantics of Imp, let us prove some results
    about it.  We start with some generic facts about [mbind] and [iter].  The
    [mbind] operation satisfies the following _monad laws_: *)

Lemma result_done_mbind :
  forall {T S} (x : T) (f : T -> result S), mbind f (Done x) = f x.
Proof. Admitted.


Lemma result_mbind_done : forall {T} (x : result T), mbind Done x = x.
Proof. Admitted.


Lemma result_mbind_assoc :
  forall {T S R} (g : S -> result R) (f : T -> result S) (x : result T),
    mbind g (mbind f x) =
    mbind (fun y : T => mbind g (f y)) x.
Proof. Admitted.


(** If [mbind] returns [Done], then the computation must have succeeded in both
    stages. *)

Lemma result_mbind_inv :
  forall {T S} {f : T -> result S} {x : result T} {y : S},
    mbind f x = Done y ->
    exists a, x = Done a /\ f a = Done y.
Proof. Admitted.


(** We define an ordering relation on [result] as follows.  We say that [x] is
    _less defined_ than [y], written [x ⊑ y], if they are equal or [x] is
    [NotYet]. This notation is provided by the [SqSubsetEq] class of stdpp, so
    we use the following instance declaration. *)

Global Instance result_sqsubseteq {T} : SqSubsetEq (result T) :=
  fun x y => x = NotYet \/ x = y.

Lemma result_sqsubseteq_NotYet :
  forall {T} (x : result T), NotYet ⊑ x.
Proof. intros T x. left. done. Qed.
Hint Resolve result_sqsubseteq_NotYet : core.

Global Instance result_sqsubseteq_refl :
  forall {T}, Reflexive (⊑@{result T}).
Proof. intros T x. right. done. Qed.

Global Instance result_sqsubseteq_trans :
  forall {T}, Transitive (⊑@{result T}).
Proof.
intros T x y z [H1 | H1] [H2 | H2]; rewrite H1; eauto; rewrite H2; eauto.
Qed.

(** The [⊑] relation is compatible with all the operations we have defined on
    [result]. For example: *)

Lemma result_bind_mono :
  forall {T S} (f g : T -> result S) (x y : result T),
    x ⊑ y ->
    (forall a, f a ⊑ g a) ->
    mbind f x ⊑ mbind g y.
Proof. Admitted.


(** (As an aside, this type of statement is common in frameworks for _relational
    reasoning_ about programs: being able to relate the final results of two
    programs.  It gives as a tool for relating these results in a compositional
    manner: the results are related provided that the inputs are related and
    that the continuations of [mbind] produce related results.) *)

(** The following result says that, if we increase the number of iterations to a
    computation, we obtain more and more defined results.  To make this result
    more general, we allow the iterated functions themselves to vary.  The case
    of a single function follows as a corollary. *)

Lemma iter_mono :
  forall {T} (f g : (T -> result T) -> T -> result T) n m x,
    (forall (f' g' : T -> result T),
      (forall x, f' x ⊑ g' x) ->
      (forall x, f f' x ⊑ g g' x)) ->
    n <= m ->
    iter f n x ⊑ iter g m x.
Proof.
intros T f g n m x f_g n_m.
induction m as [|m IH] in n, n_m, x |- *.
- assert (n = 0) as n0. { lia. }
  rewrite n0 /=. apply f_g. done.
- destruct n as [|n]; rewrite /=.
  + apply f_g. done.
  + apply f_g. intros a. apply IH. lia.
Qed.

(** Because [iter] behaves in this way, command evaluation also yields more
    results with more iterations. *)

Lemma eval_com_mono :
  forall n m c s, n <= m -> eval_com c n s ⊑ eval_com c m s.
Proof. Admitted.


(** So much for definedness.  We are now going to reason about program safety.
    Usually, obtaining an error as the result of evaluation indicates that there
    is a bug in our program.  For Imp, ruling out errors is conceptually simple:
    we just need to ensure that all the variables that the program uses are
    defined in its state. The following functions compute the variables that
    appear in expressions and commands.  We use the [gset] type of stdpp to
    represent finite sets. *)


Fixpoint vars_expr e : gset string :=
  match e with
  | Var x => singleton x
  | Num n => empty
  | Binop b e1 e2 => union (vars_expr e1) (vars_expr e2)
  end.

Fixpoint vars_com c : gset string :=
  match c with
  | Skip => empty
  | Seq c1 c2 => union (vars_com c1) (vars_com c2)
  | Assign x e => union (singleton x) (vars_expr e)
  | If e c1 c2 => union (vars_expr e) (union (vars_com c1) (vars_com c2))
  | While e c => union (vars_expr e) (vars_com c)
  end.

(** Here is what we hope to prove: *)

Lemma vars_com_not_error c k s :
  subseteq (vars_com c) (dom s) ->
  eval_com c k s <> Error.
Proof. Admitted.




