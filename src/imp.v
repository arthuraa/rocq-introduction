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

(* <skip /> *)

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

(* <skip /> *)

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
  | Leq => fun n1 n2 => if bool_decide (n1 <= n2) then 1 else 0
  end.

(** To evaluate a command, we need access to the current state of the program.
    We define the state of the program as a map from variable names to their
    values.  The [gmap] type is provided by stdpp and behaves similarly to maps
    in Java or dictionaries in Python.  *)

Definition state : Type := gmap string nat.

(* <skip /> *)

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

(* <skip /> *)

(** We are now ready to evaluate expressions.  Note that the computation returns
    error if some variable is not defined in the current state [s]. *)

Fixpoint eval_expr (e : expr) (s : state) : result nat :=
(* <exercise-only>NotYet.</exercise-only> *)
(* <solution> *)
  match e with
  | Var x => if s !! x is Some n then Done n else Error
  | Num n => Done n
  | Binop b e1 e2 =>
      n1 ← eval_expr e1 s;
      n2 ← eval_expr e2 s;
      Done (eval_binop b n1 n2)
  end.
(* </solution> *)

(** Evaluating an expression always yields a final result or an error. *)

Lemma eval_expr_notyet e s : eval_expr e s <> NotYet.
(* <admitted> *)
Proof.
induction e as [x|n|b e1 IH1 e2 IH2]; rewrite /=; eauto.
- destruct (s !! x); eauto.
- destruct (eval_expr e1) as [r1| | ]; try done.
  destruct (eval_expr e2) as [r2| | ]; done.
Qed.
(* </admitted> *)

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
      (* <exercise-only>NotYet</exercise-only> *)
      (* <solution> *)
      n ← eval_expr e s;
      if bool_decide (n = 0) then eval_com c2 k s
      else eval_com c1 k s
      (* </solution> *)

  | While e c =>
      (* <exercise-only>NotYet</exercise-only> *)
      (* <solution> *)
      let f eval_while s' : result state :=
        n ← eval_expr e s';
        if bool_decide (n = 0) then
          Done s'
        else
          s'' ← eval_com c k s';
          eval_while s''
      in
      iter f k s
      (* </solution> *)

  end.

(** Now that we have defined the semantics of Imp, let us prove some results
    about it.  We start with some generic facts about [mbind] and [iter].  The
    [mbind] operation satisfies the following _monad laws_: *)

Lemma result_done_mbind :
  forall {T S} (x : T) (f : T -> result S), mbind f (Done x) = f x.
(* <admitted> *)
Proof. eauto. Qed.
(* </admitted> *)

Lemma result_mbind_done : forall {T} (x : result T), mbind Done x = x.
(* <admitted> *)
Proof.
intros T []; eauto.
Qed.
(* </admitted> *)

Lemma result_mbind_assoc :
  forall {T S R} (g : S -> result R) (f : T -> result S) (x : result T),
    mbind g (mbind f x) =
    mbind (fun y : T => mbind g (f y)) x.
(* <admitted> *)
Proof. intros T S R f g []; eauto. Qed.
(* </admitted> *)

(** If [mbind] returns [Done], then the computation must have succeeded in both
    stages. *)

Lemma result_mbind_inv :
  forall {T S} {f : T -> result S} {x : result T} {y : S},
    mbind f x = Done y ->
    exists a, x = Done a /\ f a = Done y.
(* <admitted> *)
Proof. intros T S f [x | |] y; eauto; done. Qed.
(* </admitted> *)

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
(* <admitted> *)
Proof.
intros T S f g x y [H|H] f_g.
- rewrite H. eauto.
- rewrite H. destruct y as [a| |]; eauto.
Qed.
(* </admitted> *)

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
(* <admitted> *)
Proof.
intros n m c s n_m.
induction c as [|c1 IH1 c2 IH2|x e|e c1 IH1 c2 IH2|e c IH] in s |- *;
  rewrite /=; eauto.
- apply result_bind_mono; eauto.
- apply result_bind_mono; eauto.
  intros a. destruct (bool_decide _); eauto.
- apply iter_mono; eauto.
  intros f g f_g s'.
  apply result_bind_mono; eauto.
  intros a. destruct (bool_decide _); eauto.
  apply result_bind_mono; eauto.
Qed.
(* </admitted> *)

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
(* <admitted> *)
Proof.
induction c as [|c1 IH1 c2 IH2|x e|e c1 IH1 c2 IH2|e c IH] in s |- *;
  rewrite /=.
- done.
- intros Hdom.
  assert (subseteq (vars_com c1) (dom s) /\
          subseteq (vars_com c2) (dom s)) as [H1 H2].
  { rewrite -union_subseteq. done. }
  assert (IH1' := IH1 _ H1).
  destruct (eval_com c1 k s) as [s' | | ]; rewrite /=.
  + apply IH2. (* Stuck... *)
Abort.
(* </admitted> *)

(* <solution> *)
Lemma iter_ind :
  forall {T} (P : result T -> Prop) (f : (T -> result T) -> T -> result T),
    P NotYet ->
    (forall f',
      (forall x, P (Done x) -> P (f' x)) ->
      (forall x, P (Done x) -> P (f f' x))) ->
    forall x n, P (Done x) -> P (iter f n x).
Proof.
intros T P f H0 H1 x n Hx.
induction n as [|n IH] in x, Hx |- *; rewrite /=.
- apply H1; eauto.
- apply H1; eauto.
Qed.

Lemma vars_expr_not_error e s :
  subseteq (vars_expr e) (dom s) ->
  eval_expr e s <> Error.
Proof.
induction e as [x|n|b e1 IH1 e2 IH2]; rewrite /=; try done.
- rewrite singleton_subseteq_l elem_of_dom.
  intros [n E]. rewrite /= E. done.
- intros Hsub.
  rewrite union_subseteq in Hsub.
  destruct Hsub as [Hsub1 Hsub2].
  assert (IH1' := IH1 Hsub1). assert (IH2' := IH2 Hsub2).
  destruct (eval_expr e1 s) as [n1| |]; rewrite /=; try done.
  destruct (eval_expr e2 s) as [n2| |]; rewrite /=; try done.
Qed.

Definition safe_for (X : gset string) (f : state -> result state) : Prop :=
  forall s, subseteq X (dom s) ->
    match f s with
    | Done s' => subseteq (dom s) (dom s')
    | Error => False
    | NotYet => True
    end.

Lemma iter_safe :
  forall X F k,
    (forall f, safe_for X f -> safe_for X (F f)) ->
    safe_for X (iter F k).
Proof.
intros X F k HF.
induction k as [|k IH]; rewrite /=.
- apply HF. done.
- intros s X_s. apply HF; done.
Qed.

Lemma eval_com_safe c k : safe_for (vars_com c) (eval_com c k).
Proof.
induction c as [|c1 IH1 c2 IH2|x e|e c1 IH1 c2 IH2|e c IH];
  rewrite /=; eauto.
- intros s _; done.
- intros s. rewrite union_subseteq. intros [Hsub1 Hsub2].
  assert (E1 := IH1 s Hsub1).
  destruct (eval_com c1 k s) as [s1| |]; rewrite /=; try done.
  assert (subseteq (vars_com c2) (dom s1)) as Hsub2'.
  { intros ??; eauto. }
  assert (E2 := IH2 s1 Hsub2').
  destruct (eval_com c2 k s1) as [s2| |]; rewrite /=; try done.
  intros ??; eauto.
- intros s. rewrite union_subseteq. intros [x_s Hsub].
  assert (Hsub' := vars_expr_not_error _ _ Hsub).
  destruct eval_expr as [n| |]; rewrite /=; try done.
  rewrite dom_insert_L. intros ?. rewrite elem_of_union. eauto.
- intros s. rewrite !union_subseteq. intros (Hsube & Hsub1 & Hsub2).
  assert (Hsube' := vars_expr_not_error _ _ Hsube).
  destruct eval_expr as [n| |]; rewrite /=; try done.
  destruct bool_decide; eauto.
  + apply IH2. done.
  + apply IH1. done.
- apply iter_safe. intros f f_safe s Hsub.
  assert (Hsub' := Hsub).
  rewrite union_subseteq in Hsub'. destruct Hsub' as [Hsube Hsubc].
  assert (He := vars_expr_not_error _ _ Hsube).
  destruct (eval_expr e s) as [n| |]; rewrite /=; try done.
  destruct bool_decide; rewrite /=; try done.
  assert (IH' := IH s Hsubc).
  destruct (eval_com c k s) as [s1| |]; rewrite /= in IH' *; try done.
  assert (subseteq (vars_expr e ∪ vars_com c) (dom s1)) as Hsub'.
  { intros ??; eauto. }
  assert (Hf := f_safe _ Hsub'). destruct (f s1) as [s2| |]; eauto.
  intros ??; eauto.
Qed.

Lemma vars_com_subseteq c s k s' :
  eval_com c k s = Done s' ->
  subseteq (dom s) (dom s').
Proof.
pose (P (s : state) (r : result state) :=
  match r with
  | Done s' => subseteq (dom s) (dom s')
  | _ => True
  end
).
assert (P s (eval_com c k s)); last first.
{ intros E. rewrite E in H. done. }
clear s'.
induction c as [|c1 IH1 c2 IH2|x e|e c1 IH1 c2 IH2|e c IH] in s |- *;
  rewrite /=.
- congruence.
- assert (E1 := IH1 s).
  destruct (eval_com c1 k s) as [s1| |]; rewrite /=; try done.
  assert (E2 := IH2 s1).
  destruct (eval_com c2 k s1) as [s2| |]; rewrite /=; try done.
  trans (dom s1); eauto.
- destruct eval_expr; rewrite /=; try done.
  rewrite dom_insert. intros y. rewrite elem_of_union. eauto.
- destruct eval_expr; rewrite /=; try done.
  destruct bool_decide; eauto.
- apply (iter_ind (P s)); rewrite /=; try done.
  rewrite /=. intros ev_while Hev_while s1 Hs1.
  destruct (eval_expr e s1) as [n1| |]; rewrite /=; try done.
  destruct bool_decide; rewrite /=; try done.
  assert (IH' := IH s1).
  destruct (eval_com c k s1) as [s2| |]; rewrite /= in IH' *; try done.
  apply Hev_while. trans (dom s1); done.
Qed.

Lemma vars_com_not_error c k s :
  subseteq (vars_com c) (dom s) ->
  eval_com c k s <> Error.
Proof.
intros Hsub Herr.
assert (contra := eval_com_safe _ k s Hsub).
rewrite Herr in contra. done.
Qed.
(* </solution> *)

(** Exercise: Improving safety

    In our semantics of Imp, a program does not fail if it writes to an
    undefined variable: that variable simply becomes defined.  Strengthen the
    safety result so that written variables do not need to be included.

*)

Fixpoint vars_com_read c : gset string :=
  match c with
  | Skip => empty
  | Seq c1 c2 => union (vars_com_read c1) (vars_com_read c2)
  | Assign _ e => vars_expr e
  | If e c1 c2 => union (vars_expr e)
                    (union (vars_com_read c1) (vars_com_read c2))
  | While e c => union (vars_expr e) (vars_com_read c)
  end.

(* <solution> *)
Lemma eval_com_safe' c k : safe_for (vars_com_read c) (eval_com c k).
Proof.
induction c as [|c1 IH1 c2 IH2|x e|e c1 IH1 c2 IH2|e c IH];
  rewrite /=; eauto.
- intros s _; done.
- intros s. rewrite union_subseteq. intros [Hsub1 Hsub2].
  assert (E1 := IH1 s Hsub1).
  destruct (eval_com c1 k s) as [s1| |]; rewrite /=; try done.
  assert (subseteq (vars_com_read c2) (dom s1)) as Hsub2'.
  { intros ??; eauto. }
  assert (E2 := IH2 s1 Hsub2').
  destruct (eval_com c2 k s1) as [s2| |]; rewrite /=; try done.
  intros ??; eauto.
- intros s Hsub.
  assert (Hsub' := vars_expr_not_error _ _ Hsub).
  destruct eval_expr as [n| |]; rewrite /=; try done.
  rewrite dom_insert_L. intros ?. rewrite elem_of_union. eauto.
- intros s. rewrite !union_subseteq. intros (Hsube & Hsub1 & Hsub2).
  assert (Hsube' := vars_expr_not_error _ _ Hsube).
  destruct eval_expr as [n| |]; rewrite /=; try done.
  destruct bool_decide; eauto.
  + apply IH2. done.
  + apply IH1. done.
- apply iter_safe. intros f f_safe s Hsub.
  assert (Hsub' := Hsub).
  rewrite union_subseteq in Hsub'. destruct Hsub' as [Hsube Hsubc].
  assert (He := vars_expr_not_error _ _ Hsube).
  destruct (eval_expr e s) as [n| |]; rewrite /=; try done.
  destruct bool_decide; rewrite /=; try done.
  assert (IH' := IH s Hsubc).
  destruct (eval_com c k s) as [s1| |]; rewrite /= in IH' *; try done.
  assert (subseteq (vars_expr e ∪ vars_com_read c) (dom s1)) as Hsub'.
  { intros ??; eauto. }
  assert (Hf := f_safe _ Hsub'). destruct (f s1) as [s2| |]; eauto.
  intros ??; eauto.
Qed.
(* </solution> *)

Lemma vars_com_not_error' c k s :
  subseteq (vars_com_read c) (dom s) ->
  eval_com c k s <> Error.
(* <admitted> *)
Proof.
intros Hsub Herr.
assert (contra := eval_com_safe' _ k s Hsub).
rewrite Herr in contra. done.
Qed.
(* </admitted> *)

(** Exercise: Further Improving Safety

    We take that result even further. If we write to a variable, other commands
    will be able to read it later on.  Define a recursive function [safe_com X
    c] that checks whether [c] is safe to run when only the variables in [X] are
    defined. The function should return an [option (gset string)]: [Some X']
    indicates that the command is safe and guaranteed to leave every variable in
    [X'] defined; [None] indicates that the program is not known to be safe.

    Prove that, if a program is safe according to this definition, then it does
    not return an error. *)

(* <solution> *)
Fixpoint safe_com (X : gset string) c : option (gset string) :=
  match c with
  | Skip => Some X
  | Seq c1 c2 =>
      X1 ← safe_com X c1;
      safe_com X1 c2
  | Assign x e =>
      if bool_decide (subseteq X (vars_expr e)) then
        Some (union (singleton x) X)
      else None
  | If e c1 c2 =>
      if bool_decide (subseteq X (vars_expr e)) then
        X1 ← safe_com X c1;
        X2 ← safe_com X c2;
        Some (intersection X1 X2)
      else None
  | While e c =>
      if bool_decide (subseteq X (vars_expr e)) then
        (* There might be zero iterations, so we cannot use the variables
           written by [c] *)
        _ ← safe_com X c; Some X
      else None
  end.
(* </solution> *)
