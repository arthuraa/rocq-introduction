(** We are now going to use Rocq to define the semantics of a simple imperative
    programming language.  The language only has arithmetic, global variables,
    and control flow operations (if and while).  We leave out complex data
    types, function calls, objects, etc.

    We begin by defining the abstract syntax of the language.  The language
    comprises binary operations, arithmetic expressions and commands, given by
    the following Rocq data types.  (We use strings to represent variable
    names.) *)

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
    operation to two numbers. *)

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
  match e with
  | Var x => if s !! x is Some n then Done n else Error
  | Num n => Done n
  | Binop b e1 e2 =>
      n1 ← eval_expr e1 s;
      n2 ← eval_expr e2 s;
      Done (eval_binop b n1 n2)
  end.

(** Ideally, to evaluate commands, we would write a function [eval_com] of type
    [com -> state -> result state].  Unfortunately, Rocq will not allow us to do
    so.  The problem is that it is possible to write imperative programs that do
    not terminate, whereas every function in Rocq must terminate on all
    inputs.

    To circumvent this issue, we employ a standard Rocq trick: we add a separate
    input [k] to the evaluation function, which counts the maximum number of
    iterations of [while] that we are allowed to perform. *)

Fixpoint iter {T} (f : (T -> result T) -> T -> result T) (x : T) (k : nat) : result T :=
  f (fun x' =>
      match k with
      | 0 => NotYet
      | S k' => iter f x' k'
      end) x.

Fixpoint eval_com (c : com) (s : state) (k : nat) : result state :=
  match c with
  | Skip =>
      Done s

  | Seq c1 c2 =>
      s' ← eval_com c1 s k;
      eval_com c2 s' k

  | Assign x e =>
      n ← eval_expr e s;
      Done (<[x := n]> s)

  | If e c1 c2 =>
      n ← eval_expr e s;
      if bool_decide (n = 0) then eval_com c2 s k
      else eval_com c1 s k

  | While e c =>
      let f eval_while s' : result state :=
        n ← eval_expr e s';
        if bool_decide (n = 0) then
          Done s'
        else
          s'' ← eval_com c s' k;
          eval_while s''
      in
      iter f s k

  end.
