From stdpp Require Import base gmap ssreflect strings.
From introduction Require Import imp.

(** With the semantics of Imp in place, we can define a _constant folding_
    optimization that removes intermediate computations that are known to be
    constant.  Let us begin with expressions.  Given a binary operation [b], we
    define a function that computes an optimized version of [b] with constant
    folding. If no optimization applies, we keep the operation as is.

    For example, we optimize addition as follows. We combine literals by adding
    them together.  If one of the terms is zero, we keep the other one, even if
    it is not constant -- after all, adding zero should not change anything.  *)

Definition cf_add e1 e2 :=
  match e1, e2 with
  | Num n1, Num n2 => Num (n1 + n2)
  | Num 0, e
  | e, Num 0 => e
  | _, _ => Binop Add e1 e2
  end.

(** The key property of [cf_add] is that it does not change the result of
    evaluation. *)

Lemma cf_add_correct : forall e1 e2 s,
  eval_expr (cf_add e1 e2) s
  = eval_expr (Binop Add e1 e2) s.
Proof. Admitted.





(** Let's try another operation: multiplication. *)

Definition cf_mul e1 e2 :=
  match e1, e2 with
  | Num n1, Num n2 => Num (n1 * n2)
  | Num 0, _
  | _, Num 0 => Num 0
  | Num 1, e
  | e, Num 1 => e
  | _, _ => Binop Mul e1 e2
  end.




Lemma cf_mul_correct : forall e1 e2 s,
  eval_expr (cf_mul e1 e2) s
  = eval_expr (Binop Mul e1 e2) s.
Proof.
intros e1 e2 s.
destruct e1 as [x1|n1|b1 e11 e12];
destruct e2 as [x2|n2|b2 e21 e22];
rewrite /=; eauto.
- (* e1 = Var x1; e2 = Num n2 *)
  destruct n2 as [|n2]; rewrite /=; eauto.
  + (* n2 = 0 *)
    destruct (s !! x1) as [n1|]; rewrite /=; eauto.
    (* s !! x1 = Some n1 |- Done 0 = Error *)
    (* Oops... *)
Abort.

(** It turns out that the goal is not provable! What went wrong? If the
    expression is of the form [e1 * 0], the optimizer replaces it with [0]. The
    issue is that evaluating [e1] can return an error, whereas evaluating just
    [0] cannot.  Therefore, optimization can turn an errorneous execution into a
    successful one, thus modifying the behavior of the program.

    What can we do? We have a few possibilities:

    1. Include a side condition to describe when the equation holds. We might:

       a. Use a _static_ side condition that can be evaluated during compilation
          or linking. For example, we might require that all required variables
          are defined in the initial memory (cf. last lecture).

       b. Use a _dynamic_ side condition that depends on the particular behavior
          of the program on the state [s]. For example, we might not require
          anything if the original program yields an error on [s].

    2. Change the optimization function to make the theorem true.

    Option (2) is OK, but limiting: it rules out some optimizations that we
    would like to do.  Option (1.a) is popular with strongly typed languages,
    where we can be analyze the required side conditions ahead of time.  Option
    (1.b) is popular with weakly typed or unsafe languages like C, where it is
    just too difficult to rule out the problematic cases statically.  For
    example, if our language had dynamically allocated arrays of variable size,
    it would be very difficult to guarantee ahead of time that every memory
    access is safe.  We are going to go with option (1.b), stated in a slightly
    more convenient form.  The relation [improves r1 r2] says that the behavior
    of the computation [r1] improves the behavior of the computation [r2], in
    the sense that it exhibits fewer errors. *)

Definition improves {T} (x y : result T) : Prop :=
  y = Error \/ x = y.

Lemma improves_error {T} (x : result T) : improves x Error.
Proof. by left. Qed.

Lemma improves_refl {T} (x : result T) : improves x x.
Proof. by right. Qed.

Hint Resolve improves_error improves_refl : core.

Lemma improves_trans {T} (x y z : result T) :
  improves x y -> improves y z -> improves x z.
Proof. by move=> H1 [->|<-]. Qed.

(** This definition makes [Error] a form of _undefined behavior_. In unsafe
    languages like C, the language implementation is allowed to do anything with
    the generated code if the source code exhibits undefined behavior, such as
    accessing undefined memory.  Option (1.a) interprets errors as _unobservable
    behavior_: they are guaranteed not to occur during execution.  Option (2)
    interprets errors as undesirable, but legitimate behaviors.  For example, a
    dynamic type error in a safe language such as JavaScript leads to a run-time
    exception that can be caught and handled, leading to a non-erroneous
    outcome. These different interpretations lead to trade-offs in language
    design involving expressiveness, performance and safety.

    (Notice that this definition forces us to preserve [NotYet], and, thus,
    preserve non-terminatation. We could have adopted a more lax approach where
    non-termination can be improved or where timing behavior is not preserved,
    but we will not pursue this idea here.)

    We will follow the steps of the last lecture and prove some lemmas for
    reasoning about [improves] compositionally.  The second *)

Lemma improves_bind {T S} (x y : result T) (f g : T -> result S) :
  improves x y ->
  (∀ r, improves (f r) (g r)) ->
  improves (mbind f x) (mbind g y).
Proof.
intros [-> | ->]; eauto; intros f_g.
destruct y as [r| |]; eauto.
Qed.

Lemma improves_eval_expr {T} (x : result T) e s f :
  (∀ n, improves x (f n)) ->
  improves x (mbind f (eval_expr e s)).
Proof.
assert (H := eval_expr_notyet e s).
destruct eval_expr; rewrite /=; done.
Qed.

(** Let's now prove that [cf_mul] is correct. *)

Lemma cf_mul_correct : forall e1 e2 s,
  improves
    (eval_expr (cf_mul e1 e2) s)
    (eval_expr (Binop Mul e1 e2) s).
Proof. Admitted.

Reset cf_mul_correct.

(** We could complete this proof, but it is getting tedious. One reason is the
    branching structure.  The definition of [cf_mul] has six branches; however,
    Rocq does not have a primitive notion of complex, nested pattern matching.
    Such match expressions are compiled to a chain of nested matches, which can
    lead to more nested branches than we might realize.  We can see this in the
    above proof: to analyze the possible shapes of [e1] and [e2], we need to
    look at nine subcases, and some of them require further case analysis.

    One possible solution is to use proof automation to avoid considering all
    these subcases explicitlty.  We are going to follow a lighterweight, more
    direct approach: we'll define a custom case analysis principle for [cf_mul]
    that follows the structure of the definition.  Thus, we'll only have to
    consider the branches that are given in the definition of [cf_mul]
    itself. *)

Definition cf_mul_spec (e1 e2 e : expr) : Prop :=
  (exists n1 n2, e1 = Num n1 /\ e2 = Num n2 /\ e = Num (n1 * n2)) \/
  (e1 = Num 0 /\ e = Num 0) \/
  (e2 = Num 0 /\ e = Num 0) \/
  (e1 = Num 1 /\ e2 = e) \/
  (e1 = e /\ e2 = Num 1) \/
  (e = Binop Mul e1 e2).

Lemma cf_mulP e1 e2 : cf_mul_spec e1 e2 (cf_mul e1 e2).
Proof.
rewrite /cf_mul_spec.
destruct e1 as [x1|[|[|n1]]|b1 e11 e12]; eauto;
destruct e2 as [x2|[|[|n2]]|b2 e21 e22]; eauto 10.
Qed.

(** The lemma [cf_mulP] tells us how the result [cf_mul e1 e2] depends on the
    expressions [e1] and [e2], depending on which branch of the definition was
    used.  This allows us to improve our proof as follows. *)

Lemma cf_mul_correct : forall e1 e2 s,
  improves
    (eval_expr (cf_mul e1 e2) s)
    (eval_expr (Binop Mul e1 e2) s).
Proof. Admitted.


(** We are going to follow a similar approach for the remaining optimization
    steps.  Here is how we can optimize [Sub] and [Leq].  Notice that, just like
    the case for multiplication, some of the branches simply ignore what the
    other expression is doing.  (Remember that, since we are working with
    natural numbers, subtraction is weird: it is truncated at 0.) *)

Definition cf_sub e1 e2 :=
  match e1, e2 with
  | Num n1, Num n2 => Num (n1 - n2)
  | Num 0, _ => Num 0
  | _, Num 0 => e1
  | _, _ => Binop Sub e1 e2
  end.

Definition cf_leq e1 e2 :=
  match e1, e2 with
  | Num n1, Num n2 => Num (eval_binop Leq n1 n2)
  | Num 0, _ => Num 1
  | _, _ => Binop Leq e1 e2
  end.

Definition cf_binop b :=
  match b with
  | Add => cf_add
  | Mul => cf_mul
  | Sub => cf_sub
  | Leq => cf_leq
  end.

Definition cf_sub_spec (e1 e2 e : expr) : Prop :=
(* Replace this *) False.



Lemma cf_subP e1 e2 : cf_sub_spec e1 e2 (cf_sub e1 e2).
(*  *)
Proof. Admitted.

Lemma cf_sub_correct : forall e1 e2 s,
  improves (eval_expr (cf_sub e1 e2) s)
    (eval_expr (Binop Sub e1 e2) s).
Proof. Admitted.


Definition cf_leq_spec (e1 e2 e : expr) : Prop :=
(* Replace this *) False.



Lemma cf_leqP e1 e2 : cf_leq_spec e1 e2 (cf_leq e1 e2).
(*  *)
Proof. Admitted.

Lemma cf_leq_correct : forall e1 e2 s,
  improves (eval_expr (cf_leq e1 e2) s)
    (eval_expr (Binop Leq e1 e2) s).
Proof. Admitted.


Lemma cf_binop_correct : forall b e1 e2 s,
  improves (eval_expr (cf_binop b e1 e2) s)
    (eval_expr (Binop b e1 e2) s).
Proof.
intros b e1 e2 s. destruct b.
- rewrite cf_add_correct. done.
- apply cf_mul_correct.
- apply cf_sub_correct.
- apply cf_leq_correct.
Qed.

(** Now that we can simplify a single binary operation, we can compose such
    optimizations to handle entire expressions. *)

Fixpoint cf_expr (e : expr) : expr :=
(* Replace this *) Num 0.



Lemma cf_expr_correct : forall e s,
  improves (eval_expr (cf_expr e) s) (eval_expr e s).
Proof. Admitted.

Hint Resolve cf_expr_correct : core.

(** We can follow the same approach to optimize commands.  We define what it
    means to optimize each syntactic form, prove the correctness of each
    optimization step, and then compose everything. *)

Definition cf_seq (c1 c2 : com) : com :=
(* Replace this *) Skip.



Definition cf_assign (x : string) (e : expr) : com :=
(* Replace this *) Skip.



Definition cf_if (e : expr) (c1 c2 : com) : com :=
(* Replace this *) Skip.



Definition cf_while (e : expr) (c : com) : com :=
(* Replace this *) Skip.



Fixpoint cf_com c :=
  match c with
  | Skip => Skip
  | Seq c1 c2 => cf_seq (cf_com c1) (cf_com c2)
  | Assign x e => cf_assign x (cf_expr e)
  | If e c1 c2 => cf_if (cf_expr e) (cf_com c1) (cf_com c2)
  | While e c => cf_while (cf_expr e) (cf_com c)
  end.

(** We use the same trick as before to prove the correctness of each
    optimization. We prove a specification to allow us to structure the proof of
    correctness following the definition of each optimization. *)

Definition cf_seq_spec (c1 c2 c : com) : Prop :=
(* Replace this *) False.



Lemma cf_seqP c1 c2 : cf_seq_spec c1 c2 (cf_seq c1 c2).
(*  *)
Proof. Admitted.

Definition cf_assign_spec (x : string) (e : expr) (c : com) : Prop :=
(* Replace this *) False.



Lemma cf_assignP x e : cf_assign_spec x e (cf_assign x e).
(*  *)
Proof. Admitted.

Definition cf_if_spec (e : expr) (c1 c2 c : com) : Prop :=
(* Replace this *) False.



Lemma cf_ifP e c1 c2 : cf_if_spec e c1 c2 (cf_if e c1 c2).
(*  *)
Proof. Admitted.

Definition cf_while_spec (e : expr) (c c' : com) : Prop :=
(* Replace this *) False.



Lemma cf_whileP e c : cf_while_spec e c (cf_while e c).
(*  *)
Proof. Admitted.

Lemma cf_seq_correct : forall c1 c2 k s,
  improves (eval_com (cf_seq c1 c2) k s) (eval_com (Seq c1 c2) k s).
Proof. Admitted.


Lemma cf_assign_correct : forall x e k s,
  improves (eval_com (cf_assign x e) k s) (eval_com (Assign x e) k s).
Proof. Admitted.


Lemma cf_if_correct : forall e c1 c2 k s,
  improves (eval_com (cf_if e c1 c2) k s) (eval_com (If e c1 c2) k s).
Proof. Admitted.


Lemma cf_while_correct : forall e c k s,
  improves (eval_com (cf_while e c) k s) (eval_com (While e c) k s).
Proof. Admitted.


(** We conclude by chaining together all of these local correctness results.  We
    use the following auxiliary lemma, which guarantees that iteration is
    compatible with improvement. *)

Lemma iter_improves {T} (f g : (T -> result T) -> T -> result T) x k :
  (∀ f' g', (∀ x, improves (f' x) (g' x)) ->
             ∀ x, improves (f f' x) (g g' x)) ->
  improves (iter f k x) (iter g k x).
Proof.
intros H.
induction k as [|k IH] in x |- *; rewrite /=; apply H; eauto.
Qed.

Lemma cf_com_correct : forall c k s,
  improves (eval_com (cf_com c) k s) (eval_com c k s).
Proof. Admitted.


(** Exercise: Define a _constant propagation_ pass, which inlines the values of
    variables when they are known to be constant.  One possibility is to
    parameterize the optimization functions by a value [m : gmap string nat]
    which maps each variable to a natural number that is guaranteed to be its
    value during execution.  Prove that your definition is correct. *)
