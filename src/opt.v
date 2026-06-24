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
(* <admitted> *)
Proof.
intros e1 e2 s.
destruct e1 as [x1|[|n1]|b1 e11 e12];
destruct e2 as [x2|[|n2]|b2 e21 e22];
rewrite /=; eauto.
- destruct (s !! x1) as [n1|]; rewrite /=; eauto.
- destruct (s !! x2) as [n2|]; rewrite /=; eauto.
- destruct (eval_expr e21 s) as [n21| |]; rewrite /=; eauto.
  destruct (eval_expr e22 s) as [n22| |]; rewrite /=; eauto.
- destruct (eval_expr e11 s) as [n11| |]; rewrite /=; eauto.
  destruct (eval_expr e12 s) as [n12| |]; rewrite /=; eauto.
Qed.
(* </admitted> *)

(* <skip /> *)

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

(* <skip /> *)

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
(* <admitted> *)
Proof.
rewrite /=.
intros e1 e2 s.
destruct e1 as [x1|n1|b1 e11 e12];
destruct e2 as [x2|n2|b2 e21 e22];
rewrite /=; eauto.
- (* e1 = Var x1; e2 = Num n2 *)
  destruct n2 as [|[|n2]]; rewrite /=; eauto.
  + (* n2 = 0 *)
    destruct (s !! x1) as [n1|]; rewrite /=; eauto.
    rewrite Nat.mul_0_r. done.
  + (* n2 = 1 *)
    destruct (s !! x1) as [n1|]; rewrite /=; eauto.
    rewrite Nat.mul_1_r. done.
- (* e1 = Num n1; e2 = Var x2 *)
  destruct n1 as [|[|n1]]; rewrite /=; eauto.
  + (* n1 = 0 *)
    destruct (s !! x2) as [n2|]; rewrite /=; eauto.
  + (* n1 = 1 *)
    destruct (s !! x2) as [n2|]; rewrite /=; eauto.
    rewrite Nat.add_0_r. done.
- (* e1 = Num n1; e2 = Num n2
     boring... *)
Abort.
(* </admitted> *)
(* <exercise-only>Reset cf_mul_correct.</exercise-only> *)

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
(* <admitted> *)
Proof.
intros e1 e2 s.
destruct (cf_mulP e1 e2) as [H|[H|[H|[H|[H|H]]]]].
- destruct H as (n1 & n2 & -> & -> & ->). done.
- destruct H as (-> & ->). rewrite /=.
  apply improves_eval_expr. done.
- destruct H as (-> & ->). rewrite /=.
  apply improves_eval_expr. intros n. rewrite Nat.mul_0_r. done.
- destruct H as (-> & <-). rewrite /=.
  rewrite -{1}[eval_expr e2 s]result_mbind_done.
  apply improves_bind; eauto; intros n; rewrite Nat.add_0_r.
  done.
- destruct H as (<- & ->).
  rewrite -{1}[eval_expr e1 s]result_mbind_done.
  apply improves_bind; eauto; intros n. rewrite /= Nat.mul_1_r. done.
- rewrite H. done.
Qed.
(* </admitted> *)

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
(* <exercise-only>(* Replace this *) False.</exercise-only> *)
(* <solution> *)
  (exists n1 n2, e1 = Num n1 /\ e2 = Num n2 /\ e = Num (n1 - n2)) \/
  (e1 = Num 0 /\ e = Num 0) \/
  (e1 = e /\ e2 = Num 0) \/
  (e = Binop Sub e1 e2).
(* </solution> *)

Lemma cf_subP e1 e2 : cf_sub_spec e1 e2 (cf_sub e1 e2).
(* <commented> *)
Proof.
rewrite /cf_sub_spec.
destruct e1 as [x1|[|n1]|b1 e11 e12]; eauto;
destruct e2 as [x2|[|n2]|b2 e21 e22]; eauto 10.
Qed.
(* </commented> *)
(* <exercise-only>Proof. Admitted.</exercise-only> *)

Lemma cf_sub_correct : forall e1 e2 s,
  improves (eval_expr (cf_sub e1 e2) s)
    (eval_expr (Binop Sub e1 e2) s).
(* <admitted> *)
Proof.
intros e1 e2 s. rewrite /=.
destruct (cf_subP e1 e2) as [H|[H|[H|H]]].
- destruct H as (n1 & n2 & -> & -> & ->). done.
- destruct H as (-> & ->). rewrite /=.
  by apply: improves_eval_expr => ?; rewrite Nat.sub_0_l.
- destruct H as (<- & ->). rewrite /=.
  rewrite -{1}[eval_expr e1 s]result_mbind_done.
  by apply: improves_bind => // n; rewrite Nat.sub_0_r.
- rewrite H. done.
Qed.
(* </admitted> *)

Definition cf_leq_spec (e1 e2 e : expr) : Prop :=
(* <exercise-only>(* Replace this *) False.</exercise-only> *)
(* <solution> *)
  (exists n1 n2, e1 = Num n1 /\ e2 = Num n2 /\
                 e = Num (eval_binop Leq n1 n2)) \/
  (e1 = Num 0 /\ e = Num 1) \/
  (e = Binop Leq e1 e2).
(* </solution> *)

Lemma cf_leqP e1 e2 : cf_leq_spec e1 e2 (cf_leq e1 e2).
(* <commented> *)
Proof.
rewrite /cf_leq_spec.
destruct e1 as [x1|[|n1]|b1 e11 e12]; eauto;
destruct e2 as [x2|[|n2]|b2 e21 e22]; eauto 10.
Qed.
(* </commented> *)
(* <exercise-only>Proof. Admitted.</exercise-only> *)

Lemma cf_leq_correct : forall e1 e2 s,
  improves (eval_expr (cf_leq e1 e2) s)
    (eval_expr (Binop Leq e1 e2) s).
(* <admitted> *)
Proof.
intros e1 e2 s. rewrite /=.
destruct (cf_leqP e1 e2) as [H|[H|H]].
- destruct H as (n1 & n2 & -> & -> & ->). done.
- destruct H as (-> & ->). rewrite /=.
  by apply: improves_eval_expr.
- by rewrite H.
Qed.
(* </admitted> *)

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
(* <exercise-only>(* Replace this *) Num 0.</exercise-only> *)
(* <solution> *)
  match e with
  | Binop b e1 e2 => cf_binop b (cf_expr e1) (cf_expr e2)
  | _ => e
  end.
(* </solution> *)

Lemma cf_expr_correct : forall e s,
  improves (eval_expr (cf_expr e) s) (eval_expr e s).
(* <admitted> *)
Proof.
intros e s. induction e as [x|n'|b e1 IH1 e2 IH2]; eauto.
eapply improves_trans. { eapply cf_binop_correct. }
rewrite /=.
apply improves_bind; eauto. intros n1.
apply improves_bind; eauto.
Qed.
(* </admitted> *)
Hint Resolve cf_expr_correct : core.

(** We can follow the same approach to optimize commands.  We define what it
    means to optimize each syntactic form, prove the correctness of each
    optimization step, and then compose everything. *)

Definition cf_seq (c1 c2 : com) : com :=
(* <exercise-only>(* Replace this *) Skip.</exercise-only> *)
(* <solution> *)
  match c1, c2 with
  | Skip, c
  | c, Skip => c
  | _, _ => Seq c1 c2
  end.
(* </solution> *)

Definition cf_assign (x : string) (e : expr) : com :=
(* <exercise-only>(* Replace this *) Skip.</exercise-only> *)
(* <solution> *)
  match e with
  | Var y => if bool_decide (x = y) then Skip else Assign x e
  | _ => Assign x e
  end.
(* </solution> *)

Definition cf_if (e : expr) (c1 c2 : com) : com :=
(* <exercise-only>(* Replace this *) Skip.</exercise-only> *)
(* <solution> *)
  if bool_decide (c1 = c2) then c1
  else match e with
       | Num n => if bool_decide (n = 0) then c2 else c1
       | _ => If e c1 c2
       end.
(* </solution> *)

Definition cf_while (e : expr) (c : com) : com :=
(* <exercise-only>(* Replace this *) Skip.</exercise-only> *)
(* <solution> *)
  if bool_decide (e = Num 0) then Skip else While e c.
(* </solution> *)

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
(* <exercise-only>(* Replace this *) False.</exercise-only> *)
(* <solution> *)
  (c1 = Skip /\ c2 = c) \/
  (c1 = c /\ c2 = Skip) \/
  (c = Seq c1 c2).
(* </solution> *)

Lemma cf_seqP c1 c2 : cf_seq_spec c1 c2 (cf_seq c1 c2).
(* <commented> *)
Proof.
rewrite /cf_seq_spec.
destruct c1; destruct c2; eauto 10.
Qed.
(* </commented> *)
(* <exercise-only>Proof. Admitted.</exercise-only> *)

Definition cf_assign_spec (x : string) (e : expr) (c : com) : Prop :=
(* <exercise-only>(* Replace this *) False.</exercise-only> *)
(* <solution> *)
  (e = Var x /\ c = Skip) \/
  (c = Assign x e).
(* </solution> *)

Lemma cf_assignP x e : cf_assign_spec x e (cf_assign x e).
(* <commented> *)
Proof.
rewrite /cf_assign_spec /cf_assign.
destruct e as [y|n|b e1 e2]; eauto 10;
rewrite /= bool_decide_decide.
destruct (decide (x = y)) as [->|?]; eauto.
Qed.
(* </commented> *)
(* <exercise-only>Proof. Admitted.</exercise-only> *)

Definition cf_if_spec (e : expr) (c1 c2 c : com) : Prop :=
(* <exercise-only>(* Replace this *) False.</exercise-only> *)
(* <solution> *)
  (c1 = c2 /\ c2 = c) \/
  (e = Num 0 /\ c2 = c) \/
  (exists n, e = Num n /\ n <> 0 /\ c1 = c) \/
  (c = If e c1 c2).
(* </solution> *)

Lemma cf_ifP e c1 c2 : cf_if_spec e c1 c2 (cf_if e c1 c2).
(* <commented> *)
Proof.
rewrite /cf_if_spec /cf_if.
destruct (bool_decide_reflect (c1 = c2)) as [<-|_]; eauto 10.
destruct e as [x|[|n]|???]; eauto 10.
Qed.
(* </commented> *)
(* <exercise-only>Proof. Admitted.</exercise-only> *)

Definition cf_while_spec (e : expr) (c c' : com) : Prop :=
(* <exercise-only>(* Replace this *) False.</exercise-only> *)
(* <solution> *)
  (e = Num 0 /\ c' = Skip) \/
  c' = While e c.
(* </solution> *)

Lemma cf_whileP e c : cf_while_spec e c (cf_while e c).
(* <commented> *)
Proof.
rewrite /cf_while /cf_while_spec.
destruct bool_decide eqn:E; eauto.
rewrite bool_decide_eq_true in E. rewrite E /=; eauto.
Qed.
(* </commented> *)
(* <exercise-only>Proof. Admitted.</exercise-only> *)

Lemma cf_seq_correct : forall c1 c2 k s,
  improves (eval_com (cf_seq c1 c2) k s) (eval_com (Seq c1 c2) k s).
(* <admitted> *)
Proof.
intros c1 c2 k s.
destruct (cf_seqP c1 c2) as [H|[H|H]]; rewrite /=.
- destruct H as (-> & <-). done.
- destruct H as (<- & ->). rewrite result_mbind_done. done.
- rewrite H. done.
Qed.
(* </admitted> *)

Lemma cf_assign_correct : forall x e k s,
  improves (eval_com (cf_assign x e) k s) (eval_com (Assign x e) k s).
(* <admitted> *)
Proof.
intros x e k s. destruct (cf_assignP x e) as [H|H].
- destruct H as (-> & ->). rewrite /=.
  destruct (s !! x) as [n|] eqn:E; rewrite /=; eauto.
  rewrite insert_id; done.
- rewrite H. done.
Qed.
(* </admitted> *)

Lemma cf_if_correct : forall e c1 c2 k s,
  improves (eval_com (cf_if e c1 c2) k s) (eval_com (If e c1 c2) k s).
(* <admitted> *)
Proof.
intros e c1 c2 k s.
destruct (cf_ifP e c1 c2) as [H|[H|[H|H]]]; rewrite /=.
- destruct H as (<- & <-).
  apply improves_eval_expr. intros n.
  destruct bool_decide; done.
- destruct H as (-> & <-). done.
- destruct H as (n & -> & n0 & <-). rewrite /=.
  rewrite bool_decide_eq_false_2; done.
- rewrite H. done.
Qed.
(* </admitted> *)

Lemma cf_while_correct : forall e c k s,
  improves (eval_com (cf_while e c) k s) (eval_com (While e c) k s).
(* <admitted> *)
Proof.
intros e c k s.
destruct (cf_whileP e c) as [H| ->]; eauto.
destruct H as [-> ->]. rewrite /=.
destruct k; done.
Qed.
(* </admitted> *)

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
(* <admitted> *)
Proof.
intros c k s.
induction c as [|c1 IH1 c2 IH2|x e|e c1 IH1 c2 IH2|e c IH] in s, k |- *.
- done.
- rewrite /=. eapply improves_trans. { eapply cf_seq_correct. }
  rewrite /=. apply improves_bind; eauto.
- rewrite /=. eapply improves_trans. { eapply cf_assign_correct. }
  rewrite /=. apply improves_bind; eauto.
- rewrite /=. eapply improves_trans. { eapply cf_if_correct. }
  rewrite /=. apply improves_bind; eauto. intros n.
  destruct bool_decide; eauto.
- rewrite /=. eapply improves_trans. { eapply cf_while_correct. }
  rewrite /=. apply iter_improves. intros f g f_g s'.
  apply improves_bind; eauto. intros [|n]; rewrite /=; eauto.
  apply improves_bind; eauto.
Qed.
(* </admitted> *)

(** Exercise: Define a _constant propagation_ pass, which inlines the values of
    variables when they are known to be constant.  One possibility is to
    parameterize the optimization functions by a value [m : gmap string nat]
    which maps each variable to a natural number that is guaranteed to be its
    value during execution.  Prove that your definition is correct. *)
