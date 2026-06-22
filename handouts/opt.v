From stdpp Require Import base gmap ssreflect strings.
From introduction Require Import imp.

Definition cp_add e1 e2 :=
  match e1, e2 with
  | Num n1, Num n2 => Num (n1 + n2)
  | Num 0, e
  | e, Num 0 => e
  | _, _ => Binop Add e1 e2
  end.

Definition cp_mul e1 e2 :=
  match e1, e2 with
  | Num n1, Num n2 => Num (n1 * n2)
  | Num 0, _
  | _, Num 0 => Num 0
  | Num 1, e
  | e, Num 1 => e
  | _, _ => Binop Mul e1 e2
  end.

Definition cp_sub e1 e2 :=
  match e1, e2 with
  | Num n1, Num n2 => Num (n1 - n2)
  | Num 0, _ => Num 0
  | _, Num 0 => e1
  | _, _ => Binop Sub e1 e2
  end.

Definition cp_leq e1 e2 :=
  match e1, e2 with
  | Num n1, Num n2 => Num (eval_binop Leq n1 n2)
  | Num 0, _ => Num 1
  | _, _ => Binop Leq e1 e2
  end.

Definition cp_binop b :=
  match b with
  | Add => cp_add
  | Mul => cp_mul
  | Sub => cp_sub
  | Leq => cp_leq
  end.

Fixpoint cp_expr e :=
  match e with
  | Binop b e1 e2 => cp_binop b (cp_expr e1) (cp_expr e2)
  | _ => e
  end.

Definition cp_seq c1 c2 :=
  match c1, c2 with
  | Skip, c
  | c, Skip => c
  | _, _ => Seq c1 c2
  end.

Definition cp_assign x e :=
  match e with
  | Var y => if bool_decide (x = y) then Skip else Assign x e
  | _ => Assign x e
  end.

Definition cp_if e c1 c2 :=
  if bool_decide (c1 = c2) then c1
  else match e with
       | Num n => if bool_decide (n = 0) then c2 else c1
       | _ => If e c1 c2
       end.

Definition cp_while e c :=
  if bool_decide (e = Num 0) then Skip else While e c.

Fixpoint cp_com c :=
  match c with
  | Skip => Skip
  | Seq c1 c2 => cp_seq (cp_com c1) (cp_com c2)
  | Assign x e => cp_assign x (cp_expr e)
  | If e c1 c2 => cp_if (cp_expr e) (cp_com c1) (cp_com c2)
  | While e c => cp_while (cp_expr e) (cp_com c)
  end.

Inductive cp_add_spec : expr -> expr -> expr -> Prop :=
| CpAdd1 n1 n2 : cp_add_spec (Num n1) (Num n2) (Num (n1 + n2))
| CpAdd2 e : cp_add_spec (Num 0) e e
| CpAdd3 e : cp_add_spec e (Num 0) e
| CpAdd4 e1 e2 : cp_add_spec e1 e2 (Binop Add e1 e2).

Lemma cp_addP e1 e2 : cp_add_spec e1 e2 (cp_add e1 e2).
Proof.
case: e1 => [x1|[|n1]|b1 e11 e12] /=;
case: e2 => [x2|[|n2]|b2 e21 e22] /=;
eauto using cp_add_spec.
Qed.

Inductive cp_mul_spec : expr -> expr -> expr -> Prop :=
| CpMul1 n1 n2 : cp_mul_spec (Num n1) (Num n2) (Num (n1 * n2))
| CpMul2 e : cp_mul_spec (Num 0) e (Num 0)
| CpMul3 e : cp_mul_spec e (Num 0) (Num 0)
| CpMul4 e : cp_mul_spec (Num 1) e e
| CpMul5 e : cp_mul_spec e (Num 1) e
| CpMul6 e1 e2 : cp_mul_spec e1 e2 (Binop Mul e1 e2).

Lemma cp_mulP e1 e2 : cp_mul_spec e1 e2 (cp_mul e1 e2).
Proof.
case: e1 => [x1|[|[|n1]]|b1 e11 e12];
case: e2 => [x2|[|[|n2]]|b2 e21 e22];
eauto using cp_mul_spec.
Qed.

Inductive cp_sub_spec : expr -> expr -> expr -> Prop :=
| CpSub1 n1 n2 : cp_sub_spec (Num n1) (Num n2) (Num (n1 - n2))
| CpSub2 e : cp_sub_spec (Num 0) e (Num 0)
| CpSub3 e : cp_sub_spec e (Num 0) e
| CpSub4 e1 e2 : cp_sub_spec e1 e2 (Binop Sub e1 e2).

Lemma cp_subP e1 e2 : cp_sub_spec e1 e2 (cp_sub e1 e2).
Proof.
case: e1 => [x1|[|n1]|b1 e11 e12];
case: e2 => [x2|[|n2]|b2 e21 e22];
eauto using cp_sub_spec.
Qed.

Inductive cp_leq_spec : expr -> expr -> expr -> Prop :=
| CpLeq1 n1 n2 : cp_leq_spec (Num n1) (Num n2) (Num (eval_binop Leq n1 n2))
| CpLeq2 e : cp_leq_spec (Num 0) e (Num 1)
| CpLeq3 e1 e2 : cp_leq_spec e1 e2 (Binop Leq e1 e2).

Lemma cp_leqP e1 e2 : cp_leq_spec e1 e2 (cp_leq e1 e2).
Proof.
case: e1 => [x1|[|n1]|b1 e11 e12];
case: e2 => [x2|[|n2]|b2 e21 e22];
eauto using cp_leq_spec.
Qed.

Inductive cp_seq_spec : com -> com -> com -> Prop :=
| CpSeq1 c : cp_seq_spec Skip c c
| CpSeq2 c : cp_seq_spec c Skip c
| CpSeq3 c1 c2 : cp_seq_spec c1 c2 (Seq c1 c2).

Lemma cp_seqP c1 c2 : cp_seq_spec c1 c2 (cp_seq c1 c2).
Proof.
by case: c1 => *; case: c2 => *; eauto using cp_seq_spec.
Qed.

Inductive cp_assign_spec : string -> expr -> com -> Prop :=
| CpAssign1 x : cp_assign_spec x (Var x) Skip
| CpAssign2 x e : e ≠ Var x → cp_assign_spec x e (Assign x e).

Lemma cp_assignP x e : cp_assign_spec x e (cp_assign x e).
Proof.
case: e => [y|n|b e1 e2]; eauto using cp_assign_spec.
rewrite /= bool_decide_decide.
case: (decide (x = y)) => [->|?]; eauto using cp_assign_spec.
assert (Var y ≠ Var x) as ?. { congruence. }
eauto using cp_assign_spec.
Qed.

Inductive cp_if_spec : expr -> com -> com -> com -> Prop :=
| CPIf1 e c : cp_if_spec e c c c
| CPIf2 c1 c2 : cp_if_spec (Num 0) c1 c2 c2
| CPIf3 n c1 c2 : n ≠ 0 -> cp_if_spec (Num n) c1 c2 c1
| CPIf4 e c1 c2 : cp_if_spec e c1 c2 (If e c1 c2).

Lemma cp_ifP e c1 c2 : cp_if_spec e c1 c2 (cp_if e c1 c2).
Proof.
rewrite /cp_if. case: bool_decide_reflect => [<-|_]; first exact: CPIf1.
case: e =>[x|[|n]|*]; eauto using cp_if_spec.
Qed.

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

Lemma improves_bind {T S} (x y : result T) (f g : T -> result S) :
  improves x y ->
  (∀ r, improves (f r) (g r)) ->
  improves (mbind f x) (mbind g y).
Proof.
case=> [->|->] //= f_g. by case: y => [r||] //=.
Qed.

Lemma improves_eval_expr {T} (x : result T) e s f :
  (∀ n, improves x (f n)) ->
  improves x (mbind f (eval_expr e s)).
Proof.
have := eval_expr_notyet e s.
case: eval_expr => //= n.
Qed.

Lemma cp_add_correct e1 e2 s :
  eval_expr (cp_add e1 e2) s = eval_expr (Binop Add e1 e2) s.
Proof.
case: cp_addP => [n1 n2|e|e|{}e1 {}e2] //=.
- by case: eval_expr => // n.
- by case: eval_expr => //= n; rewrite Nat.add_0_r.
Qed.

Lemma cp_mul_correct e1 e2 s :
  improves
    (eval_expr (cp_mul e1 e2) s)
    (eval_expr (Binop Mul e1 e2) s).
Proof.
rewrite /=.
case: e1 e2 _ / cp_mulP => [n1 n2|e|e|e|e|e1 e2] //=.
- by apply: improves_eval_expr.
- by apply: improves_eval_expr => ?; rewrite Nat.mul_0_r.
- rewrite -{1}[eval_expr e s]result_mbind_done.
  by apply: improves_bind => // n; rewrite Nat.add_0_r.
- rewrite -{1}[eval_expr e s]result_mbind_done.
  by apply: improves_bind => // n; rewrite Nat.mul_1_r.
Qed.

Lemma cp_sub_correct e1 e2 s :
  improves (eval_expr (cp_sub e1 e2) s) (eval_expr (Binop Sub e1 e2) s).
Proof.
rewrite /=.
case: e1 e2 _ / cp_subP => [n1 n2|e|e|e1 e2] //=.
- by apply: improves_eval_expr => ?; rewrite Nat.sub_0_l.
- rewrite -{1}[eval_expr e s]result_mbind_done.
  by apply: improves_bind => // n; rewrite Nat.sub_0_r.
Qed.

Lemma cp_leq_correct e1 e2 s :
  improves (eval_expr (cp_leq e1 e2) s) (eval_expr (Binop Leq e1 e2) s).
Proof.
rewrite /=; case: e1 e2 _ / cp_leqP => [n1' n2'|e|e1 e2] //=.
by apply: improves_eval_expr.
Qed.

Lemma cp_binop_correct s b e1 e2 :
  improves (eval_expr (cp_binop b e1 e2) s) (eval_expr (Binop b e1 e2) s).
Proof.
case: b.
- by rewrite cp_add_correct.
- exact: cp_mul_correct.
- exact: cp_sub_correct.
- exact: cp_leq_correct.
Qed.

Lemma cp_expr_correct e s :
  improves (eval_expr (cp_expr e) s) (eval_expr e s).
Proof.
elim: e => [x|n'|b e1 IH1 e2 IH2] //=.
apply: improves_trans.
- exact: cp_binop_correct.
- rewrite /=.
  apply: improves_bind => // n1.
  apply: improves_bind => // n2.
Qed.
Hint Resolve cp_expr_correct : core.

Lemma cp_seq_correct c1 c2 k s :
  improves (eval_com (cp_seq c1 c2) k s) (eval_com (Seq c1 c2) k s).
Proof.
case: c1 c2 _ / cp_seqP => [c|c|{}c1 c2] //=.
rewrite -{1}[eval_com _ _ _]result_mbind_done.
by apply: improves_bind => //.
Qed.

Lemma cp_assign_correct x e k s :
  improves (eval_com (cp_assign x e) k s) (eval_com (Assign x e) k s).
Proof.
case: x e _ / cp_assignP => [x|x e] //=.
case E: (s !! x) => [n|] //=. by rewrite insert_id.
Qed.

Lemma cp_if_correct e c1 c2 k s :
  improves (eval_com (cp_if e c1 c2) k s) (eval_com (If e c1 c2) k s).
Proof.
rewrite /=.
case: e c1 c2 _ / cp_ifP=> [e c|c1 c2|n c1 c2 n_not_0|e c1 c2] //=.
- apply: improves_eval_expr => //= n. by case: bool_decide.
- by rewrite bool_decide_eq_false_2.
Qed.

Lemma cp_while_correct e c k s :
  improves (eval_com (cp_while e c) k s) (eval_com (While e c) k s).
Proof.
rewrite /cp_while.
case: bool_decide_reflect => [->|] //.
by case: k.
Qed.

Lemma iter_improves {T} (f g : (T -> result T) -> T -> result T) x k :
  (∀ f' g', (∀ x, improves (f' x) (g' x)) ->
             ∀ x, improves (f f' x) (g g' x)) ->
  improves (iter f k x) (iter g k x).
Proof.
move=> H; elim: k => //= [|k IH] in x *; apply: H => // {}x.
Qed.

Lemma cp_com_correct c k s :
  improves (eval_com (cp_com c) k s) (eval_com c k s).
Proof.
elim: c => [|c1 IH1 c2 IH2|x e|e c1 IH1 c2 IH2|e c IH] //= in s k *.
- apply: improves_trans; first exact: cp_seq_correct.
  by rewrite /=; apply: improves_bind => //.
- apply: improves_trans; first exact: cp_assign_correct.
  by rewrite /=; apply: improves_bind => //.
- apply: improves_trans; first exact: cp_if_correct.
  rewrite /=; apply: improves_bind => // n.
  by case: bool_decide.
- apply: improves_trans; first exact: cp_while_correct.
  rewrite /=. apply: iter_improves=> f g f_g {}s.
  apply: improves_bind => // - [|n] //=.
  apply: improves_bind => //=.
Qed.
