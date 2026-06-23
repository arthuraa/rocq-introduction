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

Definition cp_add_spec (e1 e2 e : expr) : Prop :=
  (exists n1 n2, e1 = Num n1 /\ e2 = Num n2 /\ e = Num (n1 + n2)) \/
  (e1 = Num 0 /\ e2 = e) \/
  (e1 = e /\ e2 = Num 0) \/
  (e = Binop Add e1 e2).

Lemma cp_addP e1 e2 : cp_add_spec e1 e2 (cp_add e1 e2).
Proof.
rewrite /cp_add_spec.
destruct e1 as [x1|[|n1]|b1 e11 e12];
destruct e2 as [x2|[|n2]|b2 e21 e22];
eauto 10.
Qed.

Definition cp_mul_spec (e1 e2 e : expr) : Prop :=
  (exists n1 n2, e1 = Num n1 /\ e2 = Num n2 /\ e = Num (n1 * n2)) \/
  (e1 = Num 0 /\ e = Num 0) \/
  (e2 = Num 0 /\ e = Num 0) \/
  (e1 = Num 1 /\ e2 = e) \/
  (e1 = e /\ e2 = Num 1) \/
  (e = Binop Mul e1 e2).

Lemma cp_mulP e1 e2 : cp_mul_spec e1 e2 (cp_mul e1 e2).
Proof.
rewrite /cp_mul_spec.
destruct e1 as [x1|[|[|n1]]|b1 e11 e12]; eauto;
destruct e2 as [x2|[|[|n2]]|b2 e21 e22]; eauto 10.
Qed.

Definition cp_sub_spec e1 e2 e : Prop :=
  (exists n1 n2, e1 = Num n1 /\ e2 = Num n2 /\ e = Num (n1 - n2)) \/
  (e1 = Num 0 /\ e = Num 0) \/
  (e1 = e /\ e2 = Num 0) \/
  (e = Binop Sub e1 e2).

Lemma cp_subP e1 e2 : cp_sub_spec e1 e2 (cp_sub e1 e2).
Proof.
rewrite /cp_sub_spec.
destruct e1 as [x1|[|n1]|b1 e11 e12]; eauto;
destruct e2 as [x2|[|n2]|b2 e21 e22]; eauto 10.
Qed.

Definition cp_leq_spec e1 e2 e : Prop :=
  (exists n1 n2, e1 = Num n1 /\ e2 = Num n2 /\
                 e = Num (eval_binop Leq n1 n2)) \/
  (e1 = Num 0 /\ e = Num 1) \/
  (e = Binop Leq e1 e2).

Lemma cp_leqP e1 e2 : cp_leq_spec e1 e2 (cp_leq e1 e2).
Proof.
rewrite /cp_leq_spec.
destruct e1 as [x1|[|n1]|b1 e11 e12]; eauto;
destruct e2 as [x2|[|n2]|b2 e21 e22]; eauto 10.
Qed.

Definition cp_seq_spec c1 c2 c : Prop :=
  (c1 = Skip /\ c2 = c) \/
  (c1 = c /\ c2 = Skip) \/
  (c = Seq c1 c2).

Lemma cp_seqP c1 c2 : cp_seq_spec c1 c2 (cp_seq c1 c2).
Proof.
rewrite /cp_seq_spec.
destruct c1; destruct c2; eauto 10.
Qed.

Definition cp_assign_spec x e c :=
  (e = Var x /\ c = Skip) \/
  (e <> Var x /\ c = Assign x e).

Lemma cp_assignP x e : cp_assign_spec x e (cp_assign x e).
Proof.
rewrite /cp_assign_spec.
destruct e as [y|n|b e1 e2]; eauto 10.
rewrite /= bool_decide_decide.
destruct (decide (x = y)) as [->|?]; eauto.
assert (Var y ≠ Var x) as ?. { congruence. }
eauto.
Qed.

Definition cp_if_spec e c1 c2 c :=
  (c1 = c2 /\ c2 = c) \/
  (e = Num 0 /\ c2 = c) \/
  (exists n, e = Num n /\ n <> 0 /\ c1 = c) \/
  (c = If e c1 c2).

Lemma cp_ifP e c1 c2 : cp_if_spec e c1 c2 (cp_if e c1 c2).
Proof.
rewrite /cp_if_spec /cp_if.
destruct (bool_decide_reflect (c1 = c2)) as [<-|_]; eauto 10.
destruct e as [x|[|n]|*]; eauto 10.
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

Lemma cp_add_correct e1 e2 s :
  eval_expr (cp_add e1 e2) s = eval_expr (Binop Add e1 e2) s.
Proof.
destruct (cp_addP e1 e2) as [H|[H|[H|H]]].
- destruct H as (n1 & n2 & -> & -> & ->). done.
- destruct H as (-> & <-). rewrite /=.
  destruct eval_expr; eauto.
- destruct H as (<- & ->). rewrite /=.
  destruct eval_expr; eauto; rewrite /=.
  rewrite Nat.add_0_r. done.
- rewrite H. done.
Qed.

Lemma cp_mul_correct e1 e2 s :
  improves
    (eval_expr (cp_mul e1 e2) s)
    (eval_expr (Binop Mul e1 e2) s).
Proof.
rewrite /=.
destruct (cp_mulP e1 e2) as [H|[H|[H|[H|[H|H]]]]].
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

Lemma cp_sub_correct e1 e2 s :
  improves (eval_expr (cp_sub e1 e2) s) (eval_expr (Binop Sub e1 e2) s).
Proof.
rewrite /=.
destruct (cp_subP e1 e2) as [H|[H|[H|H]]].
- destruct H as (n1 & n2 & -> & -> & ->). done.
- destruct H as (-> & ->). rewrite /=.
  by apply: improves_eval_expr => ?; rewrite Nat.sub_0_l.
- destruct H as (<- & ->). rewrite /=.
  rewrite -{1}[eval_expr e1 s]result_mbind_done.
  by apply: improves_bind => // n; rewrite Nat.sub_0_r.
- rewrite H. done.
Qed.

Lemma cp_leq_correct e1 e2 s :
  improves (eval_expr (cp_leq e1 e2) s) (eval_expr (Binop Leq e1 e2) s).
Proof.
rewrite /=.
destruct (cp_leqP e1 e2) as [H|[H|H]].
- destruct H as (n1 & n2 & -> & -> & ->). done.
- destruct H as (-> & ->). rewrite /=.
  by apply: improves_eval_expr.
- by rewrite H.
Qed.

Lemma cp_binop_correct s b e1 e2 :
  improves (eval_expr (cp_binop b e1 e2) s) (eval_expr (Binop b e1 e2) s).
Proof.
destruct b.
- by rewrite cp_add_correct.
- apply cp_mul_correct.
- apply cp_sub_correct.
- apply cp_leq_correct.
Qed.

Lemma cp_expr_correct e s :
  improves (eval_expr (cp_expr e) s) (eval_expr e s).
Proof.
induction e as [x|n'|b e1 IH1 e2 IH2]; eauto.
eapply improves_trans. { eapply cp_binop_correct. }
rewrite /=.
apply improves_bind; eauto. intros n1.
apply improves_bind; eauto.
Qed.
Hint Resolve cp_expr_correct : core.

Lemma cp_seq_correct c1 c2 k s :
  improves (eval_com (cp_seq c1 c2) k s) (eval_com (Seq c1 c2) k s).
Proof.
destruct (cp_seqP c1 c2) as [H|[H|H]]; rewrite /=.
- destruct H as (-> & <-). done.
- destruct H as (<- & ->). rewrite result_mbind_done. done.
- rewrite H. done.
Qed.

Lemma cp_assign_correct x e k s :
  improves (eval_com (cp_assign x e) k s) (eval_com (Assign x e) k s).
Proof.
destruct (cp_assignP x e) as [H|H].
- destruct H as (-> & ->). rewrite /=.
  destruct (s !! x) as [n|] eqn:E; rewrite /=; eauto.
  rewrite insert_id; done.
- destruct H as (_ & ->). done.
Qed.

Lemma cp_if_correct e c1 c2 k s :
  improves (eval_com (cp_if e c1 c2) k s) (eval_com (If e c1 c2) k s).
Proof.
destruct (cp_ifP e c1 c2) as [H|[H|[H|H]]]; rewrite /=.
- destruct H as (<- & <-).
  apply improves_eval_expr. intros n.
  destruct bool_decide; done.
- destruct H as (-> & <-). done.
- destruct H as (n & -> & n0 & <-). rewrite /=.
  rewrite bool_decide_eq_false_2; done.
- rewrite H. done.
Qed.

Lemma cp_while_correct e c k s :
  improves (eval_com (cp_while e c) k s) (eval_com (While e c) k s).
Proof.
rewrite /cp_while.
destruct bool_decide eqn:E.
- rewrite bool_decide_eq_true in E. rewrite E /=.
  destruct k; done.
- done.
Qed.

Lemma iter_improves {T} (f g : (T -> result T) -> T -> result T) x k :
  (∀ f' g', (∀ x, improves (f' x) (g' x)) ->
             ∀ x, improves (f f' x) (g g' x)) ->
  improves (iter f k x) (iter g k x).
Proof.
intros H.
induction k as [|k IH] in x |- *; rewrite /=; apply H; eauto.
Qed.

Lemma cp_com_correct c k s :
  improves (eval_com (cp_com c) k s) (eval_com c k s).
Proof.
induction c as [|c1 IH1 c2 IH2|x e|e c1 IH1 c2 IH2|e c IH] in s, k |- *.
- done.
- rewrite /=. eapply improves_trans. { eapply cp_seq_correct. }
  rewrite /=. apply improves_bind; eauto.
- rewrite /=. eapply improves_trans. { eapply cp_assign_correct. }
  rewrite /=. apply improves_bind; eauto.
- rewrite /=. eapply improves_trans. { eapply cp_if_correct. }
  rewrite /=. apply improves_bind; eauto. intros n.
  destruct bool_decide; eauto.
- rewrite /=. eapply improves_trans. { eapply cp_while_correct. }
  rewrite /=. apply iter_improves. intros f g f_g s'.
  apply improves_bind; eauto. intros [|n]; rewrite /=; eauto.
  apply improves_bind; eauto.
Qed.
