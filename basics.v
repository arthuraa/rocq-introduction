From mathcomp Require Import all_ssreflect.

Require Extraction.

Module NatPlayground.

Inductive nat :=
| O
| S (n : nat).

Definition zero := O.
Definition one := S zero.
Definition two := S one.

Fixpoint addn n m :=
  match n with
  | O => m
  | S n' => S (addn n' m)
  end.

Lemma add0n : left_id O addn.
Proof. move=> m. rewrite /=. by []. Qed.

Lemma addn0 : right_id O addn.
Proof. move=> m. elim: m => [|m IH].
- rewrite /=. by [].
- rewrite /=. rewrite IH. by [].
Qed.

Lemma addnS n m : addn n (S m) = S (addn n m).
Proof.
elim: n => /= [|n IH].
- by [].
- by rewrite IH.
Qed.

Lemma addnC n m : addn n m = addn m n.
Proof.
elim: n => /= [|n IH].
- by rewrite addn0.
- by rewrite addnS IH.
Qed.

Lemma addnA n m p : addn n (addn m p) = addn (addn n m) p.
Proof. Admitted.

Fixpoint leq n m :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leq n' m'
      end
  end.

Lemma leqnn n : leq n n.
Proof. by elim: n => /= [|n ->]. Qed.

Lemma leq_trans n m p : leq n m -> leq m p -> leq n p.
Proof.
elim: n => //= n IH in m p *.
case: m => //= m.
case: p => //= p.
exact: IH.
Qed.

Lemma leq_anti n m : leq n m -> leq m n -> n = m.
Proof.
elim: n => //= [|n IH] in m *.
- by case: m.
- case: m => //= m nm mn.
  by rewrite (IH m nm mn).
Qed.

Lemma leq_addl n1 n2 m : leq n1 n2 -> leq (addn n1 m) (addn n2 m).
Proof. Admitted.

Lemma leq_addr n m1 m2 : leq m1 m2 -> leq (addn n m1) (addn n m2).
Proof. Admitted.

End NatPlayground.

Lemma test1 : 2 = S (S O).
Proof. by []. Qed.

Lemma test2 : 1 + 1 = 2.
Proof. by []. Qed.

Module SeqPlayground.

Inductive seq (T : Type) : Type :=
| nil
| cons (x : T) (xs : seq T).

Arguments nil {T}.

Fixpoint cat T (xs ys : seq T) : seq T :=
  match xs with
  | nil => ys
  | cons x xs' => cons x (cat xs' ys)
  end.

Lemma catA T (xs ys zs : seq T) : cat xs (cat ys zs) = cat (cat xs ys) zs.
Proof.
elim: xs => //= x xs IH.
by rewrite IH.
Qed.

End SeqPlayground.

Fixpoint insert (x : nat) (xs : seq nat) : seq nat :=
  match xs with
  | [::] => [:: x]
  | x' :: xs' => if x <= x' then x :: x' :: xs'
                 else x' :: insert x xs'
  end.

Fixpoint insertion_sort xs :=
  match xs with
  | [::] => [::]
  | x :: xs' => insert x (insertion_sort xs')
  end.

Fixpoint sorted xs :=
  match xs with
  | [::] => true
  | x :: xs =>
      match xs with
      | [::] => true
      | x' :: xs' => x <= x'
      end && sorted xs
  end.

Fixpoint count (x : nat) xs :=
  match xs with
  | [::] => 0
  | y :: xs' => (x == y) + count x xs'
  end.

Lemma count_insert x y xs : count x (insert y xs) = (x == y) + count x xs.
Proof.
elim: xs => //= z xs IH.
case: leqP => //=.
move=> zy. by rewrite IH addnCA.
Qed.

Lemma count_sort x xs : count x xs = count x (insertion_sort xs).
Proof.
elim: xs => //= y xs IH.
by rewrite count_insert IH.
Qed.

Lemma sorted_insert x xs : sorted xs -> sorted (insert x xs).
Proof.
elim: xs => //= y xs' IH sorted_xs.
case/andP: sorted_xs => y_xs' sorted_xs'.
case: leqP => [xy|yx].
- by rewrite /= xy y_xs'.
- rewrite /= {}IH // andbT.
  case: xs' => /= [|z xs''] in y_xs' {sorted_xs'} *.
  + by rewrite ltnW.
  + case: leqP => [xz|zx] //.
    by rewrite ltnW.
Qed.

Lemma sorted_sort xs : sorted (insertion_sort xs).
Proof.
elim: xs => //= x xs IH.
by rewrite sorted_insert.
Qed.

Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive nat  => "int" ["0" "(fun n -> n + 1)"]
  "(fun fO fS n -> if n = 0 then fO () else fS (n - 1))".
Extract Inductive list => "list" ["[]" "(::)"].

Extraction "sort.ml" insertion_sort.
