From stdpp Require Import base gmap.
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
