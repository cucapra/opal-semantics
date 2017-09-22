Require Import OpalSrc.OpalSemantics CpdtTactics.

Fixpoint step_bool_fn (b: bool) (e: env) : option bool :=
  match b with
  | Eq (Var v) r => Some (Eq (e v) r)
  | Eq l (Var v) => Some (Eq l (e v))
  | Eq EmptySet EmptySet => Some True
  | Eq EmptySet _ => Some False
  | Eq _ EmptySet => Some False
  | Eq (Cons l1 l2) (Cons r1 r2) =>
    Some (Conj (Eq l1 r1) (Eq l2 r2))
  | Mem l EmptySet => Some False
  | Mem l (Var v) => Some (Mem l (e v))
  | Mem l (Cons l' r) =>
    Some (Disj (Eq l l') (Mem l r))
  | Conj l r =>
    match step_bool_fn l e with
    | None => match l with
              | True => Some r
              | False => Some False
              | _ => None (* impossible case *)
              end
    | Some l' => Some (Conj l' r)
    end
  | Disj l r =>
    match step_bool_fn l e with
    | None => match l with
              | True => Some True
              | False => Some r
              | _ => None (* impossible case *)
              end
    | Some l' => Some (Disj l' r)
    end
  | True => None
  | False => None
  end.

Fixpoint step_com_fn (c: com) (e: env) : option (com * env) :=
  match c with
  | Skip => None
  | If b c1 c2 =>
    match step_bool_fn b e with
    | Some b' => Some (If b' c1 c2, e)
    | None => match b with
              | True => Some (c1, e)
              | False => Some (c2, e)
              | _ => None (* impossible case *)
              end
    end
  | Seq c1 c2 =>
    match c1 with
    | Skip => Some (c2, e)
    | _ => match step_com_fn c1 e with
           | Some (c1', e') => Some (Seq c1' c2, e')
           | None => None (* impossible case *)
           end
    end
  | Assign v s =>
    Some (Skip, set_env e v s)
  end.

(*
Theorem step_bool_fn_progress : forall (b: bool) (sigma: env),
    step_bool_fn b sigma = None -> (b = True \/ b = False).
Proof.
  intros b sigma.
  induction b eqn:?.
  * destruct s, s0; crush.
  * destruct s, s0; crush.
  * crush.
    destruct (step_bool_fn b0_1 sigma).
    -
    contradiction.

*)