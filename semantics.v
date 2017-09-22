Require Import String ListSet CpdtTactics.

Definition var := string.


Inductive sexp :=
| EmptySet : sexp
| Var      : var -> sexp
| Cons     : sexp -> sexp -> sexp.

Inductive bool :=
| Eq : sexp -> sexp -> bool
| Mem : sexp -> sexp -> bool
| Conj : bool -> bool -> bool
| Disj : bool -> bool -> bool
| True : bool
| False : bool.

Inductive com :=
| Skip : com
| If : bool -> com -> com -> com
| Assign : var -> sexp -> com
| Seq : com -> com -> com.

Definition env := var -> sexp.
Definition empty_env : env := (fun var => EmptySet).
Definition set_env (e: env) (v: var) (s: sexp) : env :=
  fun var => match string_dec var v with
             | left _ => s
             | right _ => e var
             end.

Inductive step_bool : bool -> env -> bool -> Prop :=
(* Equals *)
| EqVarL : forall (v: var) (s1 s2: sexp) (sigma: env),
    sigma v = s1 -> step_bool (Eq (Var v) s2) sigma (Eq s1 s2)
| EqVarR : forall (v: var) (s1 s2: sexp) (sigma: env),
    sigma v = s2 -> step_bool (Eq s1 (Var v)) sigma (Eq s1 s2)
| EqEmpty : forall (sigma: env),
    step_bool (Eq EmptySet EmptySet) sigma True
| EqNotL : forall (s1 s2: sexp) (sigma: env),
    step_bool (Eq (Cons s1 s2) EmptySet) sigma False
| EqNotR : forall (s1 s2: sexp) (sigma: env),
    step_bool (Eq EmptySet (Cons s1 s2)) sigma False
| EqProp : forall (s1 s2 s1' s2': sexp) (sigma: env),
    step_bool (Eq (Cons s1 s2) (Cons s1' s2')) sigma (Conj (Eq s1 s1') (Eq s2 s2'))

(* Member *)
| MemVar : forall (v: var) (s1 s2: sexp) (sigma: env),
    sigma v = s2 -> step_bool (Mem s1 (Var v)) sigma (Mem s1 s2)
| MemEmpty : forall (s: sexp) (sigma: env),
    step_bool (Mem s EmptySet) sigma False
| MemCheck : forall (s1 s1' s2: sexp) (sigma: env),
    step_bool (Mem s1 (Cons s1' s2)) sigma (Disj (Eq s1 s1') (Mem s1 s2))

(* Conjunction *)
| ConjProp : forall (b1 b2 b1': bool) (sigma: env),
    step_bool b1 sigma b1' -> step_bool (Conj b1 b2) sigma (Conj b1' b2)
| ConjTrue : forall (b2: bool) (sigma: env),
    step_bool (Conj True b2) sigma b2
| ConjFalse : forall (b2: bool) (sigma: env),
    step_bool (Conj False b2) sigma False

(* Disjunction *)
| DisjProp : forall (b1 b2 b1': bool) (sigma: env),
    step_bool b1 sigma b1' -> step_bool (Disj b1 b2) sigma (Disj b1' b2)
| DisjTrue : forall (b2: bool) (sigma: env),
    step_bool (Disj True b2) sigma True
| DisjFalse : forall (b2: bool) (sigma: env),
    step_bool (Disj False b2) sigma b2.

Inductive step_com : com -> env -> com -> env -> Prop :=
(* If *)
| IfProp : forall (b b': bool) (c1 c2: com) (sigma: env),
    step_bool b sigma b' -> step_com (If b c1 c2) sigma (If b' c1 c2) sigma
| IfTrue : forall (c1 c2: com) (sigma: env),
    step_com (If True c1 c2) sigma c1 sigma
| IfFalse : forall (c1 c2: com) (sigma: env),
    step_com (If False c1 c2) sigma c2 sigma
(* Sequence *)
| SeqProp : forall (c1 c2 c1': com) (sigma sigma': env),
    step_com c1 sigma c1' sigma' -> step_com (Seq c1 c2) sigma (Seq c1' c2) sigma'
| SeqSkip : forall (c2: com) (sigma: env),
    step_com (Seq Skip c2) sigma c2 sigma
(* Assignment *)
| DoAssign : forall (v: var) (s: sexp) (sigma: env),
    step_com (Assign v s) sigma Skip (set_env sigma v s).

(*
Inductive sexp_closed_over : set var -> sexp -> Prop :=
| EmptyBound : forall (bound: set var),
    sexp_closed_over bound EmptySet
| VarBound : forall (bound: set var) (v: var),
    set_In v bound -> sexp_closed_over bound (Var v)
| ConsBound : forall (bound: set var) (s1 s2: sexp),
    sexp_closed_over bound s1 /\ sexp_closed_over bound s2 ->
    sexp_closed_over bound (Cons s1 s2).

Inductive bool_closed_over : set var -> bool -> Prop :=
| TrueBound : forall (bound: set var),
    bool_closed_over bound True
| FalseBound : forall (bound: set var),
    bool_closed_over bound False
| EqBound : forall (bound: set var) (s1 s2: sexp),
  sexp_closed_over bound s1 /\ sexp_closed_over bound s2 ->
  bool_closed_over bound (Eq s1 s2)
| MemBound : forall (bound: set var) (s1 s2: sexp),
  sexp_closed_over bound s1 /\ sexp_closed_over bound s2 ->
  bool_closed_over bound (Mem s1 s2)
| ConjBound : forall (bound: set var) (b1 b2: bool),
    bool_closed_over bound b1 /\ bool_closed_over bound b2 ->
    bool_closed_over bound (Conj b1 b2)
| DisjBound : forall (bound: set var) (b1 b2: bool),
    bool_closed_over bound b1 /\ bool_closed_over bound b2 ->
    bool_closed_over bound (Disj b1 b2).

Fixpoint update_bound (bound: set var) (com: com) : set var :=
  match com with
  | Assign v s => set_add string_dec v bound
  | Skip => bound
  | If b c1 c2 =>
    let c1b := update_bound bound c1 in
    let c2b := update_bound bound c2 in
    set_inter string_dec c1b c2b
  | Seq c1 c2 =>
    let c1b := update_bound bound c1 in
    update_bound c1b c2
  end.

Inductive com_closed_over : set var -> com -> Prop :=
| SkipBound : forall (bound: set var),
    com_closed_over bound Skip
| IfBound : forall (bound: set var) (b: bool) (c1 c2: com),
    bool_closed_over bound b /\ com_closed_over bound c1 /\ com_closed_over bound c2 ->
    com_closed_over bound (If b c1 c2)
| AssignBound : forall (bound: set var) (v: var) (s: sexp),
    sexp_closed_over bound s -> com_closed_over bound (Assign v s)
| SeqBound : forall (bound: set var) (c1 c2: com),
    com_closed_over bound c1 /\ com_closed_over (update_bound bound c1) c2 ->
    com_closed_over bound (Seq c1 c2).

 *)


Theorem bool_progress: forall (b: bool) (sigma: env),
    b = True \/ b = False \/ exists b', step_bool b sigma b'.
Proof.
  Hint Constructors step_bool.
  intros.
  induction b; intros; auto; right; right;
    try destruct s, s0; crush; eexists; eauto.
Qed.

Theorem com_progress : forall c: com,
    c = Skip \/ exists c' s', step_com c empty_env c' s'.
Proof.
  Hint Constructors step_com.
  intros.

  Ltac crush_if bool_prog b :=
    pose proof bool_progress as bool_prog;
    specialize bool_prog with b empty_env;
    crush; eexists; exists empty_env; eauto.

  induction c; crush; right;
    try progress crush_if bool_prog b;
    eexists; eexists; eauto.
Qed.