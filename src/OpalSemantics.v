Require Import String ListSet CpdtTactics Wf String.
Require Import OpalSrc.OpalUtil.

Set Implicit Arguments.
Open Scope string_scope.

Axiom proof_irrelevance :
  forall (P : Prop) (p q : P), p = q.

Definition var := string.
Definition node := string.
Definition world := string.
Definition op := string.

Inductive sexp :=
| EmptySet : sexp
| Var      : node -> var -> sexp
| Cons     : sexp -> sexp -> sexp.

Inductive sexp_is_value : sexp -> Prop :=
| EmptySetIsValue : sexp_is_value EmptySet
| ConsValuesIsValue : forall s1 s2,
    sexp_is_value s1 -> sexp_is_value s2 -> sexp_is_value (Cons s1 s2).
Hint Constructors sexp_is_value.

Definition is_sexp_value : forall s, {sexp_is_value s} + {~sexp_is_value s}.
Proof.
  intros.
  induction s.
  * left. auto.
  * right. unfold not. intros. inversion H.
  * destruct IHs1; destruct IHs2.
    - auto.
    - right. unfold not. intros. inversion H. contradiction H3.
    - right. unfold not. intros. inversion H. contradiction H2.
    - right. unfold not. intros. inversion H. contradiction H2.
Qed.

Definition sexp_value := {sexp | sexp_is_value sexp}.

Inductive bool :=
| Eq    : sexp -> sexp -> bool
| Mem   : sexp -> sexp -> bool
| Conj  : bool -> bool -> bool
| Disj  : bool -> bool -> bool
| True  : bool
| False : bool.

Inductive bool_is_value : bool -> Prop :=
| TrueIsValue : bool_is_value True
| FalseIsValue : bool_is_value False
.
Definition bool_value := { b: bool | bool_is_value b}.

Inductive com :=
| Skip   : com
| Seq    : com -> com -> com
| If     : bool -> com -> com -> com
| With   : node -> com -> com
| At     : node -> com -> com
| Hyp    : world -> com -> com
| Commit : world -> com
| Handle : node -> var -> op -> sexp -> sexp -> com -> com
| Op     : op -> com.

Module Opal (NodeMap VarMap WorldMap: SmallMap).
  Definition node := NodeMap.key.
  Definition var := VarMap.key.
  Definition world := WorldMap.key.


  Definition var_store :
  Variable get_env : var_store -> node -> var -> sexp_value -> Prop.
  Variable set_env : var_store -> node -> var -> sexp_value -> var_store -> Prop.
  Variable set_env_assigns :
    forall n v s store store',
    set_env store n v s store' ->
    get_env store' n v s.
  Variable set_env_maintains :
    forall n v s store store',
    set_env store n v s store' ->
    forall n' v' s',
      n <> n' -> v <> v' ->
      get_env store n' v' s' ->
      get_env store' n' v' s'.
  Variable set_env_conservative :
    forall n v s store store',
    set_env store n v s store' ->
    forall n' v' s',
      n <> n' -> v <> v' ->
      ~ get_env store n' v' s' ->
      ~ get_env store' n' v' s'.
  Definition mem (env: var_store) (n: node) (v: var) : Prop :=
    forall env n v, exists s, get_env env n v s.

  Variable fold_env : var_store ->
                      forall acc, (acc -> sexp_value -> acc) -> acc -> acc.
  Variable fold_base : forall env accT f acc,
      (forall n v s, ~ get_env env n v s) ->
      @fold_env env accT f acc = acc.
  Variable fold_extend :
    forall env env' accT f acc n v s,
      ~ mem env n v ->
      set_env env n v s env' ->
      @fold_env env' accT f acc = f acc s.

  Variable empty_var_store : var_store.
  Variable empty_var_store_is_empty : forall n v s, ~ get_env empty_var_store n v s.

  Definition var_store_stack := list var_store.

  Variable world_store : Type.
  Variable get_world_store : world_store -> world -> var_store_stack -> var_store -> Prop.
  Variable set_world_store : world_store -> world -> var_store_stack -> var_store -> world_store -> Prop.
  Variable set_world_store_assigns :
    forall u s1 s2 store store',
    set_world_store store u s1 s2 store' ->
    get_world_store store' u s1 s2.
  Variable set_world_store_maintains :
    forall u s1 s2 store store',
    set_world_store store u s1 s2 store' ->
    forall u' s1' s2',
      u <> u' ->
      get_world_store store u' s1' s2' ->
      get_world_store store' u' s1' s2'.
  Variable set_world_store_conservative :
    forall u s1 s2 store store',
    set_world_store store u s1 s2 store' ->
    forall u' s1' s2',
      u <> u' ->
      ~ get_world_store store u' s1' s2' ->
      ~ get_world_store store' u' s1' s2'.


Definition principals := set node.
Definition location := node.
Definition handlers := op -> option (node * var * sexp).
Definition mergers := node -> var -> option sexp.

Inductive error :=
| GenericErr : string -> error
| LookupErr  : node -> var -> error
| ReadPermErr : node -> var -> principals -> error
| WritePermErr : node -> var -> principals -> error
| MergeErr : node -> var -> mergers -> error
| HandleErr : op -> handlers -> error
| BoolEvalErr : bool -> error
| CommitErr : world -> world_store -> error
.
