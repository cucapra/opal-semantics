Require Import String ListSet CpdtTactics Wf String.
Require Import OpalSrc.OpalUtil.

Set Implicit Arguments.
Open Scope string_scope.

Axiom proof_irrelevance :
  forall (P : Prop) (p q : P), p = q.


Module Opal (NodeMap VarMap WorldMap OpMap: SmallMap).

  Module NodeVarMap := PairMap NodeMap VarMap.

  Definition node := NodeMap.key.
  Definition var := VarMap.key.
  Definition world := WorldMap.key.
  Definition op := OpMap.key.

  Inductive sexp :=
  | EmptySet : sexp
  | Var      : node -> var -> sexp
  | Cons     : sexp -> sexp -> sexp.

  Definition eq_dec_sexp : eq_dec sexp.
  Proof.
    unfold eq_dec.
    specialize NodeMap.eq_dec_key.
    specialize VarMap.eq_dec_key.
    decide equality.
  Qed.

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

  Definition eq_dec_sexp_value : eq_dec sexp_value.
  Proof.
    unfold eq_dec.
    intros.
    destruct l, r.
    destruct (eq_dec_sexp x x0).
    * crush.
      specialize (proof_irrelevance s s0).
      crush.
    * right. crush.
Qed.

  Inductive bool :=
  | Eq    : sexp -> sexp -> bool
  | Mem   : sexp -> sexp -> bool
  | Conj  : bool -> bool -> bool
  | Disj  : bool -> bool -> bool
  | True  : bool
  | False : bool.

  Inductive bool_is_value : bool -> Prop :=
  | TrueIsValue : bool_is_value True
  | FalseIsValue : bool_is_value False.

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


  Definition var_store := NodeVarMap.t sexp_value.

  Definition get_env (vs: var_store) (n: node) (v: var) (sv: sexp_value) : Prop :=
    NodeVarMap.get sexp_value eq_dec_sexp_value vs (n,v) sv.

  Definition set_env (vs: var_store) (n: node) (v: var) (sv: sexp_value) (vs': var_store): Prop :=
    NodeVarMap.set sexp_value eq_dec_sexp_value vs (n,v) sv vs'.

  Definition mem (env: var_store) (n: node) (v: var) : Prop :=
    forall env n v, exists s, get_env env n v s.

  Definition fold_env
             (vs: var_store)
             (A: Type)
             (f: A -> sexp_value -> A)
             (init: A)
             (res: A) : Prop :=
    let f' := fun acc kv => match kv with
                            | (_, v) => f acc v
                            end
    in
    (NodeVarMap.fold sexp_value eq_dec_sexp_value A f' init vs res).

  Definition empty_var_store : var_store :=
    NodeVarMap.empty sexp_value eq_dec_sexp_value.

  Definition var_store_stack := list var_store.

  Definition world_eq_dec : eq_dec (var_store_stack * var_store).
  Proof.
    unfold eq_dec.
    specialize (NodeVarMap.eq_dec_t sexp_value eq_dec_sexp_value) as vseqdec.
    specialize (List.list_eq_dec vseqdec).
    decide equality.
  Qed.

  Definition world_store := WorldMap.t (var_store_stack * var_store).
  Definition get_world_store ws w vss vs : Prop :=
    WorldMap.get (var_store_stack * var_store) world_eq_dec ws w (vss,vs).
  Definition set_world_store ws w vss vs ws': Prop :=
    WorldMap.set (var_store_stack * var_store) world_eq_dec ws w (vss,vs) ws'.
  Definition principals := set node.
  Definition location := node.

  Definition node_var_sexp_eq_dec : eq_dec (node * var * sexp).
  Proof.
    unfold eq_dec.
    specialize eq_dec_sexp.
    specialize NodeMap.eq_dec_key.
    specialize VarMap.eq_dec_key.
    intros.
    destruct l, r.
    destruct p, p0.
    decide equality.
    destruct a, p.
    decide equality.
  Qed.

  Definition handlers := OpMap.t (node * var * sexp).
  Definition get_handler hs op n v s : Prop :=
    OpMap.get (node * var * sexp) node_var_sexp_eq_dec hs op (n,v,s).
  Definition set_handler hs op n v s hs' : Prop :=
    OpMap.set (node * var * sexp) node_var_sexp_eq_dec hs op (n,v,s) hs'.


  Definition mergers := NodeVarMap.t sexp.
  Definition get_merger m (n: node) (v: var) (s: sexp) : Prop :=
    NodeVarMap.get sexp eq_dec_sexp m (n,v) s.
  Definition set_merger m (n: node) (v: var) (s: sexp) m' : Prop :=
    NodeVarMap.set sexp eq_dec_sexp m (n,v) s m'.

  Inductive error :=
  | GenericErr : string -> error
  | LookupErr  : node -> var -> error
  | ReadPermErr : node -> var -> principals -> error
  | WritePermErr : node -> var -> principals -> error
  | MergeErr : node -> var -> mergers -> error
  | HandleErr : op -> handlers -> error
  | BoolEvalErr : bool -> error
  | CommitErr : world -> world_store -> error.
End Opal.