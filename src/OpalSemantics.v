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

  Inductive var_store_stack_get :
    var_store_stack -> node -> var -> sexp_value -> Prop :=
  | HeadGet :
      forall h t n v s,
        get_env h n v s ->
        var_store_stack_get (cons h t) n v s
  | TailGet :
      forall h t n v s,
        var_store_stack_get t n v s ->
        var_store_stack_get (cons h t) n v s
    .

  Definition world_eq_dec : eq_dec (var_store_stack * var_store).
  Proof.
    unfold eq_dec.
    specialize (NodeVarMap.eq_dec_t sexp_value eq_dec_sexp_value) as vseqdec.
    specialize (List.list_eq_dec vseqdec).
    decide equality.
  Qed.

  Definition world_store := WorldMap.t (var_store_stack * var_store).
  Definition empty_world_store : world_store :=
    WorldMap.empty (var_store_stack * var_store) world_eq_dec.
  Definition get_world_store ws w vss vs : Prop :=
    WorldMap.get (var_store_stack * var_store) world_eq_dec ws w (vss,vs).
  Definition set_world_store ws w vss vs ws': Prop :=
    WorldMap.set (var_store_stack * var_store) world_eq_dec ws w (vss,vs) ws'.
  Definition principals := set node.
  Definition location := node.

  Definition node_var_eq_dec : eq_dec (node * var).
  Proof.
    unfold eq_dec.
    specialize NodeMap.eq_dec_key.
    specialize VarMap.eq_dec_key.
    intros.
    destruct l, r.
    decide equality.
  Qed.

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


  Section WellFormed.
    Definition Sigma := set (node * var).
    Definition H := set op.
    Definition Pi := set node.
    Definition Omega := set world.

    Inductive well_formed_sexp : Sigma -> sexp -> Prop :=
    | EmptySetWF : forall s, well_formed_sexp s EmptySet
    | NodeVarWf : forall s n v,
        set_In (n,v) s ->
        well_formed_sexp s (Var n v)
    | ConsWf : forall s s1 s2,
        well_formed_sexp s s1 ->
        well_formed_sexp s s2 ->
        well_formed_sexp s (Cons s1 s2)
    .

    Inductive well_formed_bool : Sigma -> bool -> Prop :=
    | TrueWF : forall s, well_formed_bool s True
    | FalseWF : forall s, well_formed_bool s False
    | ConjWF : forall s b1 b2,
        well_formed_bool s b1 ->
        well_formed_bool s b2 ->
        well_formed_bool s (Conj b1 b2)
    | DisjWF : forall s b1 b2,
        well_formed_bool s b1 ->
        well_formed_bool s b2 ->
        well_formed_bool s (Disj b1 b2)
    | EqWF : forall s s1 s2,
        well_formed_sexp s s1 ->
        well_formed_sexp s s2 ->
        well_formed_bool s (Eq s1 s2)
    | MemWF : forall s s1 s2,
        well_formed_sexp s s1 ->
        well_formed_sexp s s2 ->
        well_formed_bool s (Mem s1 s2)
    .

    Inductive well_formed_com : Omega -> Pi -> Sigma -> H -> com -> Omega -> Prop :=
    | SkipWF : forall Omega Pi Sigma H, well_formed_com Omega Pi Sigma H Skip Omega
    | SeqWf : forall Omega Omega' Omega'' Pi Sigma H c1 c2,
        well_formed_com Omega Pi Sigma H c1 Omega' ->
        well_formed_com Omega' Pi Sigma H c2 Omega'' ->
        well_formed_com Omega Pi Sigma H (Seq c1 c2) Omega''
    | IfWf : forall Omega Omega' Omega'' Pi Sigma H b c1 c2,
        well_formed_bool Sigma b ->
        well_formed_com Omega Pi Sigma H c1 Omega' ->
        well_formed_com Omega Pi Sigma H c2 Omega'' ->
        well_formed_com Omega Pi Sigma H (If b c1 c2) (set_inter WorldMap.eq_dec_key Omega' Omega'')
    | HypWf : forall Omega Omega' Pi Sigma H w c,
        well_formed_com (empty_set world) Pi Sigma H c Omega' ->
        well_formed_com Omega Pi Sigma H (Hyp w c) (set_add WorldMap.eq_dec_key w Omega)
    | CommitWf : forall Omega Pi Sigma H w,
        set_In w Omega ->
        well_formed_com Omega Pi Sigma H (Commit w) (set_remove WorldMap.eq_dec_key w Omega)
    | HandleWf : forall Omega Omega' Pi Sigma H n v op s1 s2 c,
        set_In n Pi ->
        well_formed_sexp Sigma s1 ->
        well_formed_sexp Sigma s2 ->
        well_formed_com (empty_set world) Pi (set_add NodeVarMap.eq_dec_key (n,v) Sigma) (set_add OpMap.eq_dec_key op H) c Omega' ->
        well_formed_com Omega Pi Sigma H (Handle n v op s1 s2 c) Omega
    | OpWf : forall Omega Pi Sigma H op,
        set_In op H ->
        well_formed_com Omega Pi Sigma H (Op op) Omega
    | WithWf : forall Omega Omega' Pi Sigma H n c,
        well_formed_com Omega (set_add NodeMap.eq_dec_key n Pi) Sigma H c Omega' ->
        well_formed_com Omega Pi Sigma H (With n c) Omega'
    | AtWf : forall Omega Omega' Pi Sigma H n c,
        well_formed_com Omega Pi Sigma H c Omega' ->
        well_formed_com Omega Pi Sigma H (At n c) Omega'
    .
  End WellFormed.

  Definition EmptySetValue := (exist sexp_is_value EmptySet EmptySetIsValue).

  Section BigStep.
    Inductive step_sexp : sexp -> var_store_stack -> principals -> sexp_value -> Prop :=
    | EmptySetStep : forall Sigma pi,
        step_sexp EmptySet Sigma pi EmptySetValue
    | ConsStep : forall Sigma pi l r lv lp rv rp,
        step_sexp l Sigma pi (exist sexp_is_value lv lp) ->
        step_sexp r Sigma pi (exist sexp_is_value rv rp) ->
        step_sexp (Cons l r) Sigma pi (exist sexp_is_value (Cons lv rv) (ConsValuesIsValue lp rp))
    | VarStep : forall Sigma  pi n v s,
        var_store_stack_get Sigma n v s ->
        set_In n pi ->
        step_sexp (Var n v) Sigma pi s.

    Definition TrueValue := (exist bool_is_value True TrueIsValue).
    Definition FalseValue := (exist bool_is_value False FalseIsValue).

    Inductive step_bool : bool -> var_store_stack -> principals -> bool_value -> Prop :=
    | TrueStep : forall Sigma pi,
        step_bool True Sigma pi TrueValue
    | FalseStep : forall Sigma pi,
        step_bool False Sigma pi FalseValue
    | AndTrue : forall Sigma pi b1 b2,
        step_bool b1 Sigma pi TrueValue ->
        step_bool b2 Sigma pi TrueValue ->
        step_bool (Conj b1 b2) Sigma pi TrueValue
    | AndFalseL : forall Sigma pi b1 b2,
        step_bool b1 Sigma pi FalseValue ->
        step_bool (Conj b1 b2) Sigma pi FalseValue
    | AndFalseR : forall Sigma pi b1 b2,
        step_bool b2 Sigma pi FalseValue ->
        step_bool (Conj b1 b2) Sigma pi FalseValue
    | OrFalse : forall Sigma pi b1 b2,
        step_bool b1 Sigma pi FalseValue ->
        step_bool b2 Sigma pi FalseValue ->
        step_bool (Conj b1 b2) Sigma pi FalseValue
    | OrTrueL : forall Sigma pi b1 b2,
        step_bool b1 Sigma pi TrueValue ->
        step_bool (Conj b1 b2) Sigma pi TrueValue
    | OrTrueR : forall Sigma pi b1 b2,
        step_bool b2 Sigma pi TrueValue ->
        step_bool (Conj b1 b2) Sigma pi TrueValue
    | EqTrue :
        forall Sigma pi s1 s2,
        step_sexp s1 Sigma pi EmptySetValue ->
        step_sexp s2 Sigma pi EmptySetValue ->
        step_bool (Eq s1 s2) Sigma pi TrueValue
    | EqFalseL :
        forall Sigma pi s1 s2 l r lp rp,
          step_sexp s1 Sigma pi (exist sexp_is_value (Cons l r)
                                       (ConsValuesIsValue lp rp)) ->
        step_sexp s2 Sigma pi EmptySetValue ->
        step_bool (Eq s1 s2) Sigma pi FalseValue
    | EqFalseR :
        forall Sigma pi s1 s2 l r lp rp,
        step_sexp s1 Sigma pi EmptySetValue ->
        step_sexp s2 Sigma pi (exist sexp_is_value (Cons l r)
                                     (ConsValuesIsValue lp rp)) ->
        step_bool (Eq s1 s2) Sigma pi FalseValue
    | EqProp :
        forall Sigma pi s1 s2 l1 l2 r1 r2 lp1 lp2 rp1 rp2 b,
          step_sexp s1 Sigma pi (exist sexp_is_value (Cons l1 r1)
                                       (ConsValuesIsValue lp1 rp1)) ->
          step_sexp s2 Sigma pi (exist sexp_is_value (Cons l2 r2)
                                       (ConsValuesIsValue lp2 rp2)) ->
        step_bool (Conj (Eq l1 l2) (Eq r1 r2)) Sigma pi b ->
        step_bool (Eq s1 s2) Sigma pi b
    | MemFalse :
        forall Sigma pi s1 s2 sv1,
          step_sexp s1 Sigma pi sv1 ->
          step_sexp s2 Sigma pi EmptySetValue ->
          step_bool (Mem s1 s2) Sigma pi FalseValue
    | MemProp :
        forall Sigma pi s1 s2 sv l r sp lp rp b,
          step_sexp s1 Sigma pi (exist sexp_is_value sv sp) ->
          step_sexp s2 Sigma pi (exist sexp_is_value (Cons l r)
                                       (ConsValuesIsValue lp rp)) ->
        step_bool (Disj (Eq sv l) (Mem sv r)) Sigma pi b ->
        step_bool (Mem s1 s2) Sigma pi b
    .


    Inductive step_com :
      com -> var_store_stack -> world_store -> principals -> location -> handlers -> mergers -> var_store -> world_store -> Prop :=
    | SkipStep :
        forall sigma Sigma omega pi rho eta mu,
          step_com Skip (cons sigma Sigma) omega pi rho eta mu sigma omega
    | SeqStep :
        forall c1 c2 sigma Sigma omega pi rho eta mu sigma' sigma'' omega' omega'',
          step_com c1 (cons sigma Sigma) omega pi rho eta mu sigma' omega' ->
          step_com c2 (cons sigma' Sigma) omega' pi rho eta mu sigma'' omega'' ->
          step_com (Seq c1 c2) (cons sigma Sigma) omega pi rho eta mu sigma'' omega''
    | IfTrueStep :
        forall b c1 c2 Sigma omega pi rho eta mu sigma' omega',
          step_bool b Sigma pi TrueValue ->
          step_com c1 Sigma omega pi rho eta mu sigma' omega' ->
          step_com (If b c1 c2) Sigma omega pi rho eta mu sigma' omega'
    | IfFalseStep :
        forall b c1 c2 Sigma omega pi rho eta mu sigma' omega',
          step_bool b Sigma pi FalseValue ->
          step_com c2 Sigma omega pi rho eta mu sigma' omega' ->
          step_com (If b c1 c2) Sigma omega pi rho eta mu sigma' omega'
    | AtStep :
        forall n c sigma Sigma omega pi rho eta mu sigma' omega',
          step_com c (cons sigma Sigma) omega pi n eta mu sigma' omega' ->
          step_com (At n c) (cons sigma Sigma) omega pi rho eta mu sigma' omega'
    | WithStep :
        forall n c Sigma omega pi rho eta mu sigma' omega',
          step_com c Sigma omega (set_add NodeMap.eq_dec_key n pi) rho eta mu sigma' omega' ->
          step_com c Sigma omega pi rho eta mu sigma' omega'
    | HandleStep :
        forall n v op sh sm c sigma Sigma omega pi rho eta eta' mu mu' sigma_int sigma' omega',
          set_env sigma n v EmptySetValue sigma_int ->
          set_handler eta op n v sh eta' ->
          set_merger mu n v sm mu' ->
          set_In n pi ->
          step_com c (cons sigma_int Sigma) omega pi rho eta' mu' sigma' omega' ->
          step_com (Handle n v op sh sm c) (cons sigma Sigma) omega pi rho eta mu sigma' omega'
    | OpStep :
        forall op sigma Sigma omega pi rho eta mu n v sh sv sigma',
          get_handler eta op n v sh ->
          step_sexp sh (cons sigma Sigma) pi sv ->
          set_env sigma n v sv sigma' ->
          step_com (Op op) (cons sigma Sigma) omega pi rho eta mu sigma' omega
    | HypStep :
        forall u c sigma Sigma omega pi rho eta mu sigma' omega',
          step_com c (cons empty_var_store (cons sigma Sigma)) empty_world_store pi rho eta mu sigma' omega' ->
          set_world_store omega u (cons sigma Sigma) sigma' omega' ->
          step_com (Hyp u c) (cons sigma Sigma) omega pi rho eta mu sigma omega'
    | CommitStep :
        get_world_store omega u Sigma_orig sigma_hyp ->
        (forall n v s,
            get_env sigma_hyp n v s ->
            get_merger mu n v s_m ->
            merge_store sigma_merge sigma_curr Sigma_curr
            get_env sigma' n v s_m_v
        ) ->
        (forall n v s s',
            ~ get_env sigma_hyp n v s ->
            get_env sigma n v s' ->
            get_env sigma' n v s'
        ) ->
        step_com (Commit u) (sigma_curr, Sigma_curr) omega pi rho eta mu sigma' omega
    .

  End BigStep.

End Opal.