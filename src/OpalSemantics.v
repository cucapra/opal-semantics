Require Import String ListSet CpdtTactics.

Definition var := string.
Definition world := string.

Inductive sexp :=
| EmptySet : sexp
| Var      : var -> sexp
| Cons     : sexp -> sexp -> sexp
| Extend   : sexp -> sexp -> sexp.

Inductive sexp_is_value : sexp -> Prop :=
| EmptySetIsValue : sexp_is_value EmptySet
| ConsValuesIsValue : forall s1 s2,
    sexp_is_value s1 -> sexp_is_value s2 -> sexp_is_value (Cons s1 s2).

Definition sexp_value := {s: sexp | sexp_is_value s}.

Inductive sexp_evaluation_context :=
| SexpHole : sexp_evaluation_context
| ConsLeft : sexp_evaluation_context -> sexp -> sexp_evaluation_context
| ConsRight : sexp_value -> sexp_evaluation_context -> sexp_evaluation_context
| ExtendLeft : sexp_evaluation_context -> sexp -> sexp_evaluation_context
| ExtendRight : sexp_value -> sexp_evaluation_context -> sexp_evaluation_context.

Fixpoint sexp_of_context (ctx: sexp_evaluation_context) (s: sexp) :=
  match ctx with
  | SexpHole => s
  | ConsLeft ctx' r => Cons (sexp_of_context ctx' s) r
  | ConsRight l ctx' => Cons (proj1_sig l) (sexp_of_context ctx' s)
  | ExtendLeft ctx' r => Extend (sexp_of_context ctx' s) r
  | ExtendRight l ctx' => Extend (proj1_sig l) (sexp_of_context ctx' s)
  end.

Inductive bool :=
| Eq : sexp -> sexp -> bool
| Mem : sexp -> sexp -> bool
| Conj : bool -> bool -> bool
| Disj : bool -> bool -> bool
| True : bool
| False : bool.

Definition bool_value := {b: bool | b = True \/ b = False}.

Inductive bool_sexp_evaluation_context :=
| BoolSexpMemLeft : sexp -> bool_sexp_evaluation_context
| BoolSexpMemRight : sexp_value -> bool_sexp_evaluation_context
| BoolSexpEqLeft : sexp -> bool_sexp_evaluation_context
| BoolSexpEqRight : sexp_value -> bool_sexp_evaluation_context
| BoolSexpConjLeft : bool_sexp_evaluation_context -> bool -> bool_sexp_evaluation_context
| BoolSexpConjRight : bool_value -> bool_sexp_evaluation_context -> bool_sexp_evaluation_context
| BoolSexpDisjLeft : bool_sexp_evaluation_context -> bool -> bool_sexp_evaluation_context
| BoolSexpDisjRight : bool_value -> bool_sexp_evaluation_context -> bool_sexp_evaluation_context.

Fixpoint bool_of_bool_sexp_context (ctx: bool_sexp_evaluation_context) (s: sexp) :=
  match ctx with
  | BoolSexpMemLeft r => Mem s r
  | BoolSexpMemRight lvp => Mem (proj1_sig lvp) s
  | BoolSexpEqLeft r => Eq s r
  | BoolSexpEqRight lvp => Eq (proj1_sig lvp) s
  | BoolSexpConjLeft ctx' r => Conj (bool_of_bool_sexp_context ctx' s) r
  | BoolSexpConjRight lvp ctx' => Conj (proj1_sig lvp) (bool_of_bool_sexp_context ctx' s)
  | BoolSexpDisjLeft ctx' r => Disj (bool_of_bool_sexp_context ctx' s) r
  | BoolSexpDisjRight lvp ctx' => Disj (proj1_sig lvp) (bool_of_bool_sexp_context ctx' s)
  end.

Inductive bool_evaluation_context :=
| BoolHole : bool_evaluation_context
| ConjLeft : bool_evaluation_context -> bool -> bool_evaluation_context
| ConjRight : bool_value -> bool_evaluation_context -> bool_evaluation_context
| DisjLeft : bool_evaluation_context -> bool -> bool_evaluation_context
| DisjRight : bool_value -> bool_evaluation_context -> bool_evaluation_context.

Fixpoint bool_of_bool_context (ctx: bool_evaluation_context) (b: bool) :=
  match ctx with
  | BoolHole => b
  | ConjLeft ctx' r => Conj (bool_of_bool_context ctx' b) r
  | ConjRight lvp ctx' => Conj (proj1_sig lvp) (bool_of_bool_context ctx' b)
  | DisjLeft ctx' r => Disj (bool_of_bool_context ctx' b) r
  | DisjRight lvp ctx' => Disj (proj1_sig lvp) (bool_of_bool_context ctx' b)
  end.

Inductive com :=
| Skip : com
| If : bool -> com -> com -> com
| Assign : var -> sexp -> com
| Seq : com -> com -> com
| Print : sexp -> com
| Hyp : world -> com -> com
| Commit : world -> com.

Definition env := var -> nat -> sexp_value.
Definition empty_env : env := (fun var idx => (exist _ EmptySet EmptySetIsValue)).
Definition set_env (e: env) (v: var) (i: nat) (s: sexp_value) : env :=
  fun var idx => match (string_dec var v, Nat.eqb idx i) with
                 | (left _, true) => s
                 | _ => e var idx
                 end.
Definition get_env (e: env) (v: var) (i: nat) : sexp_value := e v i.

Inductive Env : Set :=
| BaseEnv : Env
| RecEnv : Env -> world -> env -> Env -> sexp_value -> Env.
Definition empty_Env : Env := BaseEnv.
Definition set_Env (E: Env) (w: world) (e: env) (child_E: Env) (p: sexp_value) : Env :=
  RecEnv E w e child_E p.

Record EnvRes : Set :=
  mkEnvRes {
      getSigma    : env;
      getEnvSigma : Env;
      getEnvPrint : sexp_value
    }.

Fixpoint get_Env (E: Env) (w: world) : EnvRes :=
  match E with
  | BaseEnv => mkEnvRes empty_env  empty_Env (exist _ EmptySet EmptySetIsValue)
  | RecEnv rest m_world m_e m_E p =>
    match string_dec w m_world with
    | left _ => mkEnvRes m_e m_E p
    | right _ => get_Env rest w
    end
  end.

Inductive sexp_step : sexp -> env -> nat -> sexp -> Prop :=
| VarZeroStep : forall (sigma: env) (v: var),
    sexp_step (Var v) sigma 0 (proj1_sig (sigma v 0))
| VarGtStep : forall (sigma: env) (i: nat) (v: var) (s1 s2: sexp),
    i > 0 -> (proj1_sig (sigma v i)) = s1 -> sexp_step (Var v) sigma (i - 1) s2 ->
    sexp_step (Var v) sigma i (Extend s1 s2)
| NullExtendStep : forall (sigma: env) (i: nat) (svp: sexp_value),
    let sv := proj1_sig svp in
    sexp_step (Extend EmptySet sv) sigma i sv
| ExtendStep : forall (sigma: env) (i: nat) (svp1 svp2 svp3: sexp_value),
    let sv1 := proj1_sig svp1 in
    let sv2 := proj1_sig svp2 in
    let sv3 := proj1_sig svp3 in
    sexp_step (Extend (Cons sv1 sv2) sv3) sigma i (Cons sv1 (Extend sv2 sv3))
| ContextSexp : forall (sigma: env) (i: nat) (ctx: sexp_evaluation_context) (s s': sexp),
    sexp_step s sigma i s' ->
    sexp_step (sexp_of_context ctx s) sigma i (sexp_of_context ctx s').

Inductive bool_step : bool -> env -> nat -> bool -> Prop :=
| MemEmpty : forall (sigma: env) (i: nat) (svp: sexp_value),
    let sv := proj1_sig svp in
    bool_step (Mem sv EmptySet) sigma i False
| MemCons : forall (sigma: env) (i: nat) (svp1 svp2 svp3: sexp_value),
    let sv1 := proj1_sig svp1 in
    let sv2 := proj1_sig svp2 in
    let sv3 := proj1_sig svp3 in
    bool_step (Mem sv1 (Cons sv2 sv3)) sigma i (Disj (Eq sv1 sv2) (Mem sv1 sv3))
| EqEmpty : forall (sigma: env) (i: nat),
    bool_step (Eq EmptySet EmptySet) sigma i True
| EqCons : forall (sigma: env) (i: nat) (svp1 svp2 svp1' svp2': sexp_value),
    let sv1 := proj1_sig svp1 in
    let sv2 := proj1_sig svp2 in
    let sv1' := proj1_sig svp1' in
    let sv2' := proj1_sig svp2' in
    bool_step (Eq (Cons sv1 sv2) (Cons sv1' sv2')) sigma i (Conj (Eq sv1 sv1') (Eq sv2 sv2'))
| EqNotL : forall (sigma: env) (i: nat) (svp1 svp2: sexp_value),
    let sv1 := proj1_sig svp1 in
    let sv2 := proj1_sig svp2 in
    bool_step (Eq (Cons sv1 sv2) EmptySet) sigma i False
| EqNotR : forall (sigma: env) (i: nat) (svp1 svp2: sexp_value),
    let sv1 := proj1_sig svp1 in
    let sv2 := proj1_sig svp2 in
    bool_step (Eq EmptySet (Cons sv1 sv2)) sigma i False
| ConjTrue: forall (sigma: env) (i: nat) (bvp: bool_value),
    let bv := proj1_sig bvp in
    bool_step (Conj True bv) sigma i bv
| ConjFalse: forall (sigma: env) (i: nat) (bvp: bool_value),
    let bv := proj1_sig bvp in
    bool_step (Conj False bv) sigma i False
| DisjTrue: forall (sigma: env) (i: nat) (bvp: bool_value),
    let bv := proj1_sig bvp in
    bool_step (Disj True bv) sigma i True
| DisjFalse: forall (sigma: env) (i: nat) (bvp: bool_value),
    let bv := proj1_sig bvp in
    bool_step (Disj False bv) sigma i bv
| ContextBoolSexp : forall (sigma: env) (i: nat) (ctx: bool_sexp_evaluation_context) (s s': sexp),
    sexp_step s sigma i s' ->
    bool_step (bool_of_bool_sexp_context ctx s) sigma i (bool_of_bool_sexp_context ctx s')
| ContextBoolBool : forall (sigma: env) (i: nat) (ctx: bool_evaluation_context) (b b': bool),
    bool_step b sigma i b' ->
    bool_step (bool_of_bool_context ctx b) sigma i (bool_of_bool_context ctx b').

Inductive com_step : com -> env -> nat -> Env -> com -> env -> Env -> option sexp_value -> Prop :=
| SeqStep : forall (sigma: env) (i: nat) (Sigma: Env) (c: com),
    com_step (Seq Skip c) sigma i Sigma c sigma Sigma None
| SeqProp : forall (sigma sigma': env) (i: nat) (Sigma Sigma': Env) (c1 c1' c2: com) (p: option sexp_value),
    com_step c1 sigma i Sigma c1' sigma' Sigma' p ->
    com_step (Seq c1 c2) sigma i Sigma (Seq c1' c2) sigma' Sigma' p
| PrintStep : forall (sigma: env) (i: nat) (Sigma: Env) (svp: sexp_value),
    let sv := proj1_sig svp in
    com_step (Print sv) sigma i Sigma Skip sigma Sigma (Some svp)
| PrintProp : forall (sigma: env) (i: nat) (Sigma: Env) (s s': sexp),
    sexp_step s sigma i s' ->
    com_step (Print s) sigma i Sigma (Print s') sigma Sigma None
| IfTrue : forall (sigma: env) (i: nat) (Sigma: Env) (c1 c2: com),
    com_step (If True c1 c2) sigma i Sigma c1 sigma Sigma None
| IfFalse : forall (sigma: env) (i: nat) (Sigma: Env) (c1 c2: com),
    com_step (If False c1 c2) sigma i Sigma c2 sigma Sigma None
| IfProp : forall (sigma: env) (i: nat) (Sigma: Env) (c1 c2: com) (b b': bool),
    bool_step b sigma i b' ->
    com_step (If b c1 c2) sigma i Sigma (If b' c1 c2) sigma Sigma None
| Assgn : forall (sigma: env) (i: nat) (Sigma: Env) (v: var) (svp: sexp_value),
    let sv := proj1_sig svp in
    let svph := proj2_sig svp in
    let prev := sigma v i in
    let prevv := proj1_sig prev in
    let prevp := proj2_sig prev in

    let new : sexp_value := exist _ (Cons sv prevv) (ConsValuesIsValue _ _ svph prevp) in

    com_step (Assign v sv) sigma i Sigma Skip (set_env sigma v i new) Sigma None
| AssgnProp : forall (sigma: env) (i: nat) (Sigma: Env) (v: var) (s s': sexp),
    sexp_step s sigma i s' ->
    com_step (Assign v s) sigma i Sigma (Assign v s') sigma Sigma None
| HypSkip : forall (sigma: env) (i: nat) (Sigma: Env) (w: world),
    com_step (Hyp w Skip) sigma i Sigma Skip sigma Sigma None
| HypProp : forall (sigma sigma_h': env) (i: nat) (Sigma Sigma_h': Env) (w: world) (c c': com) (p: option sexp_value),
    let res := get_Env Sigma w in
    let sigma_h := getSigma res in
    let Sigma_h := getEnvSigma res in
    let p_h := getEnvPrint res in

    let p_hs := proj1_sig p_h in
    let p_hp := proj2_sig p_h in

    com_step c sigma_h (i + 1) Sigma_h c' sigma_h' Sigma_h' p ->
    let p_h' :=
        match p with
        | None => exist _ p_hs p_hp
        | Some (exist _ ps pp) =>
          exist _ (Cons ps p_hs) (ConsValuesIsValue _ _ pp p_hp)
        end
    in
    let Sigma' := set_Env Sigma w sigma_h' Sigma_h' p_h' in

    com_step (Hyp w c) sigma i Sigma (Hyp w c') sigma Sigma' None
| CommitVars : forall (sigma: env) (i: nat) (Sigma: Env) (w: world) (s1 s2: sexp_value) (v: var),
    let sv1 := proj1_sig s1 in
    let sp1 := proj2_sig s1 in
    let sv2 := proj1_sig s2 in
    let sp2 := proj2_sig s2 in

    let cons_value := exist _ (Cons sv1 sv2) (ConsValuesIsValue _ _ sp1 sp2) in

    sigma v (i + 1) = cons_value ->
    let res := get_Env Sigma w in
    let sigma_h := getSigma res in
    let Sigma_h := getEnvSigma res in
    let p_h := getEnvPrint res in

    let sigma_h' := set_env sigma_h v (i + 1) s2 in
    let Sigma' := set_Env Sigma w sigma_h' Sigma_h p_h in
    com_step (Commit w) sigma i Sigma (Seq (Assign v sv1) (Commit w)) sigma Sigma' None
| CommitPrints : forall (sigma: env) (i: nat) (Sigma: Env) (w: world) (s1 s2: sexp_value),
    let sv1 := proj1_sig s1 in
    let sp1 := proj2_sig s1 in
    let sv2 := proj1_sig s2 in
    let sp2 := proj2_sig s2 in

    let res := get_Env Sigma w in
    let sigma_h := getSigma res in
    let Sigma_h := getEnvSigma res in
    let p_h := getEnvPrint res in

    p_h = (exist _ (Cons sv1 sv2) (ConsValuesIsValue _ _ sp1 sp2)) ->

    let Sigma' := set_Env Sigma w sigma_h Sigma_h s2 in

    forall (v: var), (proj1_sig (sigma_h v (i + 1))) = EmptySet ->
                     com_step (Commit w) sigma i Sigma
                              (Seq (Print sv1) (Commit w)) sigma Sigma' None

| CommitDone : forall (sigma: env) (i: nat) (Sigma: Env) (w: world),
    let res := get_Env Sigma w in
    let sigma_h := getSigma res in
    let Sigma_h := getEnvSigma res in
    let p_h := getEnvPrint res in

    p_h = (exist _ EmptySet EmptySetIsValue) ->
    forall (v: var), (proj1_sig (sigma_h v (i + 1))) = EmptySet ->
                     com_step (Commit w) sigma i Sigma
                              (Skip) sigma Sigma None.
