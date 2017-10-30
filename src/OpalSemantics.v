Require Import String ListSet CpdtTactics ListSet Wf FMapList
        Coq.Structures.OrderedTypeEx String.

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

Definition sexp_value := {sexp | sexp_is_value sexp}.

Inductive bool :=
| Eq    : sexp -> sexp -> bool
| Mem   : sexp -> sexp -> bool
| Conj  : bool -> bool -> bool
| Disj  : bool -> bool -> bool
| True  : bool
| False : bool.

Inductive bool_is_psuedovalue : bool -> Prop :=
| TruePsuedoValue : bool_is_psuedovalue True
| FalsePsuedoValue : bool_is_psuedovalue False
| MemPsuedoValue : forall l r, sexp_is_value l -> sexp_is_value r ->
                               bool_is_psuedovalue (Mem l r)
| EqPsuedoValue : forall l r, sexp_is_value l -> sexp_is_value r ->
                              bool_is_psuedovalue (Eq l r)
| ConjPsuedoValue : forall l r, bool_is_psuedovalue l -> bool_is_psuedovalue r ->
                                bool_is_psuedovalue (Conj l r)
| DisjPsuedoValue : forall l r, bool_is_psuedovalue l -> bool_is_psuedovalue r ->
                                bool_is_psuedovalue (Disj l r).
Hint Constructors bool_is_psuedovalue.

Definition bool_psuedovalue := { b: bool | bool_is_psuedovalue b}.
Definition bool_value := { b: bool | b = True \/ b = False}.

Inductive com :=
| Skip   : com
| Seq    : com -> com -> com
| If     : bool -> com -> com -> com
| With   : node -> com -> com
| At   : node -> com -> com
| Hyp    : world -> com -> com
| Commit : world -> com
| Handle : node -> var -> op -> sexp -> sexp -> com -> com
| Op     : op -> com.

Check Compare_dec.lt_eq_lt_dec.

Fixpoint string_lt (l r: string) : Prop :=
  match l, r with
  | EmptyString, EmptyString => Logic.False
  | EmptyString, _ => Logic.True
  | String lh lr, String rh rr =>
    match Compare_dec.lt_eq_lt_dec (Ascii.nat_of_ascii lh) (Ascii.nat_of_ascii rh) with
    | inleft (left _) => Logic.True
    | inleft (right _) => string_lt lr rr
    | inright _ => Logic.False
    end
  | _, _ => Logic.False
  end.

Module String_as_OT <: UsualOrderedType.

  Definition t := string.

  Definition eq := @eq string.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt := string_lt.

  Lemma lt_trans : forall x y z : t, string_lt x y -> string_lt y z -> string_lt x z.
  Proof.
    intros x.
    induction x; intros ; destruct z; crush; destruct y; crush.
    specialize IHx with y z.
    do 3 (edestruct Compare_dec.lt_eq_lt_dec; crush).
    destruct s, s0; crush.
    destruct s, s0; crush.
  Qed.

  Lemma lt_not_eq : forall x y : t, string_lt x y -> ~ eq x y.
  Proof.
    intros x.
    induction x ; destruct y ; crush.
    edestruct Compare_dec.lt_eq_lt_dec; crush.
    unfold eq in H0.
    destruct s. crush.
    specialize IHx with y.
    crush.
  Qed.

  Definition compare x y : OrderedType.Compare string_lt eq x y.
  Proof.
    generalize y.
    clear y.
    induction x; intros.
    * destruct y.
      - assert (eq "" "").
        crush.
        constructor 2. auto.
      - constructor 1. crush.
    * destruct y.
      - constructor 3. crush.
      - remember (Ascii.nat_of_ascii a) as an.
        remember (Ascii.nat_of_ascii a0) as a0n.
        specialize Ascii.ascii_nat_embedding with a.
        specialize Ascii.ascii_nat_embedding with a0.
        intros.
        specialize IHx with y.
        destruct Compare_dec.lt_eq_lt_dec with an a0n ;
          try (destruct s) ;
          inversion IHx;
          [> constructor 1 ..
          | constructor 2
          | constructor 3
          | constructor 3
          | constructor 3
          | constructor 3 ] ;
          crush ;
          edestruct Compare_dec.lt_eq_lt_dec;
          crush.
  Qed.

  Definition eq_dec := string_dec.

End String_as_OT.

Module NodeVar_OT := PairOrderedType String_as_OT String_as_OT.
Module NodeVarMap := FMapList.Make(NodeVar_OT).

Definition var_store := NodeVarMap.t sexp_value.
Definition var_store_stack := list var_store.
Definition world_store := world -> option (var_store_stack * var_store).
Definition principals := set node.
Definition location := node.
Definition handlers := op -> option (node * var * sexp).
Definition mergers := node -> var -> option sexp.

Definition empty_env : var_store := NodeVarMap.empty sexp_value.

Definition set_env (e: var_store) (n: node) (v: var) (val: sexp_value) : var_store :=
  NodeVarMap.add (n, v) val e.

Definition get_env (e: var_store) (n: node) (v: var) : option sexp_value :=
  NodeVarMap.find (n, v) e.

Fixpoint lookup (env: var_store_stack) (n: node) (v: var) :=
  match env with
  | nil => None
  | cons e rest =>
    match get_env e n v with
    | Some res => Some res
    | None => lookup rest n v
    end
  end.

Definition empty_world_store : world_store :=
  fun _ => None.

Definition set_world_store (w: world_store) (u: world) (S: var_store_stack) (s: var_store) : world_store :=
  fun u' =>
    match string_dec u u' with
    | left _ => Some (S, s)
    | right _ => w u'
    end.

Definition empty_handlers : handlers :=
  fun _ => None.

Definition set_handler (h: handlers) (o: op) (n: node) (v: var) (s: sexp) : handlers :=
  fun o' =>
    match string_dec o o' with
    | left _ => Some (n, v, s)
    | right _ => h o'
    end.

Definition empty_mergers : mergers :=
  fun _ _ => None.

Definition set_merger (m: mergers) (n: node) (v: var) (s: sexp) : mergers :=
  fun n' v' =>
    match (string_dec n n', string_dec v v') with
    | (left _, left _) => Some s
    | _ => m n' v'
    end.

Program Fixpoint sexp_step (s: sexp) (env: var_store_stack) (pi: principals) : option sexp_value :=
  match s with
  | EmptySet => Some EmptySet
  | Cons l r =>
    match sexp_step l env pi, sexp_step r env pi with
    | Some lv, Some rv =>
      Some (Cons lv rv)
    | _, _ => None
    end
  | Var n v =>
    match set_mem string_dec n pi with
    | true => lookup env n v
    | false => None
    end
  end.
Next Obligation.
eapply ConsValuesIsValue; destruct (_: sexp_value); auto.
Defined.

Inductive bool_wf_rel : bool -> bool -> Prop :=
| ConjWfL : forall (a b: bool), bool_wf_rel a (Conj a b)
| ConjWfR : forall (a b: bool), bool_wf_rel b (Conj a b)
| DisjWfL : forall (a b: bool), bool_wf_rel a (Disj a b)
| DisjWfR : forall (a b: bool), bool_wf_rel b (Disj a b)
| TrueWf : forall a, a <> True -> bool_wf_rel True a
| FalseWf : forall a, a <> False -> bool_wf_rel False a
| EqLtMem : forall elem elemv list env pi vl vr p1 p2,
    sexp_step list env pi = Some (exist sexp_is_value (Cons vl vr) p1) ->
    sexp_step elem env pi = Some (exist sexp_is_value elemv p2) ->
    bool_wf_rel (Eq elemv vl) (Mem elem list)
| MemLtMem : forall elem elemv list env pi vl vr p1 p2,
    sexp_step list env pi = Some (exist sexp_is_value (Cons vl vr) p1) ->
    sexp_step elem env pi = Some (exist sexp_is_value elemv p2) ->
    bool_wf_rel (Mem elemv vr) (Mem elem list)
| EqLtEqL : forall l r ll lr rl rr env pi p1 p2,
    sexp_step l env pi = Some (exist sexp_is_value (Cons ll lr) p1) ->
    sexp_step r env pi = Some (exist sexp_is_value (Cons rl rr) p2) ->
    bool_wf_rel (Eq ll rl) (Eq l r)
| EqLtEqR : forall l r ll lr rl rr env pi p1 p2,
    sexp_step l env pi = Some (exist sexp_is_value (Cons ll lr) p1) ->
    sexp_step r env pi = Some (exist sexp_is_value (Cons rl rr) p2) ->
    bool_wf_rel (Eq lr rr) (Eq l r).
Hint Constructors bool_wf_rel.

Fixpoint measure_sexp_value (s: sexp) :=
  match s with
  | EmptySet => 1
  | Var _ _ => 1
  | Cons l r =>
    measure_sexp_value l +
    measure_sexp_value r
  end.

Theorem measure_sexp_value_positive : forall s, measure_sexp_value s > 0.
Proof.
  induction s; crush.
Qed.

Fixpoint measure_bool_psuedovalue (b: bool) :=
  match b with
  | True => 0
  | False => 0
  | Conj l r => 1 + measure_bool_psuedovalue l + measure_bool_psuedovalue r
  | Disj l r => 1 + measure_bool_psuedovalue l + measure_bool_psuedovalue r
  | Mem l r => 1 + measure_sexp_value l + measure_sexp_value r
  | Eq l r => 1 + measure_sexp_value l + measure_sexp_value r
  end.

Program Fixpoint bool_psuedovalue_step (b: bool_psuedovalue) (env: var_store_stack) (pi: principals) {measure (measure_bool_psuedovalue b)} : option bool_value :=
  match b with
  | True => Some True
  | False => Some False
  | Eq EmptySet EmptySet => Some True
  | Eq (Cons ll lr) (Cons rl rr) =>
    match bool_psuedovalue_step (Eq ll rl) env pi as leq,
          bool_psuedovalue_step (Eq lr rr) env pi as req with
    | (Some (exist _ True _)), (Some (exist _ True _)) => Some True
    | Some _, Some _ => Some False
    | _, _ => None
    end
  | Eq (Var _ _) _ => None
  | Eq _ (Var _ _) => None
  | Eq _ _ => Some False
  | Mem (Var _ _) _ => None
  | Mem _ (Var _ _) => None
  | Mem _ EmptySet => Some False
  | Mem l (Cons rl rr) =>
    match bool_psuedovalue_step (Eq l rl) env pi as leq,
          bool_psuedovalue_step (Mem l rr) env pi as rmem with
    | (Some (exist _ False _)), (Some (exist _ False _)) => Some False
    | Some _, Some _ => Some True
    | _, _ => None
    end
  | Conj l r =>
    match bool_psuedovalue_step l env pi as lv,
          bool_psuedovalue_step l env pi as rv with
    | (Some (exist _ True _)), (Some (exist _ True _)) => Some True
    | Some _, Some _ => Some False
    | _, _ => None
    end
  | Disj l r =>
    match bool_psuedovalue_step l env pi as lv,
          bool_psuedovalue_step l env pi as rv with
    | Some (exist _ False _), Some (exist _ False _) => Some False
    | Some _, Some _ => Some True
    | _, _ => None
    end
  end.
Ltac pseudovalue_prover b :=
  (
    destruct b;
    inversion b; crush;
    constructor;
    inversion H; eauto;
    inversion H0; eauto
  ).

Solve All Obligations with (pseudovalue_prover b).

Ltac arith_prover :=
  crush;
  match goal with
  | [H1: sexp, H2: sexp, H3: sexp |- _] =>
    specialize measure_sexp_value_positive with H1;
    specialize measure_sexp_value_positive with H2;
    specialize measure_sexp_value_positive with H3;
    crush
  end.
Obligation Tactic := Tactics.program_simpl; intros; arith_prover.
Solve Obligations.
Obligation Tactic := Tactics.program_simpl.

Program Fixpoint bool_to_psuedovalue (b: bool) (env: var_store_stack) (pi: principals) : option bool_psuedovalue :=
  match b with
  | True => Some True
  | False => Some False
  | Conj l r =>
    match bool_to_psuedovalue l env pi, bool_to_psuedovalue r env pi with
    | Some lv, Some rv => Some (Conj lv rv)
    | _, _ => None
    end
  | Disj l r =>
    match bool_to_psuedovalue l env pi, bool_to_psuedovalue r env pi with
    | Some lv, Some rv => Some (Disj lv rv)
    | _, _ => None
    end
  | Eq l r =>
    match sexp_step l env pi, sexp_step r env pi with
    | Some lv, Some rv => Some (Eq lv rv)
    | _, _ => None
    end
  | Mem l r =>
    match sexp_step l env pi, sexp_step r env pi with
    | Some lv, Some rv => Some (Mem lv rv)
    | _, _ => None
    end
  end.
Next Obligation.
  destruct b1.
  destruct b0.
  crush.
Defined.
Next Obligation.
  destruct b1.
  destruct b0.
  crush.
Defined.
Next Obligation.
  destruct lv.
  destruct rv.
  crush.
Defined.
Next Obligation.
  destruct lv.
  destruct rv.
  crush.
Defined.

Inductive result : Type -> Type :=
  fun typ => {typ} + {string}.

Definition bool_step (b: bool) (env: var_store_stack) (pi: principals) : option bool_value :=
  match bool_to_psuedovalue b env pi with
  | Some bv => bool_psuedovalue_step bv env pi
  | None => None
  end.

Open Scope string_scope.

Definition merge_variable (Sig_o Sig_t: var_store_stack) (pi: principals) (mu: mergers) (key: node*var) (hval: sexp_value) (optsig: option var_store) : option var_store :=
  let (n, v) := key in
  let orig_var := lookup Sig_o n v in
  let curr_var := lookup Sig_t n v in
  let sho := mu n v in
  match optsig, orig_var, curr_var, sho with
  | Some acc, Some oval, Some cval, Some sh =>
    let hsig := set_env empty_env "scratch" "hypo" hval in
    let osig := set_env hsig "scratch" "orig" oval in
    let csig := set_env osig "scratch" "curr" cval in
    match sexp_step sh (cons csig Sig_t) pi with
    | Some val =>
      Some (set_env acc n v val)
    | None => None
    end
  | Some acc, _, _, _ => Some acc
  | _, _, _, _ => None
  end.

Fixpoint com_step (c: com) (sigma: var_store) (Sigma: var_store_stack) (omega: world_store) (pi: principals) (rho: location) (eta: handlers) (mu: mergers) : option (var_store * world_store) :=
  match c with
  | Skip => Some (sigma, omega)
  | Seq l r =>
    match com_step l sigma Sigma omega pi rho eta mu with
    | Some (sigma', omega') =>
      com_step r sigma' Sigma omega' pi rho eta mu
    | None => None
    end
  | If b t f =>
    match bool_step b (cons sigma Sigma) pi as b' with
    | Some (exist _ True _) => com_step t sigma Sigma omega pi rho eta mu
    | Some (exist _ False _) => com_step f sigma Sigma omega pi rho eta mu
    | _ => None
    end
  | With n c' =>
    com_step c' sigma Sigma omega (cons n pi) rho eta mu
  | At n c' =>
    com_step c' sigma Sigma omega pi n eta mu
  | Handle n v op sh sm c' =>
    let eta' := set_handler eta op n v sh in
    let mu' := set_merger mu n v sm in
    com_step c' sigma Sigma omega pi rho eta' mu'
  | Op op =>
    match eta op with
    | Some (n, v, s) =>
      match sexp_step s (cons sigma Sigma) pi with
      | Some s' =>
        match set_mem string_dec n pi with
        | true =>
          let sigma' := set_env sigma n v s' in
          Some (sigma', omega)
        | false =>
          None
        end
      | None => None
      end
    | None => None
    end
  | Hyp w c =>
    match com_step c empty_env (cons sigma Sigma) empty_world_store pi rho eta mu with
    | Some (sigma', omega') =>
      let omega'' := set_world_store omega w (cons sigma Sigma) sigma' in
      Some (sigma, omega')
    | None => None
    end
  | Commit w =>
    match omega w with
    | Some (Sigma_o, sigma_h) =>
      let merge_fold := (merge_variable Sigma_o (cons sigma Sigma) (cons "scratch" pi) mu) in
      match NodeVarMap.fold merge_fold sigma_h (Some sigma) with
      | Some sigma' => Some (sigma', omega)
      | None => None
      end
    | None => None
    end
  end.


Definition run (c: com) :=
  match com_step c empty_env nil empty_world_store nil "" empty_handlers empty_mergers with
  | Some (sigma, omega) => Some sigma
  | None => None
  end.

Definition test_com := (With "Alice" (Seq (Handle "alice" "times" "%tmp" (Cons EmptySet (Cons EmptySet (Cons EmptySet (Cons EmptySet EmptySet)))) EmptySet (Op "%tmp")) (With "Bob" (Seq (Handle "bob" "times" "%tmp" (Cons EmptySet (Cons EmptySet (Cons EmptySet (Cons EmptySet EmptySet)))) EmptySet (Op "%tmp")) (With "Alice" (Seq (Handle "alice" "fitness" "%tmp" EmptySet EmptySet (Op "%tmp")) (Handle "alice" "fitness" "set_fitness" (Cons (Var "alice" "fitness") (Var "bob" "fitness")) (Cons (Var "scratch" "orig") (Cons (Var "scratch" "hypo") (Var "scratch" "curr"))) (Hyp "world" (Seq (At "DataCenter" (With "Bob" (Op "set_fitness"))) (Commit "world")))))))))).

Eval compute in (run test_com).