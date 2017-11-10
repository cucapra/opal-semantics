Require Import ListSet CpdtTactics FSetAVL FMapAVL OrderedType.

Set Implicit Arguments.

Axiom proof_irrelevance :
  forall (P : Prop) (p q : P), p = q.

Definition eq_dec_pair {A: Type} (eq_dec : forall (a1 a2: A), {a1 = a2} + {a1 <> a2})
  : forall (aa1 aa2: A*A), {aa1 = aa2} + {aa1 <> aa2}.
Proof.
  decide equality.
Qed.
Hint Resolve eq_dec_pair.

Module OrderedPair(L R: OrderedType) <: OrderedType.
  Module LFacts := OrderedTypeFacts(L).
  Module RFacts := OrderedTypeFacts(R).

  Definition t := (L.t * R.t) % type.

  Inductive eq' : t -> t -> Prop :=
  | LeftRightEq : forall ll lr rl rr,
      L.eq ll rl ->
      R.eq lr rr ->
      eq' (ll, lr) (rl, rr).
  Definition eq := eq'.

  Inductive lt' : t -> t -> Prop :=
  | LeftLt : forall ll lr rl rr,
      L.lt ll rl ->
      lt' (ll, lr) (rl, rr)
  | RightLt : forall ll lr rl rr,
      L.eq ll rl ->
      R.lt lr rr ->
      lt' (ll, lr) (rl, rr).
  Definition lt := lt'.

  Theorem eq_refl : forall x, eq x x.
  Proof.
    unfold eq.
    specialize L.eq_refl.
    specialize R.eq_refl.
    intros.
    destruct x.
    constructor; auto.
  Qed.

  Theorem eq_sym : forall x y, eq x y -> eq y x.
  Proof.
    intros. unfold eq in *. inversion H. constructor; auto.
  Qed.

  Theorem eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    destruct x, y, z.
    intros. unfold eq in *. inversion H. inversion H0.
    specialize (L.eq_trans H4 H10).
    specialize (R.eq_trans H6 H12).
    constructor; auto.
  Qed.

  Theorem lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
    destruct x, y, z.
    intros. unfold lt in *.
    inversion H; inversion H0 ; subst.
    * specialize (L.lt_trans H2 H7). intros. constructor. auto.
    * specialize (LFacts.lt_eq H2 H9). intros. constructor. auto.
    * specialize (LFacts.eq_lt H4 H8). intros. constructor. auto.
    * constructor 2.
      - specialize (L.eq_trans H4 H10). intuition.
      - specialize (R.lt_trans H6 H12). intuition.
  Qed.

  Theorem lt_not_eq : forall x y, lt x y -> ~ eq x y.
  Proof.
    intros.
    destruct x,y.
    unfold not. intros. unfold eq in *. unfold lt in *. inversion H0.
    inversion H; subst.
    * specialize (L.lt_not_eq H8 H4). auto.
    * specialize (R.lt_not_eq H12 H6). auto.
  Qed.

  Theorem compare : forall x y, Compare lt eq x y.
  Proof.
    destruct x, y.
    destruct (L.compare t0 t2).
    * constructor 1. constructor. auto.
    * destruct (R.compare t1 t3).
      - constructor 1. constructor 2; auto.
      - constructor 2. constructor; auto.
      - constructor 3. constructor 2; auto.
    * constructor 3. constructor. auto.
  Qed.

  Theorem eq_dec : forall x y, {eq x y} + {~ eq x y}.
  Proof.
    destruct x, y.
    destruct (L.eq_dec t0 t2).
    * destruct (R.eq_dec t1 t3).
      - left. constructor; auto.
      - right. intuition. inversion H. intuition.
    * right. intuition. inversion H. intuition.
  Qed.
End OrderedPair.

Module Opal (NodeType VarType WorldVarType OpType: OrderedType).
  Module NodeVarType := OrderedPair(NodeType)(VarType).

  Module NodeMap := FMapAVL.Make(NodeType).
  Module NodeSet := FSetAVL.Make(NodeType).
  Module VarMap := FMapAVL.Make(VarType).
  Module NodeVarMap := FMapAVL.Make(NodeVarType).
  Module WorldVarMap := FMapAVL.Make(WorldVarType).
  Module OpMap := FMapAVL.Make(OpType).

  Definition node := NodeType.t.
  Definition var := VarMap.key.
  Definition worldvar := WorldVarMap.key.
  Definition op := OpMap.key.

  Inductive com :=
  | SkipCom : com
  | SeqCom : com -> com -> com
  | IfCom : bool -> com -> com -> com
  | WithCom : node -> com -> com
  | AtCom : node -> com -> com
  | HandleCom : node -> var -> op -> sexp -> var -> var -> var -> sexp -> com -> com
  | OpCom : op -> com
  | WorldAssignCom : worldvar -> world -> com
  | CommitCom : world -> com
  with
  bool :=
  | TrueBool : bool
  | FalseBool : bool
  | ConjBool : bool -> bool -> bool
  | DisjBool : bool -> bool -> bool
  | EqBool : sexp -> sexp -> bool
  | MemBool : sexp -> sexp -> bool
  with
  sexp :=
  | EmptySexp : sexp
  | ConsSexp : sexp -> sexp -> sexp
  | VarSexp : node -> var -> sexp
  | WeightSexp : world -> node -> var -> sexp
  with
  world :=
  | VarWorld : worldvar -> world
  | HypWorld : com -> world
  .

  Section Evaluation.
    Definition sigma_t := NodeVarMap.t sexp.
    Definition sigma_0 : sigma_t := NodeVarMap.empty sexp.

    Definition sigma_get (sigma: sigma_t) (n: node) (v: var) : option sexp :=
      NodeVarMap.find (n,v) sigma.
    Definition sigma_set (sigma: sigma_t) (n: node) (v: var) (s: sexp) (sigma': sigma_t) : sigma_t :=
      NodeVarMap.add (n,v) s sigma.

    Definition Sigma_t := list sigma_t.
    Fixpoint Sigma_get (Sigma: Sigma_t) (n: node) (v: var) : option sexp :=
      match Sigma with
      | nil => None
      | (cons sigma Sigma) =>
        match sigma_get sigma n v with
        | Some s => Some s
        | None => Sigma_get Sigma n v
        end
      end.

    Definition omega_t := WorldVarMap.t (sigma_t * sigma_t).
    Definition omega_0 : omega_t := WorldVarMap.empty (sigma_t * sigma_t).
    Definition omega_get (omega: omega_t) (u: worldvar) : option (sigma_t * sigma_t) :=
      WorldVarMap.find u omega.
    Definition omega_set (omega: omega_t) (u: worldvar) (sig_orig sig_hyp: sigma_t) : omega_t :=
      WorldVarMap.add u (sig_orig, sig_hyp) omega.

    Definition pi_t := NodeSet.t.
    Definition pi_mem (n: node) (pi: pi_t) : Datatypes.bool :=
      NodeSet.mem n pi.

    Definition rho_t := node.

    Definition eta_t := OpMap.t (node * var * sexp).
    Definition eta_get (eta: eta_t) (op: op) (n: node) (v: var) : option (node * var * sexp) :=
      OpMap.find op eta.
    Definition eta_set (eta: eta_t) (op: op) (n: node) (v: var) (sh: sexp) : eta_t :=
      OpMap.add op (n,v,sh) eta.

    Definition mu_t := NodeVarMap.t (var * var * var * sexp).
    Definition mu_get (mu: mu_t) (n: node) (v: var) : option (var * var * var * sexp) :=
      NodeVarMap.find (n,v) mu.
    Definition mu_set (mu: mu_t) (n: node) (v vo vh vc: var) (sm: sexp) : mu_t:=
      NodeVarMap.add(n,v) (vo,vh,vc,sm) mu.

    Fixpoint eval_sexp (s: sexp) (Sigma: Sigma_t) (omega: omega_t) (pi: pi_t) (rho: rho_t) (eta: eta_t) (mu: mu_t) : option sexp :=
      match s with
      | EmptySexp => Some EmptySexp
      | VarSexp n v =>
        if pi_mem n pi then
          Sigma_get Sigma n v
        else
          None
      | WeightSexp w n v =>
        match eval_world w Sigma omega pi rho eta mu with
        | Some (sigma_orig, sigma_hyp) =>
          sigma_get sigma_hyp n v
        | None =>
          None
        end
    | ConsSexp s1 s2 =>
      match eval_sexp s1 Sigma omega pi rho eta mu,
            eval_sexp s2 Sigma omega pi rho eta mu with
      | Some s1v, Some s2v =>
        Some (ConsSexp s1v s2v)
      | _, _ => None
      end
      end
    with
    eval_bool (b: bool) (Sigma: Sigma_t) (omega: omega_t) (pi: pi_t) (rho: rho_t) (eta: eta_t) (mu: mu_t) : option bool :=
      match b with
      | _ =>
        None
      end
    with
    eval_com (c: com) (Sigma: Sigma_t) (omega: omega_t) (pi: pi_t) (rho: rho_t) (eta: eta_t) (mu: mu_t) : option (sigma_t * omega_t) :=
      match c with
      | _ =>
        None
      end
    with
    eval_world (w: world) (Sigma: Sigma_t) (omega: omega_t) (pi: pi_t) (rho: rho_t) (eta: eta_t) (mu: mu_t) : option (sigma_t * sigma_t) :=
      match w with
      | _ =>
        None
      end
    .

    Inductive eval_sexp : sexp -> Sigma_t -> omega_t -> pi_t -> rho_t -> eta_t -> mu_t -> sexp -> Prop :=
    | EmptyEval : forall Sigma omega pi rho eta mu,
        eval_sexp EmptySexp Sigma omega pi rho eta mu EmptySexp
    | ConsEval : forall s1 s1' s2 s2' Sigma omega pi rho eta mu,
        eval_sexp s1 Sigma omega pi rho eta mu s1' ->
        eval_sexp s2 Sigma omega pi rho eta mu s2' ->
        eval_sexp (ConsSexp s1 s2) Sigma omega pi rho eta mu (ConsSexp s1' s2')
    | VarEval : forall n v s Sigma omega pi rho eta mu,
        Sigma_get Sigma n v s ->
        eval_sexp (VarSexp n v) Sigma omega pi rho eta mu s
    | WeightEval : forall w n v s sigma_orig sigma_hyp Sigma omega pi rho eta mu,
        eval_world w Sigma omega pi rho eta mu sigma_orig sigma_hyp ->
        sigma_get sigma_hyp n v s ->
        set_In n pi ->
        eval_sexp (WeightSexp w n v) Sigma omega pi rho eta mu s
    with
    eval_bool : bool -> Sigma_t -> omega_t -> pi_t -> rho_t -> eta_t -> mu_t -> bool -> Prop :=
    | TrueEval : forall Sigma omega pi rho eta mu,
        eval_bool TrueBool Sigma omega pi rho eta mu TrueBool
    | FalseEval : forall Sigma omega pi rho eta mu,
        eval_bool FalseBool Sigma omega pi rho eta mu FalseBool
    | ConjTrueEval : forall b1 b2 b2' Sigma omega pi rho eta mu,
        eval_bool b1 Sigma omega pi rho eta mu TrueBool ->
        eval_bool b2 Sigma omega pi rho eta mu b2' ->
        eval_bool (ConjBool b1 b2) Sigma omega pi rho eta mu b2'
    | ConjFalseEval : forall b1 b2 b2' Sigma omega pi rho eta mu,
        eval_bool b1 Sigma omega pi rho eta mu FalseBool ->
        eval_bool b2 Sigma omega pi rho eta mu b2' ->
        eval_bool (ConjBool b1 b2) Sigma omega pi rho eta mu FalseBool
    | DisjFalseEval : forall b1 b2 b2' Sigma omega pi rho eta mu,
        eval_bool b1 Sigma omega pi rho eta mu FalseBool ->
        eval_bool b2 Sigma omega pi rho eta mu b2' ->
        eval_bool (DisjBool b1 b2) Sigma omega pi rho eta mu b2'
    | DisjTrueEval : forall b1 b2 b2' Sigma omega pi rho eta mu,
        eval_bool b1 Sigma omega pi rho eta mu TrueBool ->
        eval_bool b2 Sigma omega pi rho eta mu b2' ->
        eval_bool (DisjBool b1 b2) Sigma omega pi rho eta mu TrueBool
    | EqTrueEval : forall s1 s2 Sigma omega pi rho eta mu,
        eval_sexp s1 Sigma omega pi rho eta mu EmptySexp ->
        eval_sexp s2 Sigma omega pi rho eta mu EmptySexp ->
        eval_bool (EqBool s1 s2) Sigma omega pi rho eta mu TrueBool
    | EqFalseLEval : forall s1 s1l s1r s2 Sigma omega pi rho eta mu,
        eval_sexp s1 Sigma omega pi rho eta mu (ConsSexp s1l s1r) ->
        eval_sexp s2 Sigma omega pi rho eta mu EmptySexp ->
        eval_bool (EqBool s1 s2) Sigma omega pi rho eta mu FalseBool
    | EqFalseREval : forall s1 s2 s2l s2r Sigma omega pi rho eta mu,
        eval_sexp s1 Sigma omega pi rho eta mu EmptySexp ->
        eval_sexp s2 Sigma omega pi rho eta mu (ConsSexp s2l s2r) ->
        eval_bool (EqBool s1 s2) Sigma omega pi rho eta mu FalseBool
    | EqPropEval : forall s1 s1l s1r s2 s2l s2r b Sigma omega pi rho eta mu,
        eval_sexp s1 Sigma omega pi rho eta mu (ConsSexp s1l s1r) ->
        eval_sexp s2 Sigma omega pi rho eta mu (ConsSexp s2l s2r) ->
        eval_bool (ConjBool (EqBool s1l s2l) (EqBool s1r s2r)) Sigma omega pi rho eta mu b ->
        eval_bool (EqBool s1 s2) Sigma omega pi rho eta mu b
    | MemFalseEval : forall s1 s1' s2 Sigma omega pi rho eta mu,
        eval_sexp s1 Sigma omega pi rho eta mu s1' ->
        eval_sexp s2 Sigma omega pi rho eta mu EmptySexp ->
        eval_bool (MemBool s1 s2) Sigma omega pi rho eta mu FalseBool
    | MemPropEval : forall s1 s1' s2 s2l s2r b Sigma omega pi rho eta mu,
        eval_sexp s1 Sigma omega pi rho eta mu s1' ->
        eval_sexp s2 Sigma omega pi rho eta mu (ConsSexp s2l s2r) ->
        eval_bool (DisjBool (EqBool s1' s2l) (MemBool s1' s2r)) Sigma omega pi rho eta mu b ->
        eval_bool (MemBool s1 s2) Sigma omega pi rho eta mu b
    with
    eval_world : world -> Sigma_t -> omega_t -> pi_t -> rho_t -> eta_t -> mu_t -> sigma_t -> sigma_t -> Prop :=
    | LookupEval : forall u sigma_orig sigma_hyp Sigma omega pi rho eta mu,
        omega_get omega u sigma_orig sigma_hyp ->
        eval_world (VarWorld u) Sigma omega pi rho eta mu sigma_orig sigma_hyp
    | HypEval : forall c sigma_hyp omega_hyp sigma Sigma omega pi rho eta mu,
        eval_com c (cons sigma_0 (cons sigma Sigma)) omega_0 pi rho eta mu sigma_hyp omega_hyp ->
        eval_world (HypWorld c) (cons sigma Sigma) omega pi rho eta mu sigma sigma_hyp
    with
    eval_com : com -> Sigma_t -> omega_t -> pi_t -> rho_t -> eta_t -> mu_t -> sigma_t -> omega_t -> Prop :=
    | SkipEval : forall sigma Sigma omega pi rho eta mu,
        eval_com SkipCom (cons sigma Sigma) omega pi rho eta mu sigma omega
    | SeqEval : forall c1 c2 sigma sigma' sigma'' Sigma omega omega' omega'' pi rho eta mu,
        eval_com c1 (cons sigma Sigma) omega pi rho eta mu sigma' omega' ->
        eval_com c2 (cons sigma' Sigma) omega' pi rho eta mu sigma'' omega'' ->
        eval_com (SeqCom c1 c2) (cons sigma Sigma) omega pi rho eta mu sigma'' omega''
    | IfTrueEval : forall b c1 c2 sigma sigma' Sigma omega omega' pi rho eta mu,
        eval_bool b (cons sigma Sigma) omega pi rho eta mu TrueBool ->
        eval_com c1 (cons sigma Sigma) omega pi rho eta mu sigma' omega' ->
        eval_com (IfCom b c1 c2) (cons sigma Sigma) omega pi rho eta mu sigma' omega'
    | IfFalseEval : forall b c1 c2 sigma' Sigma omega omega' pi rho eta mu,
        eval_bool b Sigma omega pi rho eta mu FalseBool ->
        eval_com c2 Sigma omega pi rho eta mu sigma' omega' ->
        eval_com (IfCom b c1 c2) Sigma omega pi rho eta mu sigma' omega'
    | WithEval : forall n c sigma' Sigma omega omega' pi rho eta mu,
        eval_com c Sigma omega (set_add node_eq_dec n pi) rho eta mu sigma' omega' ->
        eval_com (WithCom n c) Sigma omega pi rho eta mu sigma' omega'
    | AtEval : forall n c sigma' Sigma omega omega' pi rho eta mu,
        eval_com c Sigma omega pi n eta mu sigma' omega' ->
        eval_com (AtCom n c) Sigma omega pi rho eta mu sigma' omega'
    | HandleEval : forall n v op sh vo vh vc sm c sigma sigma' sigma'' Sigma omega omega' pi rho eta eta' mu mu',
        set_In n pi ->
        sigma_set sigma n v EmptySexp sigma' ->
        eta_set eta op n v sh eta' ->
        mu_set mu n v vo vh vc sm mu' ->
        eval_com c (cons sigma' Sigma) omega_0 pi rho eta' mu' sigma'' omega' ->
        eval_com (HandleCom n v op sh vo vh vc sm c) (cons sigma Sigma) omega pi rho eta mu sigma'' omega
    | OpEval : forall op n v sh sv sigma sigma' Sigma omega pi rho eta mu,
        eta_get eta op n v sh ->
        set_In n pi ->
        eval_sexp sh (cons sigma Sigma) omega pi rho eta mu sv ->
        sigma_set sigma n v sv sigma' ->
        eval_com (OpCom op) (cons sigma Sigma) omega pi rho eta mu sigma' omega
    | WorldAssign : forall u w sigma_orig sigma_hyp sigma Sigma omega omega' pi rho eta mu,
        eval_world w (cons sigma Sigma) omega pi rho eta mu sigma_orig sigma_hyp ->
        omega_set omega u sigma_orig sigma_hyp omega' ->
        eval_com (WorldAssignCom u w) (cons sigma Sigma) omega pi rho eta mu sigma omega'
    | CommitEval :
        forall w sigma_orig sigma_hyp sigma sigma' Sigma omega pi rho eta mu,
        eval_world w (cons sigma Sigma) omega pi rho eta mu sigma_orig sigma_hyp ->
        (forall n v vo vc vh so sc sh sm sig_c sig_co sig_coh s,
            mu_get mu n v vo vh vc sm ->
            eval_sexp (VarSexp n v) (cons sigma Sigma) omega pi rho eta mu sc ->
            sigma_set sigma_0 n vc sc sig_c ->
            eval_sexp (VarSexp n v) (cons sigma_orig Sigma) omega pi rho eta mu so ->
            sigma_set sig_c n vo so sig_co ->
            sigma_get sigma_hyp n v sh ->
            sigma_set sig_co n vh sh sig_coh ->
            eval_sexp sm (cons sig_coh Sigma) omega pi rho eta mu s ->
            sigma_get sigma' n v s
        ) ->
        (forall n v,
            (~exists s, sigma_get sigma_hyp n v s) ->
            forall s,
              sigma_get sigma n v s ->
              sigma_get sigma' n v s
        ) ->
        eval_com (CommitCom w) (cons sigma Sigma) omega pi rho eta mu sigma' omega
    .
  End Evaluation.

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