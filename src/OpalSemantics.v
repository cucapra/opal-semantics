Require Import CpdtTactics Structures.OrderedType FMapAVL FMapFacts Setoid Morphisms Wf.

Set Implicit Arguments.

Axiom proof_irrelevance :
  forall (P : Prop) (p q : P), p = q.


Module Opal (NodeType VarType WorldVarType: OrderedType.OrderedType).
  Module NodeVarType : OrderedType.OrderedType with
        Definition t := (NodeType.t * VarType.t)%type
    := OrderedTypeEx.PairOrderedType(NodeType)(VarType).
  Module WorldNodeVarType : OrderedType.OrderedType with
        Definition t := (WorldVarType.t * NodeVarType.t)%type
    := OrderedTypeEx.PairOrderedType(WorldVarType)(NodeVarType).

  Module NodeMap : FMapInterface.WS with Module E := NodeType :=
    FMapAVL.Make(NodeType).
  Module NodeMapFacts := FMapFacts.Properties(NodeMap).

  Module NodeVarMap : FMapInterface.WS with Module E := NodeVarType :=
    FMapAVL.Make(NodeVarType).
  Module NodeVarMapFacts := FMapFacts.Properties(NodeVarMap).

  Module WorldVarMap : FMapInterface.WS with Module E := WorldVarType :=
    FMapAVL.Make(WorldVarType).
  Module WorldVarMapFacts := FMapFacts.Properties(WorldVarMap).

  Definition node := NodeType.t.
  Definition var := VarType.t.
  Definition worldvar := WorldVarType.t.

  Inductive com :=
  | SkipCom : com
  | SeqCom : com -> com -> com
  | IfCom : bool -> com -> com -> com
  | WithCom : node -> com -> com
  | AtCom : node -> com -> com
  | WorldAssignCom : worldvar -> com -> com
  | CommitCom : worldvar -> com
  with
  sexp :=
  | EmptySexp : sexp
  | VarSexp : node -> var -> sexp
  | WeightSexp : worldvar -> node -> var -> sexp
  | ConsSexp : sexp -> sexp -> sexp
  with
  bool :=
  | TrueBool : bool
  | FalseBool : bool
  | ConjBool : bool -> bool -> bool
  | DisjBool : bool -> bool -> bool
  | EqBool : sexp -> sexp -> bool
  | MemBool : sexp -> sexp -> bool
  .

  Inductive bool_is_value : bool -> Prop :=
  | TrueBoolIsValue : bool_is_value TrueBool
  | FalseBoolIsValue : bool_is_value FalseBool
  .
  Hint Constructors bool_is_value.

  Definition bool_value := { b: bool | bool_is_value b }.

  Inductive sexp_is_value : sexp -> Prop :=
  | EmptySexpIsValue : sexp_is_value EmptySexp
  | ConsSexpIsValue : forall l r,
      sexp_is_value l -> sexp_is_value r -> sexp_is_value (ConsSexp l r)
  .
  Hint Constructors sexp_is_value.

  Definition sexp_value := { s: sexp | sexp_is_value s }.

  Section Evaluation.
    Definition sigma_t : Type := NodeVarMap.t sexp_value.
    Definition sigma_0 : sigma_t := NodeVarMap.empty sexp_value.
    Definition sigma_get (sigma: sigma_t) (n: node) (v: var) : option sexp_value :=
      NodeVarMap.find (n,v) sigma.
    Definition sigma_set (sigma: sigma_t) (n: node) (v: var) (s: sexp_value) : sigma_t :=
      NodeVarMap.add (n,v) s sigma.

    Definition omega_t : Type := WorldVarMap.t sigma_t.
    Definition omega_0 : omega_t := WorldVarMap.empty sigma_t.
    Definition omega_get (omega: omega_t) (u: worldvar) : option sigma_t :=
      WorldVarMap.find u omega.
    Definition omega_set (omega: omega_t) (u: worldvar) (sig_hyp: sigma_t) : omega_t :=
      WorldVarMap.add u sig_hyp omega.

    Definition pi_t : Type := NodeMap.t unit.
    Definition pi_0 : pi_t := NodeMap.empty unit.
    Definition pi_add (n: node) (pi: pi_t) : pi_t :=
      NodeMap.add n tt pi.
    Definition pi_mem (n: node) (pi: pi_t) : Datatypes.bool :=
      NodeMap.mem n pi.

    Definition rho_t := node.

    Definition mu_t : Type := NodeVarMap.t (sexp_value -> sexp_value -> sexp_value).

    Definition mu_get (mu: mu_t) (n: node) (v: var) :
      option (sexp_value -> sexp_value -> sexp_value) :=
      NodeVarMap.find (n,v) mu.


    Inductive EvalSexp
      : sexp -> sigma_t -> omega_t -> pi_t -> sexp_value -> Prop :=
    | EEmptySexp :
        forall sigma omega pi,
          EvalSexp EmptySexp sigma omega pi (exist _ EmptySexp EmptySexpIsValue)
    | ECons :
        forall (l r: sexp) sigma omega pi (lv rv: sexp_value),
          EvalSexp l sigma omega pi lv ->
          EvalSexp r sigma omega pi rv ->
          EvalSexp EmptySexp sigma omega pi (exist _ EmptySexp EmptySexpIsValue)
    | EVar :
        forall (n: node) (v: var) sigma omega pi (s: sexp_value),
          pi_mem n pi = true ->
          sigma_get sigma n v = Some s ->
          EvalSexp (VarSexp n v) sigma omega pi s
    | EWeight :
        forall (u: worldvar) (n: node) (v: var) (sig_hyp: sigma_t) sigma omega pi (s: sexp_value),
          pi_mem n pi = true ->
          omega_get omega u = Some sig_hyp ->
          sigma_get sig_hyp n v = Some s ->
          EvalSexp (WeightSexp u n v) sigma omega pi s
    .

    Inductive EvalBool
      : bool -> sigma_t -> omega_t -> pi_t -> bool_value -> Prop :=
    | ETrue :
        forall sigma omega pi,
          EvalBool TrueBool sigma omega pi (exist _ TrueBool TrueBoolIsValue)
    | EFalse :
        forall sigma omega pi,
          EvalBool FalseBool sigma omega pi (exist _ FalseBool FalseBoolIsValue)
    | EAndTrue :
        forall (l r: bool) sigma omega pi,
          EvalBool l sigma omega pi (exist _ TrueBool TrueBoolIsValue) ->
          EvalBool r sigma omega pi (exist _ TrueBool TrueBoolIsValue) ->
          EvalBool (ConjBool l r) sigma omega pi (exist _ TrueBool TrueBoolIsValue)
    | EAndFalseL :
        forall (l r: bool) sigma omega pi,
          EvalBool l sigma omega pi (exist _ FalseBool FalseBoolIsValue) ->
          EvalBool (ConjBool l r) sigma omega pi (exist _ FalseBool FalseBoolIsValue)
    | EAndFalseR :
        forall (l r: bool) sigma omega pi,
          EvalBool r sigma omega pi (exist _ FalseBool FalseBoolIsValue) ->
          EvalBool (ConjBool l r) sigma omega pi (exist _ FalseBool FalseBoolIsValue)
    | EOrFalse :
        forall (l r: bool) sigma omega pi,
          EvalBool l sigma omega pi (exist _ FalseBool FalseBoolIsValue) ->
          EvalBool r sigma omega pi (exist _ FalseBool FalseBoolIsValue) ->
          EvalBool (DisjBool l r) sigma omega pi (exist _ FalseBool FalseBoolIsValue)
      | EOrTrueL :
          forall (l r: bool) sigma omega pi,
            EvalBool l sigma omega pi (exist _ TrueBool TrueBoolIsValue) ->
            EvalBool (DisjBool l r) sigma omega pi (exist _ TrueBool TrueBoolIsValue)
      | EOrTrueR :
          forall (l r: bool) sigma omega pi,
            EvalBool r sigma omega pi (exist _ TrueBool TrueBoolIsValue) ->
            EvalBool (DisjBool l r) sigma omega pi (exist _ TrueBool TrueBoolIsValue)
      | EEqTrue :
          forall (l r: sexp) sigma omega pi,
            EvalSexp l sigma omega pi (exist _ EmptySexp EmptySexpIsValue) ->
            EvalSexp r sigma omega pi (exist _ EmptySexp EmptySexpIsValue) ->
            EvalBool (EqBool l r) sigma omega pi (exist _ TrueBool TrueBoolIsValue)
      | EEqFalseL :
          forall (l r ll' lr': sexp) sigma omega pi lp,
            EvalSexp l sigma omega pi (exist _ (ConsSexp ll' lr') lp) ->
            EvalSexp r sigma omega pi (exist _ EmptySexp EmptySexpIsValue) ->
            EvalBool (EqBool l r) sigma omega pi (exist _ FalseBool FalseBoolIsValue)
      | EEqFalseR :
          forall (l r rl' rr': sexp) sigma omega pi rp,
            EvalSexp l sigma omega pi (exist _ EmptySexp EmptySexpIsValue) ->
            EvalSexp r sigma omega pi (exist _ (ConsSexp rl' rr') rp) ->
            EvalBool (EqBool l r) sigma omega pi (exist _ FalseBool FalseBoolIsValue)
      | EEqProp :
          forall (l r ll lr rl rr: sexp) (b: bool) sigma omega pi llp lrp rlp rrp bp,
            EvalSexp l sigma omega pi (exist _ (ConsSexp ll lr) (ConsSexpIsValue llp lrp)) ->
            EvalSexp r sigma omega pi (exist _ (ConsSexp rl rr) (ConsSexpIsValue rlp rrp)) ->
            EvalBool (ConjBool (EqBool ll rl) (EqBool lr rr)) sigma omega pi (exist _ b bp) ->
            EvalBool (EqBool l r) sigma omega pi (exist _ b bp)
      | EMemFalse :
          forall l r sigma omega pi,
            EvalSexp r sigma omega pi (exist _ EmptySexp EmptySexpIsValue) ->
            EvalBool (MemBool l r) sigma omega pi (exist _ FalseBool FalseBoolIsValue)
      | EMemProp :
          forall (l r rl rr: sexp) (b: bool) sigma omega pi rp bp,
            EvalSexp r sigma omega pi (exist _ (ConsSexp rl rr) rp) ->
            EvalBool (DisjBool (EqBool l rl) (MemBool l rr)) sigma omega pi (exist _ b bp) ->
            EvalBool (MemBool l r) sigma omega pi (exist _ b bp)
    .

      Inductive EvalCom
        : com -> sigma_t -> omega_t -> pi_t -> rho_t -> mu_t -> sigma_t -> omega_t -> Prop :=
      | ESkip :
          forall sigma omega pi rho mu,
            EvalCom SkipCom sigma omega pi rho mu sigma omega
      | ESeq :
          forall c1 c2 sigma omega pi rho mu sigma' sigma'' omega' omega'',
            EvalCom c1 sigma omega pi rho mu sigma' omega' ->
            EvalCom c2 sigma' omega' pi rho mu sigma'' omega'' ->
            EvalCom (SeqCom c1 c2) sigma omega pi rho mu sigma'' omega''
      | EIfTrue :
          forall c1 c2 b sigma omega pi rho mu sigma' omega',
            EvalBool b sigma omega pi (exist _ TrueBool TrueBoolIsValue) ->
            EvalCom c1 sigma omega pi rho mu sigma' omega' ->
            EvalCom (IfCom b c1 c2) sigma omega pi rho mu sigma' omega'
      | EIfFalse :
          forall c1 c2 b sigma omega pi rho mu sigma' omega',
            EvalBool b sigma omega pi (exist _ FalseBool FalseBoolIsValue) ->
            EvalCom c2 sigma omega pi rho mu sigma' omega' ->
            EvalCom (IfCom b c1 c2) sigma omega pi rho mu sigma' omega'
      | EAt :
          forall n c sigma omega pi rho mu sigma' omega',
            EvalCom c sigma omega pi n mu sigma' omega' ->
            EvalCom (AtCom n c) sigma omega pi rho mu sigma' omega'
      | EWith :
          forall n c sigma omega pi rho mu sigma' omega',
            EvalCom c sigma omega (pi_add n pi) rho mu sigma' omega' ->
            EvalCom (WithCom n c) sigma omega pi rho mu sigma' omega'
      | EHyp :
          forall u c sigma omega pi rho mu sigma_hyp omega_hyp,
            EvalCom c sigma omega_0 pi rho mu sigma_hyp omega_hyp ->
            EvalCom (WorldAssignCom u c) sigma omega pi rho mu sigma (omega_set omega u sigma_hyp)
      | ECommit :
          forall u sigma omega pi rho mu sigma_hyp sigma_merge,
            omega_get omega u = Some sigma_hyp ->
            (forall n v,
                sigma_get sigma_hyp n v = None ->
                sigma_get sigma_merge n v = sigma_get sigma n v
            ) ->
            (forall n v,
                sigma_get sigma n v = None ->
                sigma_get sigma_merge n v = sigma_get sigma_hyp n v
            ) ->
            (forall n v sc sh f,
                sigma_get sigma n v = Some sc ->
                sigma_get sigma_hyp n v = Some sh ->
                mu_get mu n v = Some f ->
                sigma_get sigma_merge n v = Some (f sc sh)
            ) ->
            EvalCom (CommitCom u) sigma omega pi rho mu sigma_merge omega
    .
  End Evaluation.

  Section WellFormed.
    Definition Omega_t : Type := WorldVarMap.t unit.
    Definition Omega_0 : Omega_t := WorldVarMap.empty unit.
    Definition Omega_in (Omega: Omega_t) (u: worldvar) : Prop :=
      WorldVarMap.MapsTo u tt Omega
    .
    Definition Omega_add (Omega: Omega_t) (u: worldvar) : Omega_t :=
      WorldVarMap.add u tt Omega
    .
    Definition Omega_remove (Omega: Omega_t) (u: worldvar) : Omega_t :=
      WorldVarMap.remove u Omega
    .
    Definition Omega_inter (Omega Omega': Omega_t) : Omega_t :=
      WorldVarMapFacts.restrict Omega Omega'.

    Definition Sigma_t : Type := NodeVarMap.t unit.
    Definition Sigma_0 : Sigma_t := NodeVarMap.empty unit.
    Definition Sigma_in (Sigma: Sigma_t) (n: node) (v: var) : Prop :=
      NodeVarMap.MapsTo (n,v) tt Sigma
    .
    Definition Sigma_add (Sigma: Sigma_t) (n: node) (v: var) : Sigma_t :=
      NodeVarMap.add (n,v) tt Sigma
    .

    Definition Pi_t : Type := NodeMap.t unit.
    Definition Pi_0 : Pi_t := NodeMap.empty unit.
    Definition Pi_in (Pi: Pi_t) (n: node) : Prop :=
      NodeMap.MapsTo n tt Pi
    .
    Definition Pi_add (Pi: Pi_t) (n: node) : Pi_t :=
      NodeMap.add n tt Pi
    .

    Inductive well_formed_sexp : sexp -> Omega_t -> Pi_t -> Sigma_t -> Prop :=
    | TEmptySexp : forall Omega Pi Sigma,
        well_formed_sexp EmptySexp Omega Pi Sigma
    | TVariable : forall n v Omega Pi Sigma,
        Pi_in Pi n ->
        Sigma_in Sigma n v ->
        well_formed_sexp (VarSexp n v) Omega Pi Sigma
    | TWeight : forall u n v Omega Pi Sigma,
        Omega_in Omega u ->
        Sigma_in Sigma n v ->
        Pi_in Pi n ->
        well_formed_sexp (WeightSexp u n v) Omega Pi Sigma
    | TCons : forall l r Omega Pi Sigma,
        well_formed_sexp l Omega Pi Sigma ->
        well_formed_sexp r Omega Pi Sigma ->
        well_formed_sexp (ConsSexp l r) Omega Pi Sigma
    .

    Inductive well_formed_bool : bool -> Omega_t -> Pi_t -> Sigma_t -> Prop :=
    | TTrue : forall Omega Pi Sigma,
        well_formed_bool TrueBool Omega Pi Sigma
    | TFalse : forall Omega Pi Sigma,
        well_formed_bool FalseBool Omega Pi Sigma
    | TConj : forall l r Omega Pi Sigma,
        well_formed_bool l Omega Pi Sigma ->
        well_formed_bool r Omega Pi Sigma ->
        well_formed_bool (ConjBool l r) Omega Pi Sigma
    | TDisj : forall l r Omega Pi Sigma,
        well_formed_bool l Omega Pi Sigma ->
        well_formed_bool r Omega Pi Sigma ->
        well_formed_bool (DisjBool l r) Omega Pi Sigma
    | TEq : forall l r Omega Pi Sigma,
        well_formed_sexp l Omega Pi Sigma ->
        well_formed_sexp r Omega Pi Sigma ->
        well_formed_bool (EqBool l r) Omega Pi Sigma
    | TMem : forall l r Omega Pi Sigma,
        well_formed_sexp l Omega Pi Sigma ->
        well_formed_sexp r Omega Pi Sigma ->
        well_formed_bool (MemBool l r) Omega Pi Sigma
    .

    Inductive well_formed_com : com -> Omega_t -> Pi_t -> Sigma_t -> Omega_t -> Prop :=
    | TSkip : forall Omega Pi Sigma Omega',
        well_formed_com SkipCom Omega Pi Sigma Omega'
    | TSeq : forall l r Omega Pi Sigma Omega' Omega'',
        well_formed_com l Omega Pi Sigma Omega' ->
        well_formed_com r Omega' Pi Sigma Omega'' ->
        well_formed_com (SeqCom l r) Omega Pi Sigma Omega''
    | TIf : forall b l r Omega Pi Sigma Omega' Omega'',
        well_formed_bool b Omega Pi Sigma ->
        well_formed_com l Omega Pi Sigma Omega' ->
        well_formed_com r Omega Pi Sigma Omega'' ->
        well_formed_com (IfCom b l r) Omega Pi Sigma (Omega_inter Omega' Omega'')
    | TAssignWorld : forall u c Omega Pi Sigma Omega',
        well_formed_com c Omega_0 Pi Sigma Omega' ->
        well_formed_com (WorldAssignCom u c) Omega Pi Sigma (Omega_add Omega u)
    | TCommitWorld : forall u Omega Pi Sigma,
        Omega_in Omega u ->
        well_formed_com (CommitCom u) Omega Pi Sigma (Omega_remove Omega u)
    | TWith : forall n c Omega Pi Sigma Omega',
        well_formed_com c Omega (Pi_add Pi n) Sigma Omega' ->
        well_formed_com (WithCom n c) Omega Pi Sigma Omega'
    | TAt : forall n c Omega Pi Sigma Omega',
        well_formed_com c Omega Pi Sigma Omega' ->
        well_formed_com (AtCom n c) Omega Pi Sigma Omega'
    .
  End WellFormed.

End Opal.