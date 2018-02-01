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

    Fixpoint eval_eq (l r: sexp) {lp: sexp_is_value l} {rp: sexp_is_value r}
      : bool_value.
      unshelve
        refine (
          match l as l', r as r'
                return l=l' -> r=r' -> bool_value
          with
          | EmptySexp, EmptySexp =>
            fun _ _ =>
              exist _ TrueBool _
          | (ConsSexp ll lr), (ConsSexp rl rr) =>
            fun _ _ =>
              let leqv := eval_eq ll rl _ _ in
              let leq := proj1_sig leqv in
              let reqv := eval_eq lr rr _ _ in
              let req := proj1_sig reqv in
              match leq as leq', req as req'
                    return leq=leq' -> req=req' -> bool_value
              with
              | TrueBool, TrueBool =>
                fun _ _ =>
                  exist _ TrueBool _
              | _, _ =>
                fun _ _ =>
                  exist _ FalseBool _
              end eq_refl eq_refl
          | _, _ =>
            fun _ _ =>
              exist _ FalseBool _
          end eq_refl eq_refl) ;
        auto ;
        subst ;
        inversion lp ;
        inversion rp ;
        eauto.
    Defined.

    Arguments eval_eq l r : clear implicits.

    Fixpoint eval_mem
             (l r: sexp) {lp: sexp_is_value l} {rp: sexp_is_value r}
      : bool_value.
      unshelve
        refine (
          match r as r' return r=r' -> bool_value with
          | EmptySexp => fun _ => exist _ FalseBool _
          | ConsSexp rl rr =>
            fun _ =>
              let eqv := eval_eq l rl _ _ in
              let eq := proj1_sig eqv in
              match eq as eq' return eq=eq' -> bool_value with
              | TrueBool =>
                fun _ => exist _ TrueBool _
              | FalseBool =>
                fun _ => eval_mem l rr lp _
              | _ =>
                fun _ => _
              end eq_refl
          | _ => fun _ => exist _ FalseBool _
          end eq_refl
        ) ;
        subst ;
        eauto ;
        inversion rp ;
        eauto.
    Defined.

    Arguments eval_mem l r : clear implicits.

    Fixpoint eval_sexp (s: sexp) (sigma: sigma_t) (omega: omega_t) (pi: pi_t) {struct s} : option sexp_value.
      unshelve
        refine (
          match s with
          | EmptySexp => Some (exist _ EmptySexp _)
          | VarSexp n v =>
            if pi_mem n pi then
              sigma_get sigma n v
            else
              None
          | WeightSexp w n v =>
            match omega_get omega w with
            | Some sigma_hyp =>
              sigma_get sigma_hyp n v
            | None =>
              None
            end
          | ConsSexp s1 s2 =>
            match eval_sexp s1 sigma omega pi,
                  eval_sexp s2 sigma omega pi with
            | Some (exist _ s1v _), Some (exist _ s2v _) =>
              Some (exist _ (ConsSexp s1v s2v) _)
            | _, _ => None
            end
          end)
      .
      constructor.
      constructor ; auto.
    Defined.


    Fixpoint eval_bool (b: bool) (sigma: sigma_t) (omega: omega_t) (pi: pi_t) {struct b} : option bool_value.
      unshelve
        refine (
          match b with
          | TrueBool => Some (exist _ TrueBool _)
          | FalseBool => Some (exist _ FalseBool _)
          | ConjBool b1 b2 =>
            match eval_bool b1 sigma omega pi,
                  eval_bool b2 sigma omega pi
            with
            | Some (exist _ TrueBool _), Some b2' => Some b2'
            | Some (exist _ FalseBool _), Some b2' => Some (exist _ FalseBool _)
            | _, _ => None
            end
          | DisjBool b1 b2 =>
            match eval_bool b1 sigma omega pi,
                  eval_bool b2 sigma omega pi
            with
            | Some (exist _ FalseBool _), Some b2' => Some b2'
            | Some (exist _ TrueBool _), Some b2' => Some (exist _ TrueBool _)
            | _, _ => None
            end
          | EqBool s1 s2 =>
            match eval_sexp s1 sigma omega pi,
                  eval_sexp s2 sigma omega pi
            with
            | Some (exist _ l lp), Some (exist _ r rp) => Some (eval_eq l r lp rp)
            | _, _ => None
            end
          | MemBool s1 s2 =>
            match eval_sexp s1 sigma omega pi,
                  eval_sexp s2 sigma omega pi
            with
            | Some (exist _ l lp), Some (exist _ r rp) => Some (eval_mem l r lp rp)
            | _, _ => None
            end
          end)
      ;
      eauto.
    Defined.

    Fixpoint eval_com (c: com) (sigma: sigma_t) (omega: omega_t) (pi: pi_t) (rho: rho_t) (mu: mu_t) {struct c} : option (sigma_t * omega_t).
      unshelve (
          refine (
              match c with
              | SkipCom => Some (sigma, omega)
              | SeqCom c1 c2 =>
                match eval_com c1 sigma omega pi rho mu with
                | None => None
                | Some (sigma', omega') =>
                  eval_com c2 sigma' omega' pi rho mu
                end
              | IfCom b c1 c2 =>
                match eval_bool b sigma omega pi with
                | Some (exist _ TrueBool _) =>
                  eval_com c1 sigma omega pi rho mu
                | Some (exist _ FalseBool _) =>
                  eval_com c2 sigma omega pi rho mu
                | _ => None
                end
              | WithCom n c =>
                eval_com c sigma omega (pi_add n pi) rho mu
              | AtCom n c =>
                eval_com c sigma omega pi n mu
              | WorldAssignCom u c =>
                match eval_com c sigma omega_0 pi rho mu with
                | None => None
                | Some (sigma_hyp, omega_hyp) =>
                  Some (sigma, omega_set omega u sigma_hyp)
                end
              | CommitCom w =>
                match omega_get omega w with
                | None => None
                | Some sigma_hyp =>
                  let merged_sigma : NodeVarMap.t (option sexp_value) :=
                      NodeVarMap.mapi
                        (fun key sh =>
                           match key with
                           | (n, v) =>
                             match mu_get mu n v,
                                   sigma_get sigma n v
                             with
                             | Some merge_func, Some sc =>
                               Some (merge_func sc sh)
                             | _, _ => None
                             end
                           end)
                        sigma_hyp
                  in
                  match
                    NodeVarMap.fold
                      (fun k vo so =>
                         match vo, so with
                         | Some v, Some s =>
                           Some (NodeVarMap.add k v s)
                         | _, _ => None
                         end) merged_sigma (Some sigma)
                  with
                  | None => None
                  | Some sigma' =>
                    Some (sigma', omega)
                  end
                end
              end
            )
        ).
    Defined.

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

  Definition omega_reps (omega: omega_t) (Omega: Omega_t) : Prop :=
    forall k, Omega_in Omega k -> (exists v, WorldVarMap.MapsTo k v omega).

  Definition sigma_reps (sigma: sigma_t) (Sigma: Sigma_t) : Prop :=
    forall n v, Sigma_in Sigma n v ->
                exists val, sigma_get sigma n v = Some val.

  Theorem sexp_progress:
    forall s omega sigma Omega Pi Sigma,
      well_formed_sexp s Omega Pi Sigma ->
      omega_reps omega Omega ->
      sigma_reps sigma Sigma ->
      (exists sv, eval_sexp s sigma omega Pi = Some sv).
  Proof.
    induction s ; intros ; inversion H ; subst.
    * unfold eval_sexp. eauto.
    * assert (pi_mem n Pi = true).
      unfold Pi_in in H8. unfold pi_mem.
      eapply NodeMap.mem_1.
      unfold NodeMap.In. exists tt. auto.
      unfold sigma_reps in H1.
      specialize (H1 n v H8).
      inversion H1.
      exists x.
      unfold eval_sexp.
      rewrite H2.
      apply H3.
    * assert (pi_mem n Pi = true).
      eapply NodeMap.mem_1.
      unfold NodeMap.In. exists tt. auto.

      unfold eval_sexp.
      unfold omega_reps in H0.
      specialize (H0 w).
      intuition.
      destruct H3.
      specialize (WorldVarMap.find_1 H0).
      intros.
      unfold omega_get.
      rewrite H3.

      unfold sigma_reps in H1.
      specialize (H1 n v).
      intuition.
      destruct H4.
      exists x0.
      eauto.

      unfold omega_reps in H0.
      specialize (H0 w).
      intuition.
      unfold omega_get.
      inversion H3.
      specialize (WorldVarMap.find_1 H0).
      edestruct WorldVarMap.find ; intros ; try discriminate.
      injection H4 ; clear H4.
      intros. subst.
      unfold eval_sexp.
      destruct H3.
      unfold omega_get.
      specialize (WorldVarMap.find_1 H0). intros. rewrite H4.
      destruct (sigma_get x n v) eqn:? ; eauto.
    * specialize (IHs1 omega sigma Omega Sigma Pi).
      specialize (IHs2 omega sigma Omega Sigma Pi).
      intuition.
      inversion H2. inversion H3.
      unfold eval_sexp.
      fold eval_sexp.
      edestruct eval_sexp; edestruct eval_sexp; eauto.
  Qed.

  Theorem bool_progress:
    forall b omega sigma Omega Sigma Pi,
      well_formed_bool b Omega Sigma Pi ->
      omega_reps omega Omega ->
      sigmas_reps sigma Sigma ->
      (exists bv, eval_bool b sigma omega Pi = Some bv).
  Proof.
    induction b ; intros ; inversion H ; subst.
    * unfold eval_bool. eauto.
    * unfold eval_bool. eauto.
    * specialize (IHb1 omega sigma Omega Sigma Pi H4 H0 H1).
      specialize (IHb2 omega sigma Omega Sigma Pi H8 H0 H1).
      crush.
      destruct x0 ; eauto.
    * specialize (IHb1 omega sigma Omega Sigma Pi H4 H0 H1).
      specialize (IHb2 omega sigma Omega Sigma Pi H8 H0 H1).
      crush.
      destruct x0 ; eauto.
    * specialize (sexp_progress) as sp1.
      specialize (sexp_progress) as sp2.
      specialize (sp1 s omega sigma Omega Sigma Pi H4 H0 H1).
      specialize (sp2 s0 omega sigma Omega Sigma Pi H8 H0 H1).
      crush.
      eauto.
    * specialize (sexp_progress) as sp1.
      specialize (sexp_progress) as sp2.
      specialize (sp1 s omega sigma Omega Sigma Pi H4 H0 H1).
      specialize (sp2 s0 omega sigma Omega Sigma Pi H8 H0 H1).
      crush.
      eauto.
  Qed.


  Theorem progress:
    forall c sigmas Sigma omega Omega Pi eta Eta mu rho,
      sigmas <> nil ->
      omega_reps omega Omega ->
      sigmas_reps sigmas Sigma ->
      eta_reps eta Eta ->
      mu_reps mu Sigma ->
      (exists Omega', well_formed_com c Omega Sigma Pi Eta Omega') ->
      exists sigma' omega',
        eval_com c sigmas omega Pi rho eta mu = Some (sigma', omega').
  Proof.
    induction c ; intros ; unfold eval_com ; fold eval_com.
    * intros. destruct sigmas. contradiction H. reflexivity.
      exists s. exists omega. auto.
    * inversion H4.
      inversion H5.
    * inversion H4. inversion H5.
      subst. intuition.

      specialize (bool_progress).
      intros.

      destruct sigmas. contradiction H. reflexivity.
      specialize (H6 b omega (s::sigmas) Omega Sigma Pi H10 H0 H1).
      destruct (eval_bool b (s :: sigmas) omega Pi).
      specialize (IHc1 (s::sigmas) Sigma omega Omega Pi eta Eta mu rho).
      specialize (IHc2 (s::sigmas) Sigma omega Omega Pi eta Eta mu rho).
      destruct b0.
      - intuition.
        eapply H9.
        exists Omega'.
        auto.
      - intuition.
        eapply H7.
        exists Omega''.
        auto.
      - inversion H6. inversion H7.
   * destruct sigmas. contradiction H. reflexivity.
     specialize (IHc (s::sigmas) Sigma omega Omega (pi_add n Pi) eta Eta mu rho).
     intuition.
     assert (exists Omega' : Omega_t,
                well_formed_com c Omega Sigma (pi_add n Pi) Eta Omega').
      - inversion H4. inversion H6. subst. exists x. apply H15.
      - crush.
   * destruct sigmas. contradiction H. reflexivity.
     specialize (IHc (s::sigmas) Sigma omega Omega Pi eta Eta mu n).
     intuition.
     assert (exists Omega' : Omega_t, well_formed_com c Omega Sigma Pi Eta Omega').
      - destruct H4. exists x. inversion H4. auto.
      - intuition.
   * destruct sigmas. contradiction H. reflexivity.
     inversion H4.
     inversion H5.
     assert (pi_mem n Pi = true). specialize (NodeSet.mem_spec Pi n). crush.
     subst.
     rewrite H26.
     remember (sigma_set s1 n v EmptySexpValue) as s2.
     pose (OpSet.add o Eta).
     pose (NodeVarSet.add (n,v) Sigma).
     specialize (IHc (s2::sigmas) (NodeVarSet.add (n, v) Sigma) omega Omega Pi (eta_set eta o n v s) t (mu_set mu n v v0 v1 v2 s0) n).
     intuition.

     assert (s2 :: sigmas = nil -> False).
     intros. discriminate.

     assert (sigmas_reps (s2 :: sigmas) (NodeVarSet.add (n, v) Sigma)).
     unfold sigmas_reps in *.
     unfold sigmas_get in *.
     unfold sigma_set in *.
     intros.
     destruct (NodeVarType.eq_dec (n,v) (n0,v3)).
      - specialize (NodeVarMap.add_1 s1 EmptySexpValue e).
        intros.
        exists (EmptySexpValue).
        specialize (NodeVarMap.find_1 H8).
        intros.
        rewrite <- Heqs2 in H9.
        assert (sigma_get s2 n0 v3 = Some EmptySexpValue).
        + crush.
        + rewrite H10. auto.
      - fold sigmas_get in *.
        specialize (H1 n0 v3).
        specialize (NodeVarSet.add_spec Sigma (n,v) (n0,v3)).
        intros.
        destruct H8.
        intuition.
        destruct (sigma_get s2 n0 v3) eqn:?.
        + exists s3. auto.
        + inversion H10.
          destruct (sigma_get s1 n0 v3) eqn:?.
          ** subst.
             unfold sigma_get in *.
             specialize (NodeVarMap.find_2 Heqo1).
             intros.
             specialize (NodeVarMap.add_2 EmptySexpValue n1 H13).
             intros.
             specialize (NodeVarMap.find_1 H14).
             intros.
             assert (sigma_get (NodeVarMap.add (n, v) EmptySexpValue s1) n0 v3 = Some s3). unfold sigma_get. auto.
             assert (sigma_get (NodeVarMap.add (n, v) EmptySexpValue s1) n0 v3 = None). unfold sigma_get. auto.
             rewrite H16 in H17. discriminate.
          ** auto.
-
     assert (eta_reps (eta_set eta o n v s) t).
     unfold eta_reps in *.
     intros.
     unfold eta_get in *.
     unfold eta_set in *.
     destruct (OpType.eq_dec o op0).
     specialize (OpMap.add_1 eta (n,v,s) e).
     exists (n,v,s).
     specialize (OpMap.find_1 H9).
     intros.
     auto.
     subst.
     specialize H2 with op0.
     assert (OpSet.In op0 Eta).
     specialize (OpSet.add_spec Eta o op0).
     intuition.
     intuition.
     inversion H11.
     exists x0.
     specialize (OpMap.find_2 H2).
     intros.
     specialize (OpMap.add_2 (n,v,s) n0 H12).
     intros.
     specialize (OpMap.find_1 H13).
     auto.

     assert (mu_reps (mu_set mu n v v0 v1 v2 s0) (NodeVarSet.add (n, v) Sigma)).
     unfold mu_reps in *.
     unfold mu_get in *.
     unfold mu_set in *.
     intros.
     destruct (NodeVarType.eq_dec (n,v) (n0,v3)) eqn:?.
     + specialize (NodeVarMap.add_1 mu (v0, v1, v2, s0) e).
       intros.
       specialize (NodeVarMap.find_1 H10).
       intros.
       exists (v0,v1,v2,s0). auto.
     + specialize (H3 n0 v3).
       assert (NodeVarSet.In (n0, v3) Sigma).
       specialize (NodeVarSet.add_spec Sigma (n,v) (n0,v3)).
       intros.
       destruct H10. intuition.
       intuition.
       inversion H11.
       specialize (NodeVarMap.find_2 H3).
       intros.
       specialize (NodeVarMap.add_2 (v0, v1, v2, s0) n1 H13).
       intros.
       exists x0.
       specialize (NodeVarMap.find_1 H14).
       intros.
       auto.
     + assert (exists Omega', well_formed_com c Omega (NodeVarSet.add (n, v) Sigma) Pi t Omega').
     exists x. auto.

     intuition.
   * destruct sigmas. contradiction H. reflexivity.
     inversion H4.
     inversion H5.
     subst.
     unfold eta_reps in *.
     unfold eta_get in *.
     specialize (H2 o H8).
     inversion H2.
     rewrite H6.
     destruct x0, p.
     pose

    subst. intuition.
    specialize (IHc n Pi).
    eapply IHc.
    eauto.
  * inversion H. inversion H0.
    subst. intuition.
    specialize (IHc n Pi).
    assert (pi_mem n Pi = true). inversion H16.
    crush.
      - inversion H16; subst.
        +

    specialize (NodeSet.mem_spec Pi n). crush.
    assert
    inversion H16.
    crush.
    eapply IHc.
  Qed.
End Opal.