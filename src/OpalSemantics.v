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
    Definition sigma_set (sigma: sigma_t) (n: node) (v: var) (s: sexp) : sigma_t :=
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
    Definition pi_add (n: node) (pi: pi_t) : pi_t :=
      NodeSet.add n pi.
    Definition pi_mem (n: node) (pi: pi_t) : Datatypes.bool :=
      NodeSet.mem n pi.

    Definition rho_t := node.

    Definition eta_t := OpMap.t (node * var * sexp).
    Definition eta_get (eta: eta_t) (op: op) : option (node * var * sexp) :=
      OpMap.find op eta.
    Definition eta_set (eta: eta_t) (op: op) (n: node) (v: var) (sh: sexp) : eta_t :=
      OpMap.add op (n,v,sh) eta.

    Definition mu_t := NodeVarMap.t (var * var * var * sexp).
    Definition mu_get (mu: mu_t) (n: node) (v: var) : option (var * var * var * sexp) :=
      NodeVarMap.find (n,v) mu.
    Definition mu_set (mu: mu_t) (n: node) (v vo vh vc: var) (sm: sexp) : mu_t:=
      NodeVarMap.add(n,v) (vo,vh,vc,sm) mu.

    Program Fixpoint eval_sexp (s: sexp) (Sigma: Sigma_t) (omega: omega_t) (pi: pi_t) (rho: rho_t) (eta: eta_t) (mu: mu_t) {s} : option sexp :=
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
    eval_bool (b: bool) (Sigma: Sigma_t) (omega: omega_t) (pi: pi_t) (rho: rho_t) (eta: eta_t) (mu: mu_t) {b} : option bool :=
      match b with
      | TrueBool => Some TrueBool
      | FalseBool => Some FalseBool
      | ConjBool b1 b2 =>
        match eval_bool b1 Sigma omega pi rho eta mu,
              eval_bool b2 Sigma omega pi rho eta mu
        with
        | Some TrueBool, Some b2' => Some b2'
        | Some FalseBool, Some b2' => Some FalseBool
        | _, _ => None
        end
      | DisjBool b1 b2 =>
        match eval_bool b1 Sigma omega pi rho eta mu,
              eval_bool b2 Sigma omega pi rho eta mu
        with
        | Some FalseBool, Some b2' => Some b2'
        | Some TrueBool, Some b2' => Some TrueBool
        | _, _ => None
        end
      | EqBool s1 s2 =>
        match eval_sexp s1 Sigma omega pi rho eta mu,
              eval_sexp s2 Sigma omega pi rho eta mu
        with
        | Some EmptySexp, Some EmptySexp => Some TrueBool
        | Some (ConsSexp s1l s1r), Some (ConsSexp s2l s2r) =>
          eval_bool (ConjBool (EqBool s1l s2l) (EqBool s1r s2r)) Sigma omega pi rho eta mu
        | Some EmptySexp, Some _ => Some FalseBool
        | Some _, Some EmptySexp => Some FalseBool
        | _, _ => None
        end
      | MemBool s1 s2 =>
        match eval_sexp s1 Sigma omega pi rho eta mu,
              eval_sexp s2 Sigma omega pi rho eta mu
        with
        | Some _, Some EmptySexp => Some FalseBool
        | Some s1', Some (ConsSexp s2l s2r) =>
          eval_bool (DisjBool (EqBool s1' s2l) (MemBool s1' s2r)) Sigma omega pi rho eta mu
        | _, _ => None
        end
      end
    with
    eval_com (c: com) (Sigma: Sigma_t) (omega: omega_t) (pi: pi_t) (rho: rho_t) (eta: eta_t) (mu: mu_t) {c} : option (sigma_t * omega_t) :=
      match Sigma with
      | nil => None
      | cons sigma Simga =>
        match c with
        | SkipCom => Some (sigma, omega)
        | SeqCom c1 c2 =>
          match eval_com c1 (cons sigma Sigma) omega pi rho eta mu with
          | None => None
          | Some (sigma', omega') =>
            eval_com c2 (cons sigma' Sigma) omega' pi rho eta mu
          end
        | IfCom b c1 c2 =>
          match eval_bool b (cons sigma Sigma) omega pi rho eta mu with
          | Some TrueBool =>
            eval_com c1 (cons sigma Sigma) omega pi rho eta mu
          | Some FalseBool =>
            eval_com c2 (cons sigma Sigma) omega pi rho eta mu
          | _ => None
          end
        | WithCom n c =>
          eval_com c (cons sigma Sigma) omega (pi_add n pi) rho eta mu
        | AtCom n c =>
          eval_com c (cons sigma Sigma) omega pi n eta mu
        | HandleCom n v op sh vo vh vc sm c =>
          if pi_mem n pi then
            eval_com c (cons sigma Sigma) omega pi n (eta_set eta op n v sh) (mu_set mu n v vo vh vc sm)
          else
            None
        | OpCom op =>
          match eta_get eta op with
          | Some (n, v, sh) =>
            if pi_mem n pi then
              match eval_sexp sh (cons sigma Sigma) omega pi rho eta mu with
              | None => None
              | Some s' =>
                Some (sigma_set sigma n v s', omega)
              end
            else
              None
          | None => None
          end
        | WorldAssignCom u w =>
          match eval_world w (cons sigma Sigma) omega pi rho eta mu with
          | None => None
          | Some (sigma_orig, sigma_hyp) =>
            Some (sigma, omega_set omega u sigma_orig sigma_hyp)
          end
        | CommitCom w =>
          match eval_world w (cons sigma Sigma) omega pi rho eta mu with
          | None => None
          | Some (sigma_orig, sigma_hyp) =>
            let merged_sigma : NodeVarMap.t (option sexp) :=
                NodeVarMap.mapi
                  (fun key sh =>
                     match key return option sexp with
                     | (n, v) =>
                       match mu_get mu n v,
                             Sigma_get (cons sigma Sigma) n v,
                             Sigma_get (cons sigma_orig Sigma) n v
                       with
                       | Some (vo, vh, vc, sm), Some sc, Some so =>
                         let sigma_o := sigma_set sigma n vo so in
                         let sigma_oh := sigma_set sigma_o n vh sh in
                         let sigma_ohc := sigma_set sigma_oh n vc sc in
                         eval_sexp sm (cons sigma_ohc Sigma) omega pi rho eta mu
                       | _, _, _ => None
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
      end
    with
    eval_world (w: world) (Sigma: Sigma_t) (omega: omega_t) (pi: pi_t) (rho: rho_t) (eta: eta_t) (mu: mu_t) : option (sigma_t * sigma_t) :=
      match Sigma with
      | nil => None
      | cons sigma Sigma =>
        match w with
        | VarWorld u =>
          omega_get omega u
        | HypWorld c =>
          match eval_com c (cons sigma_0 (cons sigma Sigma)) omega_0 pi rho eta mu with
          | None => None
          | Some (sigma_hyp, omega_hyp) =>
            Some (sigma, sigma_hyp)
          end
        end
      end
    .

    Obligation Tactic := admit.
    Solve All Obligations.


End Opal.