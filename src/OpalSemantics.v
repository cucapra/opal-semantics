Require Import CpdtTactics Orders MSetAVL FMapAVL MSets Setoid Morphisms.

Set Implicit Arguments.

Axiom proof_irrelevance :
  forall (P : Prop) (p q : P), p = q.

Definition eq_dec_pair {A: Type} (eq_dec : forall (a1 a2: A), {a1 = a2} + {a1 <> a2})
  : forall (aa1 aa2: A*A), {aa1 = aa2} + {aa1 <> aa2}.
Proof.
  decide equality.
Qed.
Hint Resolve eq_dec_pair.

Module OrderedTypeOld(T: Orders.OrderedType) <: Structures.OrderedType.OrderedType.
  Definition t := T.t.
  Definition eq := T.eq.
  Definition lt := T.lt.

  Theorem eq_refl : forall x : t, eq x x.
  Proof.
    specialize T.eq_equiv. crush.
  Qed.

  Theorem eq_sym : forall x y : t, eq x y -> eq y x.
    Proof.
      specialize T.eq_equiv. crush.
    Qed.

  Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    Proof.
      specialize T.eq_equiv. crush.
    Qed.

    Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    Proof.
      specialize T.lt_strorder.
      intros.
      unfold lt in *.
      destruct H.
      eapply StrictOrder_Transitive. apply H0. apply H1.
    Qed.

    Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    Proof.
      specialize T.eq_equiv.
      specialize T.lt_strorder.
      intros.
      unfold lt in *.
      destruct H, H0.
      unfold not. intros.
      specialize (T.lt_compat H (Equivalence_Reflexive y)).
      crush.
      eapply StrictOrder_Irreflexive. apply H0.
    Qed.

    Print Module Type OrderedType.

    Definition compare : forall x y : t, Structures.OrderedType.Compare lt eq x y.
    Proof.
      intros.
      specialize (T.compare_spec x y).
      destruct (T.compare x y) ; intros.
      * constructor 2.
        inversion H. auto.
      * constructor 1.
        inversion H. auto.
      * constructor 3.
        inversion H. auto.
    Qed.

    Definition eq_dec := T.eq_dec.
End OrderedTypeOld.

Module Opal (NodeType VarType WorldVarType OpType: OrderedType).
  Module NodeVarType := PairOrderedType(NodeType)(VarType).

  Module NodeVarType' := OrderedTypeOld(NodeVarType).
  Module WorldVarType' := OrderedTypeOld(WorldVarType).
  Module OpType' := OrderedTypeOld(OpType).

  Module NodeSet := MSetAVL.Make(NodeType).
  Module NodeVarMap := FMapAVL.Make(NodeVarType').
  Module NodeVarSet := MSetAVL.Make(NodeVarType).
  Module NodeVarProps := MSetProperties.Properties NodeVarSet.
  Module WorldVarMap := FMapAVL.Make(WorldVarType').
  Module WorldVarSet := MSetAVL.Make(WorldVarType).
  Module OpMap := FMapAVL.Make(OpType').
  Module OpSet := MSetAVL.Make(OpType).

  Definition node := NodeType.t.
  Definition var := VarType.t.
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
  | WorldAssignCom : worldvar -> com -> com
  | CommitCom : worldvar -> com
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
  | WeightSexp : worldvar -> node -> var -> sexp
  .

  Inductive bool_value :=
  | TrueBoolValue : bool_value
  | FalseBoolValue : bool_value
  .
  Definition bool_of_bool_value (b: bool_value) : bool :=
    match b with
    | TrueBoolValue => TrueBool
    | FalseBoolValue => FalseBool
    end.

  Inductive sexp_value :=
  | EmptySexpValue : sexp_value
  | ConsSexpValue : sexp_value -> sexp_value -> sexp_value
  .
  Fixpoint sexp_of_sexp_value (s: sexp_value) : sexp :=
    match s with
    | EmptySexpValue => EmptySexp
    | ConsSexpValue s1 s2 =>
      ConsSexp (sexp_of_sexp_value s1)
               (sexp_of_sexp_value s2)
    end.


  Section Evaluation.
    Definition sigma_t := NodeVarMap.t sexp_value.
    Definition sigma_0 : sigma_t := NodeVarMap.empty sexp_value.

    Definition sigma_get (sigma: sigma_t) (n: node) (v: var) : option sexp_value :=
      NodeVarMap.find (n,v) sigma.
    Definition sigma_set (sigma: sigma_t) (n: node) (v: var) (s: sexp_value) : sigma_t :=
      NodeVarMap.add (n,v) s sigma.

    Definition sigmas_t := list sigma_t.
    Fixpoint sigmas_get (sigmas: sigmas_t) (n: node) (v: var) : option sexp_value :=
      match sigmas with
      | nil => None
      | (cons sigma sigmas) =>
        match sigma_get sigma n v with
        | Some s => Some s
        | None => sigmas_get sigmas n v
        end
      end.

    Definition omega_t := WorldVarMap.t (sigma_t * sigma_t).
    Definition omega_0 : omega_t := WorldVarMap.empty (sigma_t * sigma_t).
    Definition omega_get (omega: omega_t) (u: worldvar) : option (sigma_t * sigma_t) :=
      WorldVarMap.find u omega.
    Definition omega_set (omega: omega_t) (u: worldvar) (sig_orig sig_hyp: sigma_t) : omega_t :=
      WorldVarMap.add u (sig_orig, sig_hyp) omega.

    Definition pi_t := NodeSet.t.
    Definition pi_0 : pi_t := NodeSet.empty.
    Definition pi_add (n: node) (pi: pi_t) : pi_t :=
      NodeSet.add n pi.
    Definition pi_mem (n: node) (pi: pi_t) : Datatypes.bool :=
      NodeSet.mem n pi.

    Definition rho_t := node.

    Definition eta_t := OpMap.t (node * var * sexp).
    Definition eta_0 : eta_t := OpMap.empty (node * var * sexp).
    Definition eta_get (eta: eta_t) (op: op) : option (node * var * sexp) :=
      OpMap.find op eta.
    Definition eta_set (eta: eta_t) (op: op) (n: node) (v: var) (sh: sexp) : eta_t :=
      OpMap.add op (n,v,sh) eta.

    Definition mu_t := NodeVarMap.t (var * var * var * sexp).
    Definition mu_0 : mu_t := NodeVarMap.empty (var * var * var * sexp).
    Definition mu_get (mu: mu_t) (n: node) (v: var) : option (var * var * var * sexp) :=
      NodeVarMap.find (n,v) mu.
    Definition mu_set (mu: mu_t) (n: node) (v vo vh vc: var) (sm: sexp) : mu_t:=
      NodeVarMap.add(n,v) (vo,vh,vc,sm) mu.

    Fixpoint eval_eq (l r: sexp_value) :=
      match l, r with
      | EmptySexpValue, EmptySexpValue => TrueBoolValue
      | ConsSexpValue ll lr, ConsSexpValue rl rr =>
        match eval_eq ll rl, eval_eq ll rl with
        | TrueBoolValue, TrueBoolValue => TrueBoolValue
        | _, _ => FalseBoolValue
        end
      | _, _ => FalseBoolValue
      end.

    Fixpoint eval_mem (l r: sexp_value) :=
      match r with
      | EmptySexpValue => FalseBoolValue
      | ConsSexpValue rl rr =>
        match eval_eq l rl, eval_mem l rr with
        | TrueBoolValue, _ => TrueBoolValue
        | _, TrueBoolValue => TrueBoolValue
        | _, _ => FalseBoolValue
        end
      end.

    Fixpoint eval_sexp (s: sexp) (sigmas: sigmas_t) (omega: omega_t) (pi: pi_t) : option sexp_value :=
      match s with
      | EmptySexp => Some EmptySexpValue
      | VarSexp n v =>
        if pi_mem n pi then
          sigmas_get sigmas n v
        else
          None
      | WeightSexp w n v =>
        match omega_get omega w with
        | Some (sigma_orig, sigma_hyp) =>
          sigmas_get (cons sigma_hyp sigmas) n v
        | None =>
          None
        end
      | ConsSexp s1 s2 =>
        match eval_sexp s1 sigmas omega pi,
              eval_sexp s2 sigmas omega pi with
        | Some s1v, Some s2v =>
          Some (ConsSexpValue s1v s2v)
        | _, _ => None
        end
      end.

    Fixpoint eval_bool (b: bool) (sigmas: sigmas_t) (omega: omega_t) (pi: pi_t) : option bool_value :=
      match b with
      | TrueBool => Some TrueBoolValue
      | FalseBool => Some FalseBoolValue
      | ConjBool b1 b2 =>
        match eval_bool b1 sigmas omega pi,
              eval_bool b2 sigmas omega pi
        with
        | Some TrueBoolValue, Some b2' => Some b2'
        | Some FalseBoolValue, Some b2' => Some FalseBoolValue
        | _, _ => None
        end
      | DisjBool b1 b2 =>
        match eval_bool b1 sigmas omega pi,
              eval_bool b2 sigmas omega pi
        with
        | Some FalseBoolValue, Some b2' => Some b2'
        | Some TrueBoolValue, Some b2' => Some TrueBoolValue
        | _, _ => None
        end
      | EqBool s1 s2 =>
        match eval_sexp s1 sigmas omega pi,
              eval_sexp s2 sigmas omega pi
        with
        | Some l, Some r => Some (eval_eq l r)
        | _, _ => None
        end
      | MemBool s1 s2 =>
        match eval_sexp s1 sigmas omega pi,
              eval_sexp s2 sigmas omega pi
        with
        | Some l, Some r => Some (eval_mem l r)
        | _, _ => None
        end
      end.

    Fixpoint eval_com (c: com) (sigmas: sigmas_t) (omega: omega_t) (pi: pi_t) (rho: rho_t) (eta: eta_t) (mu: mu_t) : option (sigma_t * omega_t) :=
      match sigmas with
      | nil => None
      | cons sigma sigmas =>
        match c with
        | SkipCom => Some (sigma, omega)
        | SeqCom c1 c2 =>
          match eval_com c1 (cons sigma sigmas) omega pi rho eta mu with
          | None => None
          | Some (sigma', omega') =>
            eval_com c2 (cons sigma' sigmas) omega' pi rho eta mu
          end
        | IfCom b c1 c2 =>
          match eval_bool b (cons sigma sigmas) omega pi with
          | Some TrueBoolValue =>
            eval_com c1 (cons sigma sigmas) omega pi rho eta mu
          | Some FalseBoolValue =>
            eval_com c2 (cons sigma sigmas) omega pi rho eta mu
          | _ => None
          end
        | WithCom n c =>
          eval_com c (cons sigma sigmas) omega (pi_add n pi) rho eta mu
        | AtCom n c =>
          eval_com c (cons sigma sigmas) omega pi n eta mu
        | HandleCom n v op sh vo vh vc sm c =>
          if pi_mem n pi then
            eval_com c (cons (sigma_set sigma n v EmptySexpValue) sigmas) omega pi n (eta_set eta op n v sh) (mu_set mu n v vo vh vc sm)
          else
            None
        | OpCom op =>
          match eta_get eta op with
          | Some (n, v, sh) =>
            match eval_sexp sh (cons sigma sigmas) omega pi with
            | None => None
            | Some s' =>
              Some (sigma_set sigma n v s', omega)
            end
          | None => None
          end
        | WorldAssignCom u c =>
          match eval_com c (cons sigma_0 (cons sigma sigmas)) omega_0 pi rho eta mu with
          | None => None
          | Some (sigma_hyp, omega_hyp) =>
            Some (sigma, omega_set omega u sigma sigma_hyp)
          end
        | CommitCom w =>
          match omega_get omega w with
          | None => None
          | Some (sigma_orig, sigma_hyp) =>
            let merged_sigma : NodeVarMap.t (option sexp_value) :=
                NodeVarMap.mapi
                  (fun key sh =>
                     match key with
                     | (n, v) =>
                       match mu_get mu n v,
                             sigmas_get (cons sigma sigmas) n v,
                             sigmas_get (cons sigma_orig sigmas) n v
                       with
                       | Some (vo, vh, vc, sm), Some sc, Some so =>
                         let sigma_o := sigma_set sigma n vo so in
                         let sigma_oh := sigma_set sigma_o n vh sh in
                         let sigma_ohc := sigma_set sigma_oh n vc sc in
                         eval_sexp sm (cons sigma_ohc sigmas) omega pi
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
      end.
  End Evaluation.

  Section WellFormed.
    Definition Omega_t := WorldVarSet.t.
    Definition Sigma_t := NodeVarSet.t.
    Definition Pi_t := NodeSet.t.
    Definition H_t := OpSet.t.

    Inductive well_formed_sexp : sexp -> Omega_t -> Sigma_t -> Pi_t -> Prop :=
    | EmptySexpWellFormed : forall Omega Sigma Pi,
        well_formed_sexp EmptySexp Omega Sigma Pi
    | ConsSexpWellFormed : forall l r Omega Sigma Pi,
        well_formed_sexp l Omega Sigma Pi ->
        well_formed_sexp r Omega Sigma Pi ->
        well_formed_sexp (ConsSexp l r) Omega Sigma Pi
    | VarSexpWellFormed : forall n v Omega Sigma Pi,
        NodeVarSet.In (n,v) Sigma ->
        NodeSet.In n Pi ->
        well_formed_sexp (VarSexp n v) Omega Sigma Pi
    | WeightSexpWellFormed : forall u n v Omega Sigma Pi,
        WorldVarSet.In u Omega ->
        NodeVarSet.In (n,v) Sigma ->
        NodeSet.In n Pi ->
        well_formed_sexp (WeightSexp u n v) Omega Sigma Pi
    .

    Inductive well_formed_bool : bool -> Omega_t -> Sigma_t -> Pi_t -> Prop :=
    | TrueBoolWellFormed : forall Omega Sigma Pi,
        well_formed_bool TrueBool Omega Sigma Pi
    | FalseBoolWellFormed : forall Omega Sigma Pi,
        well_formed_bool FalseBool Omega Sigma Pi
    | ConjBoolWellFormed : forall l r Omega Sigma Pi,
        well_formed_bool l Omega Sigma Pi ->
        well_formed_bool r Omega Sigma Pi ->
        well_formed_bool (ConjBool l r) Omega Sigma Pi
    | DisjBoolWellFormed : forall l r Omega Sigma Pi,
        well_formed_bool l Omega Sigma Pi ->
        well_formed_bool r Omega Sigma Pi ->
        well_formed_bool (DisjBool l r) Omega Sigma Pi
    | EqSexpWellFormed : forall l r Omega Sigma Pi,
        well_formed_sexp l Omega Sigma Pi ->
        well_formed_sexp r Omega Sigma Pi ->
        well_formed_bool (EqBool l r) Omega Sigma Pi
    | MemSexpWellFormed : forall l r Omega Sigma Pi,
        well_formed_sexp l Omega Sigma Pi ->
        well_formed_sexp r Omega Sigma Pi ->
        well_formed_bool (MemBool l r) Omega Sigma Pi
    .

    Inductive well_formed_com : com -> Omega_t -> Sigma_t -> Pi_t -> H_t -> Omega_t -> Prop :=
    | SkipComWellFormed : forall Omega Sigma Pi H Omega',
        well_formed_com SkipCom Omega Sigma Pi H Omega'
    | SeqComWellFormed : forall l r Omega Sigma Pi H Omega' Omega'',
        well_formed_com l Omega Sigma Pi H Omega' ->
        well_formed_com r Omega' Sigma Pi H Omega'' ->
        well_formed_com SkipCom Omega Sigma Pi H Omega''
    | IfComWellFormed : forall b l r Omega Sigma Pi H Omega' Omega'',
        well_formed_bool b Omega Sigma Pi ->
        well_formed_com l Omega Sigma Pi H Omega' ->
        well_formed_com r Omega Sigma Pi H Omega'' ->
        well_formed_com (IfCom b l r) Omega Sigma Pi H
                        (WorldVarSet.inter Omega' Omega'')
    | WithComWellFormed : forall n c Omega Sigma Pi H Omega',
        well_formed_com c Omega Sigma (NodeSet.add n Pi) H Omega' ->
        well_formed_com (WithCom n c) Omega Sigma Pi H Omega'
    | AtComWellFormed : forall n c Omega Sigma Pi H Omega',
        well_formed_com c Omega Sigma Pi H Omega' ->
        well_formed_com (AtCom n c) Omega Sigma Pi H Omega'
    | WorldAssignComWellFormed : forall u c Omega Sigma Pi H Omega',
        well_formed_com c WorldVarSet.empty Sigma Pi H Omega' ->
        well_formed_com (WorldAssignCom u c) Omega Sigma Pi H (WorldVarSet.add u Omega)
    | CommitComWellFormed : forall u Omega Sigma Pi H,
        WorldVarSet.In u Omega ->
        well_formed_com (CommitCom u) Omega Sigma Pi H (WorldVarSet.remove u Omega)
    | HandleComWellFormed : forall n v op sh vo vh vc sm c Omega Sigma Pi H Omega',
        NodeSet.In n Pi ->
        NodeVarSet.In (n,v) Sigma ->
        well_formed_sexp sh Omega (NodeVarSet.add (n,v) Sigma) Pi ->
        well_formed_sexp sh Omega (NodeVarSet.add
                                     (n,vc)
                                     (NodeVarSet.add
                                        (n,vh)
                                        (NodeVarSet.add (n,vo) Sigma))) Pi ->
        well_formed_com c Omega (NodeVarSet.add (n,v) Sigma) Pi (OpSet.add op H) Omega' ->
        well_formed_com (HandleCom n v op sh vo vh vc sm c) Omega Sigma Pi H Omega'
    | OpComWellFormed : forall op (Omega: Omega_t) Sigma Pi H Omega,
        OpSet.In op H ->
        well_formed_com (OpCom op) Omega Sigma Pi H Omega
    .
  End WellFormed.

  Definition omega_reps (omega: omega_t) (Omega: Omega_t) :=
    forall k, WorldVarSet.In k Omega -> WorldVarMap.In k omega.

  Definition sigmas_reps (sigmas: sigmas_t) (Sigma: Sigma_t) : Prop :=
    forall n v, NodeVarSet.In (n,v) Sigma ->
                exists val, sigmas_get sigmas n v = Some val.

  Definition eta_reps (eta: eta_t) (H: H_t) : Prop :=
    forall op, OpSet.In op H ->
                exists v, eta_get eta op = Some v.

  Definition mu_reps (mu: mu_t) (Sigma: Sigma_t) : Prop :=
    forall n v, NodeVarSet.In (n,v) Sigma ->
                exists val, mu_get mu n v = Some val.

  Theorem sexp_progress:
    forall s omega sigma Omega Sigma Pi,
      well_formed_sexp s Omega Sigma Pi ->
      omega_reps omega Omega ->
      sigmas_reps sigma Sigma ->
      (exists sv, eval_sexp s sigma omega Pi = Some sv).
  Proof.
    induction s ; intros ; inversion H ; subst.
    * unfold eval_sexp. eauto.
    * specialize (IHs1 omega sigma Omega Sigma Pi).
      specialize (IHs2 omega sigma Omega Sigma Pi).
      intuition.
      inversion H2. inversion H3.
      unfold eval_sexp.
      fold eval_sexp.
      edestruct eval_sexp; edestruct eval_sexp; eauto.
    * assert (pi_mem n Pi = true). specialize (NodeSet.mem_spec Pi n). crush.
      unfold sigmas_reps in H1.
      specialize (H1 n v H4).
      inversion H1.
      exists x.
      unfold eval_sexp.
      rewrite H2.
      apply H3.
    * assert (pi_mem n Pi = true). specialize (NodeSet.mem_spec Pi n). crush.
      crush.
      unfold omega_reps in H0.
      specialize (H0 w).
      intuition.
      unfold omega_get.
      inversion H3.
      specialize (WorldVarMap.find_1 H0).
      edestruct WorldVarMap.find ; intros ; try discriminate.
      destruct p.
      destruct (sigma_get s0 n v) ; eauto.
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