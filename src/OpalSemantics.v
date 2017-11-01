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

Definition is_sexp_value (s: sexp) : {sexp_is_value s} + {not (sexp_is_value s)}.
Proof.
  induction s.
  * left. auto.
  * right. crush. inversion H.
  * inversion IHs1 ; inversion IHs2 ; auto ;
      right ; crush ; inversion H1 ;auto.
Defined.

Definition sexp_value := {sexp | sexp_is_value sexp}.

Inductive bool :=
| Eq    : sexp -> sexp -> bool
| Mem   : sexp -> sexp -> bool
| Conj  : bool -> bool -> bool
| Disj  : bool -> bool -> bool
| True  : bool
| False : bool.

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

Record state :=
  mkState {
      sigma : var_store ;
      Sigma : var_store_stack ;
      omega : world_store ;
      pi : principals ;
      rho : location ;
      eta : handlers ;
      mu : mergers
    }.

Definition error := string.

Program Fixpoint sexp_step (s: sexp) (env: var_store_stack) (pi: principals) :
  sexp_value + error :=
  match s with
  | EmptySet => inl EmptySet
  | Cons l r =>
    match sexp_step l env pi, sexp_step r env pi with
    | inl lv, inl rv =>
      inl (Cons lv rv)
    | inr e, _ => inr e
    | _, inr e => inr e
    end
  | Var n v =>
    match set_mem string_dec n pi with
    | true =>
      match lookup env n v with
      | Some val => inl val
      | None => inr (append "No value set for " n)
      end
    | false => inr (append "No permission to read " n)
    end
  end.
Next Obligation.
eapply ConsValuesIsValue; destruct (_: sexp_value); auto.
Defined.

Inductive bool_lt : bool -> bool -> Prop :=
| TrueEq : forall l r, bool_lt True (Eq l r)
| TrueMem : forall l r, bool_lt True (Mem l r)
| TrueConj : forall l r, bool_lt True (Conj l r)
| TrueDisj : forall l r, bool_lt True (Disj l r)
| FalseEq : forall l r, bool_lt False (Eq l r)
| FalseMem : forall l r, bool_lt False (Mem l r)
| FalseConj : forall l r, bool_lt False (Conj l r)
| FalseDisj : forall l r, bool_lt False (Disj l r)
| EqL : forall ll lr rl rr,
    bool_lt (Eq ll rl) (Eq (Cons ll lr) (Cons rl rr))
| EqR : forall ll lr rl rr,
    bool_lt (Eq lr rr) (Eq (Cons ll lr) (Cons rl rr))
| EqVL : forall (l': sexp_value) l r,
    ~ sexp_is_value l ->
    bool_lt (Eq (proj1_sig l') r) (Eq l r)
| EqVR : forall l (r': sexp_value) r,
    ~ sexp_is_value r ->
    bool_lt (Eq l (proj1_sig r')) (Eq l r)
| MemL : forall l rl rr,
    bool_lt (Eq l rl) (Mem l (Cons rl rr))
| MemR : forall (l: sexp_value) rl rr,
    bool_lt (Mem (proj1_sig l) rr) (Mem (proj1_sig l) (Cons rl rr))
| MemVL : forall (l': sexp_value) l r,
    ~ sexp_is_value l ->
    bool_lt (Mem (proj1_sig l') r) (Mem l r)
| MemVR : forall l (r': sexp_value) r,
    ~ sexp_is_value r ->
    bool_lt (Mem l (proj1_sig r')) (Mem l r)
| ConjL : forall l r, bool_lt l (Conj l r)
| ConjR : forall l r, bool_lt r (Conj l r)
| DisjL : forall l r, bool_lt l (Disj l r)
| DisjR : forall l r, bool_lt r (Disj l r).

Theorem acc_true : Acc bool_lt True.
Proof.
  constructor. intros. inversion H.
Qed.

Theorem acc_false : Acc bool_lt False.
Proof.
  constructor. intros. inversion H.
Qed.

Theorem acc_prop :
  forall ll lr rl rr,
    Acc bool_lt (Eq ll rl) ->
    Acc bool_lt (Eq lr rr) ->
    Acc bool_lt (Eq (Cons ll lr) (Cons rl rr)).
Admitted.
(*
Proof.
  Hint Resolve acc_true acc_false.
  intros.
  constructor.
  intros.
  inversion H1; auto.
Qed.
*)

Theorem acc_eq_v : forall l,
    sexp_is_value l ->
    forall r,
    sexp_is_value r ->
    Acc bool_lt (Eq l r).
Admitted.
(*
Proof.
  Hint Resolve acc_true acc_false.
  induction l;
    induction r;
    constructor;
    intros;
    inversion H;
    try (solve [
             inversion H0 ; constructor ; intros ; inversion H4
           | pose acc_prop ; eauto
        ]).
  * inversion H1; auto.
  * inversion H1; auto.
  * inversion H1; auto.
  * inversion H. inversion H0.
    inversion H1; auto.
Qed.
*)

Theorem acc_eq : forall l r, Acc bool_lt (Eq l r).
Admitted.
(*
Proof.
  Hint Resolve acc_true acc_false.
  induction l;
    induction r;
    constructor;
    intros;
    inversion H;
    try (solve [
             inversion H0 ; constructor ; intros ; inversion H4
           | pose acc_prop ; eauto
        ]).
  * constructor ; intros ; inversion H1; auto.
    subst.
    destruct r.
    destruct s; crush.
  * constructor ; intros ; inversion H1; auto.
    subst.
    destruct l.
    destruct s; crush.
  * pose acc_eq_v. intros.
    subst.
    destruct l.
    crush.
    inversion s.
  - crush. constructor. intros.
    inversion H0 ; auto.
    subst.
    constructor.
    intros.
    inversion H ; auto.
    subst.
    inversion H1 ; auto.
    subst.
    destruct r.
    destruct s0; crush.
  - crush. constructor. intros.
    inversion H2; auto. subst.
    constructor. intros.
    inversion H3; auto. subst.
    + constructor. intros.
      inversion H4; auto. subst.
      ** inversion H0.
         destruct r.
         inversion s3; subst. inversion H8.
         inversion H8. inversion H10. subst. inversion H5.
         subst.
         injection H14. intros.
         eapply acc_eq_v; crush.
      ** assert (sexp_is_value lr). inversion s. subst. inversion H11. auto.
         assert (sexp_is_value rr0). destruct r. inversion s0. crush. subst.
         inversion H8. subst. inversion H10. auto.
         eapply acc_eq_v; crush.
      ** eapply acc_eq_v.
      -- destruct l. auto.
      -- destruct r. inversion s0. crush. crush.
      ** eapply acc_eq_v.
      -- inversion s. auto.
      -- destruct r0. inversion s0. crush. crush.
    + eapply acc_eq_v.
      inversion s. auto.
      destruct r. inversion s0. crush. crush.
    + eapply acc_eq_v.
      inversion s. auto.
      destruct r. inversion s0. crush. crush.
  * constructor. intros.
    inversion H1; auto.
  - eapply acc_eq_v.
    destruct l0. inversion s ; crush.
    destruct r. inversion s ; crush.
  - destruct r. destruct s. crush. crush.
 * constructor. intros.
   inversion H1 ; auto.
   - subst.
     inversion IHr1.
     eapply H0.
     destruct l.
     inversion s; crush.
     assert (ll = (proj1_sig (exist sexp_is_value ll H2))). auto.
     rewrite H4.
     eapply EqVL.
   - subst.
     inversion IHr2.
     eapply H0.
     destruct l.
     inversion s; crush.
     assert (lr = (proj1_sig (exist sexp_is_value lr H3))). auto.
     rewrite H4.
     eapply EqVL.
   - destruct l. inversion s; crush.
 * constructor. intros.
   inversion H1 ; auto.
   constructor. intros. inversion H6 ; auto.
   destruct r0. inversion s; crush.
Qed.
*)

Theorem acc_mem_v : forall l,
    sexp_is_value l ->
    forall r,
    sexp_is_value r ->
    Acc bool_lt (Mem l r).
Admitted.
(*
Proof.
  Hint Resolve acc_true acc_false acc_eq.
  induction l;
    induction r;
    constructor;
    intros;
    inversion H;
    try (solve [
             inversion H0 ; constructor ; intros ; inversion H4
           | pose acc_prop ; eauto
        ]).
  * inversion H1; auto.
  * inversion H0.
    inversion H1; auto.
    rewrite H8.
    eapply IHr2. auto.
  * inversion H1; auto.
  * inversion H. inversion H0.
    inversion H1; auto.
    subst.
    rewrite H16.
    eapply IHr2. auto.
Qed.
*)

Theorem acc_mem : forall r l, Acc bool_lt (Mem l r).
Admitted.
(*
Proof.
  induction r;
    constructor;
    intros ;
    inversion H ;
    try solve [ constructor ; intros ; inversion H1
              | inversion H2
              | apply acc_eq
              | crush].
  * eapply acc_mem_v.
    destruct l0. auto. eauto.
  * subst.
    constructor. intros.
    inversion H0; auto.
  - destruct l0. inversion s; crush.
  - eapply acc_mem_v. destruct l0. crush. destruct r. crush.
  * subst.
    constructor.
    intros.
    inversion H0; auto.
    - eapply acc_mem_v.
      +destruct l0. inversion s; crush.
      + destruct r. inversion s; crush.
    - eapply acc_mem_v.
      +destruct l0. inversion s; crush.
      + destruct r. inversion s; crush.
    - destruct r. inversion s; crush.
  * crush.
    constructor. intros.
    inversion H0; auto.
    destruct l0. inversion s; crush.
Qed.
*)

Ltac prove_conj_disj l r y IHl1 IHl2 H2 :=
  induction l ;
    induction r ;
    constructor ;
    intros ;
    inversion H ;
    try (apply acc_eq) ;
    try (apply acc_mem) ;
    try (solve [constructor ; intros ; inversion H1]);
    subst;
    constructor;
    intros ;
    try (specialize IHl1 with y) ;
    try (specialize IHl2 with y) ;
    inversion H0 ;
    try solve [constructor ; intros ; inversion H2];
    try (inversion IHr1 ; eapply H2 ; constructor) ;
    try (inversion IHr2 ; eapply H2 ; constructor) ;
    try (inversion IHl1 ; eapply H2 ; constructor) ;
    try (inversion IHl2 ; eapply H2 ; constructor).

Theorem acc_conj : forall l r, Acc bool_lt (Conj l r).
Proof.
  prove_conj_disj l r y IHl1 IHl2 H2.
Qed.

Theorem acc_disj : forall l r, Acc bool_lt (Disj l r).
Proof.
  prove_conj_disj l r y IHl1 IHl2 H2.
Qed.

Theorem bool_lt_wf : well_founded bool_lt.
Proof.
  Hint Resolve acc_eq acc_mem acc_conj acc_disj.
  unfold well_founded.
  intros.
  constructor.
  intros.

  Ltac kill_acc :=
    try solve [
          apply acc_true
        | apply acc_false
        | apply acc_eq
        | apply acc_mem
        | apply acc_conj
        | apply acc_disj
        ].

  destruct H eqn:? ; kill_acc.
  * induction l ; kill_acc.
  * induction r ; kill_acc.
  * induction l ; kill_acc.
  * induction r ; kill_acc.
Qed.

Require Import Relation_Operators.

Lemma rel_trans : forall A (R: A -> A -> Prop),
    well_founded R -> well_founded (clos_trans A R).
Proof.
Admitted.
(*
  intros.
  unfold well_founded.
  unfold well_founded in H.
  specialize Acc_inv. intros.
  specialize (H0 A R).
  intros.
  induction (H a).
  * constructor.
    intros.
    induction H3.
    - auto.
    - crush.
      constructor.
      intros.
      inversion H3.
      specialize (H1 A R).
      specialize (IHclos_trans1 H).
      destruct H2.

    inversion H1.
    - auto.
    - subst.
Qed.
*)

Definition bool_lt_trans := clos_trans bool bool_lt.
Definition bool_lt_trans_wf := rel_trans bool bool_lt bool_lt_wf.

Definition append2 := append.
Definition append3 (s1 s2 s3: string) : string :=
  (append (append s1 s2) s3).
Definition append4 (s1 s2 s3 s4: string) : string :=
  (append (append s1 s2) (append s3 s4)).

Definition bool_step :
  forall (env: var_store_stack) (pi: principals),
    bool -> (bool_value + error).
  intros env pi.
  refine (Fix bool_lt_trans_wf
              (fun _ => (sum bool_value error))
              (fun (b: bool)
                   (bool_step : forall y : bool, bool_lt_trans y b -> (sum bool_value error)) =>
                 match b as b'
                       return b=b' -> (sum bool_value error) with
                 | True => fun H => inl (exist _ True _)
                 | False => fun H => inl (exist _ False _)
                 | Eq l r =>
                   fun H =>
                     match is_sexp_value l as isvl, is_sexp_value r as isvr
                           return (is_sexp_value l) = isvl -> (is_sexp_value r) = isvr -> (sum bool_value error)
                     with
                     | left _, left _ =>
                       fun _ _ =>
                         match l as l', r as r'
                               return l=l' -> r=r' -> (sum bool_value error) with
                         | Cons ll lr, Cons rl rr =>
                           fun _ _ =>
                             match bool_step (Eq ll rl) _ as leq, bool_step (Eq lr rr) _ as req with
                             | inl (exist _ True _), inl (exist _ True _) =>
                               inl (exist _ True _)
                             | inl _, inl _ => inl (exist _ False _)
                             | inr err, _ => inr err
                             | _, inr err => inr err
                             end
                         | _, _ =>  fun
                             H1 H2 =>
                             inl (exist _ False _)
                         end eq_refl eq_refl
                     | right _, _ =>
                       fun _ _ =>
                         let lstep := sexp_step l env pi in
                         match lstep as lstep'
                               return lstep = lstep' -> (sum bool_value error)
                         with
                         | inl (exist _ lv _) =>
                           fun _ => bool_step (Eq lv r) _
                         | inr err =>
                           fun _ => inr err
                         end eq_refl
                     | _, right _ =>
                       fun _ _ =>
                         match sexp_step r env pi as rstep
                               return (sexp_step r env pi) = rstep -> (sum bool_value error)
                         with
                         | inl (exist _ rv _) =>
                           fun _ =>
                             bool_step (Eq l rv) _
                         | inr err =>
                           fun _ => inr err
                         end eq_refl
                     end eq_refl eq_refl
                 | Mem l r => fun H =>
                   match is_sexp_value l, is_sexp_value r with
                   | left _, left _ =>
                     match l, r with
                     | l, Cons rl rr =>
                       match bool_step (Eq l rl) _ as leq, bool_step (Mem l rr) _ as req with
                       | inl (exist _ False _), inl (exist _ False _) =>
                         inl (exist _ False _)
                       | inl _, inl _ => inl (exist _ True _)
                       | inr err, _ => inr err
                       | _, inr err => inr err
                       end
                     | _, _ => inl (exist _ False _)
                     end
                   | right _, _ =>
                     match sexp_step l env pi with
                     | inl (exist _ lv _) =>
                       bool_step (Mem lv r) _
                     | inr err => inr err
                     end
                   | _, right _ =>
                     match sexp_step r env pi with
                     | inl (exist _ rv _) =>
                       bool_step (Mem l rv) _
                     | inr err => inr err
                     end
                   end
                 | Conj l r => fun H =>
                   match bool_step l _ as lv, bool_step r _ as rv with
                   | (inl (exist _ True _)), (inl (exist _ True _)) =>
                     inl (exist _ True _)
                   | inl _, inl _ => inl (exist _ False _)
                   | inr err, _ => inr err
                   | _, inr err => inr err
                   end
                 | Disj l r => fun H =>
                   match bool_step l _ as lv, bool_step r _ as rv with
                   | (inl (exist _ False _)), (inl (exist _ False _)) =>
                     inl (exist _ False _)
                   | inl _, inl _ => inl (exist _ True _)
                   | inr err, _ => inr err
                   | _, inr err => inr err
                   end
                 end eq_refl));
    try solve [crush].
  * subst. constructor. constructor.
  * subst. constructor. constructor.
  * subst. crush.
    induction r.
  - constructor. contradiction (n EmptySetIsValue).
  - constructor. assert (rv = proj1_sig (exist sexp_is_value rv s1)). auto.
    rewrite H.
    eapply EqVR.
    auto.
  - constructor. assert (rv = proj1_sig (exist sexp_is_value rv s1)). auto.
    auto.
    rewrite H.
    eapply EqVR.
    auto.
  *
    constructor.

    inversion e0.
    eauto.
    inversion n.
    induction (Cons r1 r2
    eapply EqVR.
    destruct l.
    +
      apply t_trans with (Eq EmptySet r1).
      ** constructor.
                rewrite H.
      eapply t_trans.
      ** constructor. constructor.
      ** constructor.
     constructor 2.
    eapply EqVR.
    (
    eapply EqVR./
    destruct r ; crush.
    - crus
    inversion s1; crush.
    - eapply EqVR.

  * crush.
    constructor.
Defined.
     assert (ll = (proj1_sig (exist sexp_is_value ll H2))). auto.
rr))
| EqVL : forall n v (l: sexp_value) r,
    bool_lt (Eq (proj1_sig l) r) (Eq (Var n v) r)
| EqVR : forall n v l (r: sexp_value),
    bool_lt (Eq l (proj1_sig r)) (Eq l (Var n v))
Next Obligation.
Proof.
  apply Prop.
Defined.
Next Obligation.
Proof.
  apply Prop.
Defined.
Next Obligation.
Proof.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
  apply Prop.
Defined.
Next Obligation.
Proof.
  apply Prop.
Qed.
Next Obligation.
  crush.
  inversion wildcard'.
  inversion wildcard'0.
  crush.
  inversion

  destruct b;
    inversion b; crush;
      constructor;
      inversion H; eauto;
        inversion H0 ; eauto.


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